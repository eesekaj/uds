
use std::
{
    cmp::min, ffi::{c_int, c_void}, io::{self, ErrorKind}, mem::{self, MaybeUninit}, 
    os::windows::io::{AsRawSocket, AsSocket, BorrowedSocket, FromRawSocket, IntoRawSocket, OwnedSocket, RawSocket}, 
    path::Path, ptr, sync::{LazyLock, OnceLock}
};

use windows_sys::
{
    Win32::Networking::WinSock::
    {
        AF_UNIX, FIONBIO, INVALID_SOCKET, MSG_TRUNC, SO_ERROR, SO_TYPE, SOCK_STREAM, 
        SOCKADDR as sockaddr, SOCKET_ERROR, SOL_SOCKET, WSADATA, WSAEMSGSIZE, WSAESHUTDOWN, 
        WSARecv, WSASend, WSAStartup, accept, bind, connect, getpeername, getsockname, 
        getsockopt, ioctlsocket, listen, recv, send, socket, socklen_t
    }, 
    core::PCSTR
};

use crate::{LISTEN_BACKLOG, UnixSocketAddr};


fn create_socket() -> io::Result<OwnedSocket>
{
     let socket_res = 
           unsafe { socket(AF_UNIX as i32, SOCK_STREAM, 0) };

    if socket_res != INVALID_SOCKET
    {
        return Ok(
            unsafe{ OwnedSocket::from_raw_socket(socket_res as u64) }
        );
    }
    else
    {
        return Err(io::Error::last_os_error());
    }
}

fn connect_socket<S: AsRawSocket>(so: &S, addr: &UnixSocketAddr) -> io::Result<()>
{
    let sa =  unsafe{ addr.as_raw_ptr_general() };

    let res = unsafe { connect(so.as_raw_socket() as usize, sa.0, sa.1) };

    if res != SOCKET_ERROR
    {
        return Ok(());
    }
    else
    {
        return Err(io::Error::last_os_error());
    }
}

fn bind_socket<S: AsRawSocket>(so: &S, addr: &UnixSocketAddr) -> io::Result<()>
{
    let sa =  unsafe{ addr.as_raw_ptr_general() };

    let res = unsafe{ bind(so.as_raw_socket() as usize, sa.0, sa.1) };

    if res != SOCKET_ERROR
    {
        return Ok(());
    }
    else
    {
        return Err(io::Error::last_os_error());
    }
}

fn listen_socket<S: AsRawSocket>(so: &S, backlog: i32) -> io::Result<()>
{
    let res = unsafe{ listen(so.as_raw_socket() as usize, backlog) };

    if res != SOCKET_ERROR
    {
        return Ok(());
    }
    else
    {
        return Err(io::Error::last_os_error());
    }
}

/// Safe wrapper around `getsockname()` or `getpeername()`. 
fn get_unix_local_addr<FD>(socket: &FD) -> Result<UnixSocketAddr, io::Error> 
where FD: AsRawSocket
{
    unsafe 
    {
        UnixSocketAddr::new_from_ffi(
            |addr_ptr, addr_len| 
            {
                if getsockname(socket.as_raw_socket() as usize, addr_ptr, addr_len) != SOCKET_ERROR
                {
                    Ok(())
                }
                else
                {
                    Err(io::Error::last_os_error())
                }
            }
        )
        .map(|((), addr)| addr )
    }
}


fn get_unix_peer_addr<FD>(socket: &FD) -> Result<UnixSocketAddr, io::Error> 
where FD: AsRawSocket
{
    unsafe 
    {
        UnixSocketAddr::new_from_ffi(
            |addr_ptr, addr_len| 
            {
                if getpeername(socket.as_raw_socket() as usize, addr_ptr, addr_len)  != SOCKET_ERROR
                {
                    Ok(())
                }
                else
                {
                    Err(io::Error::last_os_error())
                }
            }
        )
        .map(|((), addr)| addr )
    }
}

pub 
fn get_socket_family<S: AsRawSocket>(fd: &S) -> io::Result<u16>
{
    let mut optval: MaybeUninit<sockaddr> = MaybeUninit::zeroed();
    let mut len = size_of::<sockaddr>() as socklen_t;
    

    let res = 
        unsafe
        {
            getsockname(fd.as_raw_socket() as usize,optval.as_mut_ptr().cast(), &mut len)
        };

    // more likely it will not fail
    if res == 0
    {
        return Ok(unsafe { optval.assume_init() }.sa_family);
    }
    else
    {
        return Err(io::Error::last_os_error());
    }
}

pub 
fn get_socket_type<S: AsRawSocket>(fd: &S) -> io::Result<c_int>
{
    let mut optval: MaybeUninit<c_int> = MaybeUninit::zeroed();
    let mut len = size_of::<c_int>() as socklen_t;

    let res = 
        unsafe
        {
            getsockopt(fd.as_raw_socket() as usize, SOL_SOCKET, SO_TYPE,
                optval.as_mut_ptr().cast(),&mut len,
            )
        };

    // more likely it will not fail
    if res == 0
    {
        if len as usize != size_of::<c_int>()
        {
            return Err(
                std::io::Error::new(
                    ErrorKind::Other, 
                    format!("assertion trap: returned data len mispatch {} != {}",
                            len, size_of::<c_int>())
                )
            );
        }

        return Ok(unsafe { optval.assume_init() });
    }
    else
    {
        return Err(io::Error::last_os_error());
    }
}

/// Safe wrapper around `getsockopt(SO_ERROR)`.
fn take_error<FD>(socket: &FD) -> Result<Option<io::Error>, io::Error> 
where FD: AsRawSocket
{
    let mut stored_errno: c_int = 0;
    let mut optlen = mem::size_of::<c_int>() as socklen_t;
    let dst_ptr = &mut stored_errno as *mut c_int as *mut u8;
    
    unsafe 
    {
        if getsockopt(socket.as_raw_socket() as usize, SOL_SOCKET, SO_ERROR, dst_ptr, &mut optlen) == -1 
        {
            Err(io::Error::last_os_error())
        } 
        else if optlen != mem::size_of::<c_int>() as socklen_t 
        {
            // std panics here
            Err(
                io::Error::new(
                    ErrorKind::InvalidData,
                    "got unexpected length from getsockopt(SO_ERROR)"
                )
            )
        } 
        else if stored_errno == 0 
        {
            Ok(None)
        } 
        else 
        {
            Ok(Some(io::Error::last_os_error()))
        }
    }
}

fn set_nonblocking<FD: AsRawSocket>(so: &FD,  nonblocking: bool) -> Result<(), io::Error> 
{
    let mut nonblocking = if nonblocking { 1 } else { 0 };

    let res = unsafe{ ioctlsocket(so.as_raw_socket() as usize, FIONBIO, &mut nonblocking) };

    if res == SOCKET_ERROR
    {
        return Err(io::Error::last_os_error());
    }

    return Ok(());
}
 
fn accept_from<FD>(fd: &FD, nonblocking: bool) -> Result<(WindowsUnixStream, UnixSocketAddr), io::Error> 
where FD: AsRawSocket
{
    unsafe 
    { 
        UnixSocketAddr::new_from_ffi(
            |addr_ptr, len_ptr| 
            {
                let socket = 
                    accept(fd.as_raw_socket() as usize, addr_ptr, len_ptr);

                if socket == INVALID_SOCKET
                {
                    return Err(io::Error::last_os_error());
                }

                let o_sock = WindowsUnixStream::from_raw_socket(socket as u64);

                if nonblocking  == true
                {
                    set_nonblocking(&o_sock, true)?;
                }

                return Ok(o_sock);
            }
        ) 
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecvFlags(pub u32);

impl RecvFlags
{
    pub const MSG_TRUNC: u32 = MSG_TRUNC;
}

fn recv_vectored<S: AsRawSocket>(socket: &S, bufs: &mut [io::IoSliceMut<'_>], flags: c_int) -> io::Result<(usize, RecvFlags)> 
{
    let mut nread = 0;
    let mut flags = flags as u32;
    let res = 
         unsafe
         {
            WSARecv(
                socket.as_raw_socket() as usize,
                bufs.as_mut_ptr().cast(),
                min(bufs.len(), u32::MAX as usize) as u32,
                &mut nread,
                &mut flags,
                ptr::null_mut(),
                None,
            )
        };

    if res == SOCKET_ERROR
    {
        let e = io::Error::last_os_error();

        if e.raw_os_error() == Some(WSAESHUTDOWN as i32)
        {
            return Ok( (0, RecvFlags(0)) );
        }
        else if e.raw_os_error() ==  Some(WSAEMSGSIZE as i32)
        {
            return Ok( (nread as usize, RecvFlags(RecvFlags::MSG_TRUNC)) );
        }
        else
        {
            return Err(e);
        }
    }

    return Ok( (nread as usize, RecvFlags(0)) );
}

fn send_vectored<S: AsRawSocket>(socket: &S, bufs: &[io::IoSlice<'_>], flags: c_int) -> io::Result<usize> 
{
    let mut nsent = 0;

    let res = 
        unsafe
        {
            WSASend(
                socket.as_raw_socket() as usize,
                bufs.as_ptr() as *mut _,
                min(bufs.len(), u32::MAX as usize) as u32,
                &mut nsent,
                flags as u32,
                std::ptr::null_mut(),
                None,
            )
        };

    if res == SOCKET_ERROR
    {
        return Err(io::Error::last_os_error());
    }

    return Ok( nsent as usize);
}

static WSA_STARTUP: LazyLock<()> = 
    LazyLock::new(
        ||
        {
            let mut wsadata = MaybeUninit::<WSADATA>::zeroed();
            
            let res = unsafe{ WSAStartup(0x0202, wsadata.as_mut_ptr()) };

            if res != 0
            {
                panic!("WSAStartup error: {}", io::Error::last_os_error());
            }
        }
    );

/// An unix domain `stream` packet connection for Windows.
/// 
/// It requires WSA version 2.0 or 2.2 i.e Windows 10 and above.
/// 
/// The crate requests version 2.2 by default!
///
/// Is simular to the `UnixStream` but with some limitations:
/// 
/// * no `SOCK_DGRAM` or `SOCK_SEQPACKET` support
/// 
/// * Ancillary data like `SCM_RIGHTS` `SCM_CREDENTIALS`
/// 
/// * Autobind feature
/// 
/// * socketpair
///
/// # Examples
///
/// ```ignore
/// let path = "server3.sock";
/// 
/// let client = WindowsUnixStream::connect(path).unwrap();
/// client.send(b"first").unwrap();
/// client.send(b"second").unwrap();
/// ```
#[derive(Debug)]
#[repr(transparent)]
pub struct WindowsUnixStream
{
    sock: OwnedSocket,
}

impl FromRawSocket for WindowsUnixStream
{
    unsafe 
    fn from_raw_socket(sock: RawSocket) -> Self 
    {
        let os = unsafe{ OwnedSocket::from_raw_socket(sock) };

        return WindowsUnixStream::from(os);
    }
}

impl From<OwnedSocket> for WindowsUnixStream
{
    fn from(os: OwnedSocket) -> Self 
    {
        let sa_fam = get_socket_family(&os).unwrap();
        let sa_type = get_socket_type(&os).unwrap();

        if sa_fam != AF_UNIX || sa_type != SOCK_STREAM
        {
            panic!("assertion trap: provided FD is not AF_UNIX & SOCK_STREAM, {} {}", 
                sa_fam, sa_type);
        }

        let _ = &*WSA_STARTUP;

        return Self{ sock: os };
    }
}

impl From<WindowsUnixStream> for OwnedSocket
{
    fn from(value: WindowsUnixStream) -> Self 
    {
        return value.sock;
    }
}

impl AsSocket for WindowsUnixStream
{
    fn as_socket(&self) -> BorrowedSocket<'_> 
    {
        return self.sock.as_socket();
    }
}

impl AsRawSocket for WindowsUnixStream
{
    fn as_raw_socket(&self) -> RawSocket 
    {
        return self.sock.as_raw_socket();
    }
}

impl IntoRawSocket for WindowsUnixStream
{
    fn into_raw_socket(self) -> RawSocket 
    {
        return self.sock.into_raw_socket();
    }
}

impl io::Write for WindowsUnixStream
{
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> 
    {
        self.send(buf)
    }

    /// Do not access `bufs` after sending!
    fn write_vectored(&mut self, bufs: &[io::IoSlice<'_>]) -> io::Result<usize> 
    {
        send_vectored(self, &bufs, 0)
    }
    
    fn flush(&mut self) -> io::Result<()>
    {
        todo!()
    }
}

impl io::Read for WindowsUnixStream
{
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> 
    {
        self.recv(buf)
    }

    fn read_vectored(&mut self, bufs: &mut [io::IoSliceMut<'_>]) -> io::Result<usize> 
    {
        self.recv_vectored(bufs).map(|(n, _)| n)
    }
}

impl WindowsUnixStream
{
    /// Connects to an unix stream server listening at `path`.
    ///
    /// This is a wrapper around [`connect_unix_addr()`](#method.connect_unix_addr)
    /// for convenience and compatibility with std.
    pub 
    fn connect<P: AsRef<Path>>(path: P) -> Result<Self, io::Error> 
    {
        let addr = UnixSocketAddr::from_path(&path)?;

        return Self::connect_unix_addr(&addr);
    }

    /// Connects to an unix seqpacket server listening at `addr`.
    pub 
    fn connect_unix_addr(addr: &UnixSocketAddr) -> Result<Self, io::Error> 
    {
        let _ = &*WSA_STARTUP;

        let socket = create_socket()?;

        connect_socket(&socket, addr)?;

        return Ok( Self{ sock: socket } );
    }

    /// Binds to an address before connecting to a listening seqpacet socket.
    pub 
    fn connect_from_to_unix_addr(from: &UnixSocketAddr,  to: &UnixSocketAddr) -> Result<Self, io::Error> 
    {
        let _ = &*WSA_STARTUP;

        let socket = create_socket()?;

        bind_socket(&socket, from)?;

        connect_socket(&socket, to)?;

        return Ok( Self{ sock: socket } );
    }

    pub 
    fn set_nonblocking(&self, nonblk: bool) -> io::Result<()>
    {
        set_nonblocking(self, nonblk)
    }

    /// Returns the address of this side of the connection.
    pub 
    fn local_unix_addr(&self) -> Result<UnixSocketAddr, io::Error> 
    {
        get_unix_local_addr(self)
    }

    /// Returns the address of the other side of the connection.
    pub 
    fn peer_unix_addr(&self) -> Result<UnixSocketAddr, io::Error> 
    {
        get_unix_peer_addr(self)
    }

    /// Sends a packet to the peer.
    pub 
    fn send(&self, packet: &[u8]) -> Result<usize, io::Error> 
    {
        let ptr = packet.as_ptr();
        let pkt_len = min(packet.len(), i32::MAX as usize) as i32;
        let flags = 0;

        let sent = unsafe { send(self.sock.as_raw_socket() as usize, ptr, pkt_len, flags) };
        
        if sent != SOCKET_ERROR
        {
            return Ok(sent as usize);
        }
        
        return Err(std::io::Error::last_os_error());
    }

    /// Receives a packet from the peer.
    pub 
    fn recv(&self, buffer: &mut[u8]) -> Result<usize, io::Error> 
    {
        let ptr = buffer.as_mut_ptr();
        let pkt_len = min(buffer.len(), i32::MAX as usize) as i32;
        let received = unsafe { recv(self.sock.as_raw_socket() as usize, ptr, pkt_len, 0) };
        
        if received >= 0
        {
            return Ok(received as usize);
        }

        return Err(std::io::Error::last_os_error());
    }

    pub 
    fn recv_vectored(&self, bufs: &mut [io::IoSliceMut<'_>]) -> io::Result<(usize, RecvFlags)> 
    {
        recv_vectored(self, bufs, 0)
    }

    /// Windows consumes the [io::IoSlice] instances, so can no logner be accessed.
    /// The [io::Write] borrows, but it is not correct. DO not access the slices after
    /// it were sent.
    pub 
    fn send_vectored(&self, bufs: Vec<io::IoSlice<'_>>) -> io::Result<usize>
    {
        send_vectored(self, &bufs, 0)
    }

    /// Returns the value of the `SO_ERROR` option.
    ///
    /// This might only provide errors generated from nonblocking `connect()`s,
    /// which this library doesn't support. It is therefore unlikely to be 
    /// useful, but is provided for parity with stream counterpart in std.
    pub 
    fn take_error(&self) -> Result<Option<io::Error>, io::Error> 
    {
        take_error(self)
    }
}

/// An unix domain listener for [SOCK_STREAM] packet connections which requires
/// WSA version 2.2 i.e Windows 10 minimum.
///
/// See [`WindowsUnixStream`](struct.WindowsUnixStream.html) for a description
/// of this type of connection.
///
/// # Examples
///
/// ```no_run
/// let file_path = "server_test.sock";
/// let _ = std::fs::remove_file(file_path);
/// let listener = uds_fork::WindowsUnixListener::bind(file_path)
///     .expect("Create seqpacket listener");
/// let client = uds_fork::WindowsUnixStream::connect(file_path).unwrap();
/// let (conn, _addr) = listener.accept_unix_addr().unwrap();
/// conn.send(b"Welcome").unwrap();
/// std::thread::sleep(std::time::Duration::from_secs(1));
/// drop(client);
/// std::fs::remove_file(file_path).unwrap();
/// ```
#[derive(Debug)]
#[repr(transparent)]
pub struct WindowsUnixListener
{
    sock: OwnedSocket,
}

impl FromRawSocket for WindowsUnixListener
{
    unsafe 
    fn from_raw_socket(sock: RawSocket) -> Self 
    {
        let os = unsafe{ OwnedSocket::from_raw_socket(sock) };

        return WindowsUnixListener::from(os);
    }
}

impl From<OwnedSocket> for WindowsUnixListener
{
    fn from(os: OwnedSocket) -> Self 
    {
        let sa_fam = get_socket_family(&os).unwrap();
        let sa_type = get_socket_type(&os).unwrap();

        if sa_fam != AF_UNIX || sa_type != SOCK_STREAM
        {
            panic!("assertion trap: provided FD is not AF_UNIX & SOCK_SEQPACKET, {} {}", 
                sa_fam, sa_type);
        }

        let _ = &*WSA_STARTUP;

        return Self{ sock: os };
    }
}

impl From<WindowsUnixListener> for OwnedSocket
{
    fn from(value: WindowsUnixListener) -> Self 
    {
        return value.sock;
    }
}

impl AsSocket for WindowsUnixListener
{
    fn as_socket(&self) -> BorrowedSocket<'_> 
    {
        return self.sock.as_socket();
    }
}

impl AsRawSocket for WindowsUnixListener
{
    fn as_raw_socket(&self) -> RawSocket 
    {
        return self.sock.as_raw_socket();
    }
}

impl IntoRawSocket for WindowsUnixListener
{
    fn into_raw_socket(self) -> RawSocket 
    {
        return self.sock.into_raw_socket();
    }
}

impl WindowsUnixListener
{
     /// Creates a socket that listens for seqpacket connections on the specified socket file.
    pub 
    fn bind<P: AsRef<Path>>(path: P) -> Result<Self, io::Error> 
    {
        let addr = UnixSocketAddr::from_path(path.as_ref())?;
        
        return Self::bind_unix_addr(&addr);
    }

    /// Creates a socket that listens for seqpacket connections on the specified address.
    pub 
    fn bind_unix_addr(addr: &UnixSocketAddr) -> Result<Self, io::Error> 
    {
        let _ = &*WSA_STARTUP;

        let socket = create_socket()?;

        bind_socket(&socket, addr)?;

        listen_socket(&socket, LISTEN_BACKLOG)?;
        
        return Ok(Self{ sock: socket });
    }

    pub 
    fn set_nonblocking(&self, nonblk: bool) -> io::Result<()>
    {
        set_nonblocking(self, nonblk)
    }

    /// Returns the address the socket is listening on.
    pub 
    fn local_unix_addr(&self) -> Result<UnixSocketAddr, io::Error> 
    {
        get_unix_local_addr(self)
    }

    pub 
    fn listen(&self, backlog: i32) -> io::Result<()>
    {
        listen_socket(self, backlog)
    }

    /// Accepts a new incoming connection to this listener.
    pub 
    fn accept_unix_addr(&self)-> Result<(WindowsUnixStream, UnixSocketAddr), io::Error> 
    {
        let (socket, addr) = accept_from(self, false)?;
        
        return Ok((socket, addr));
    }

    /// Returns the value of the `SO_ERROR` option.
    ///
    /// This might never produce any errors for listeners. It is therefore
    /// unlikely to be useful, but is provided for parity with
    /// `std::unix::net::UnixListener`.
    pub 
    fn take_error(&self) -> Result<Option<io::Error>, io::Error> 
    {
        take_error(self)
    }
}