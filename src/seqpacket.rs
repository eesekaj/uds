#[cfg(any(
    target_vendor="apple", target_os="freebsd",
    target_os="netbsd",
    target_os="illumos", target_os="solaris",
))]
use std::io::ErrorKind;
use std::
{
    io::{self, IoSlice, IoSliceMut}, net::Shutdown, ops::{Deref, DerefMut}, os::unix::io::{AsFd, AsRawFd, BorrowedFd, FromRawFd, IntoRawFd, OwnedFd, RawFd}, path::Path, time::Duration
};

use libc::{MSG_EOR, MSG_PEEK, c_void, send, recv};

//use crate::addr::*;
use crate::{UnixSocketAddr, helpers::*};
use crate::ancillary::*;
use crate::credentials::*;

/// An unix domain sequential packet connection.
///
/// Sequential-packet connections have an interface similar to streams,
/// but behave more like connected datagram sockets.
///
/// They have guaranteed in-order and reliable delivery,
/// which unix datagrams technically doesn't.
///
/// # Operating system support
///
/// Sequential-packet sockets are supported by Linux, FreeBSD, NetBSD
/// and Illumos, but not by for example macOS or OpenBSD.
///
/// # Zero-length packets
///
/// ... are best avoided:  
/// On Linux and FreeBSD zero-length packets can be sent and received,
/// but there is no way to distinguish receiving one from reaching
/// end of connection unless the packet has an ancillary payload.
/// Also beware of trying to receive with a zero-length buffer,
/// as that will on FreeBSD (and probably other BSDs with seqpacket sockets)
/// always succeed even if there is no packet waiting.
///
/// Illumos and Solaris doesn't support receiving zero-length packets at all:
/// writes succeed but recv() will block.
///
/// # Examples
///
/// What is sent separately is received separately:
///
#[cfg_attr(not(target_vendor="apple"), doc="```")]
#[cfg_attr(target_vendor="apple", doc="```no_run")]
/// let (a, b) = uds_fork::UnixSeqpacketConn::pair().expect("Cannot create seqpacket pair");
///
/// a.send(b"first").unwrap();
/// a.send(b"second").unwrap();
///
/// let mut buffer_big_enough_for_both = [0; 20];
/// let len = b.recv(&mut buffer_big_enough_for_both).unwrap();
/// assert_eq!(&buffer_big_enough_for_both[..len], b"first");
/// let len = b.recv(&mut buffer_big_enough_for_both).unwrap();
/// assert_eq!(&buffer_big_enough_for_both[..len], b"second");
/// ```
///
/// Connect to a listener on a socket file and write to it:
///
#[cfg_attr(not(target_vendor="apple"), doc="```")]
#[cfg_attr(target_vendor="apple", doc="```no_run")]
/// use uds_fork::{UnixSeqpacketListener, UnixSeqpacketConn};
///
/// let file_path = "/tmp/seqpacket.socket";
/// let _ = std::fs::remove_file(file_path); // pre-emptively delete just in case
/// let listener = UnixSeqpacketListener::bind(file_path)
///     .expect("create seqpacket listener");
/// let conn = UnixSeqpacketConn::connect(file_path)
///     .expect("connect to seqpacket listener");
///
/// let message = "Hello, listener";
/// let sent = conn.send(message.as_bytes()).unwrap();
/// assert_eq!(sent, message.len());
///
/// std::fs::remove_file(file_path).unwrap(); // clean up after ourselves
/// ```
///
/// Connect to a listener on an abstract address:
///
#[cfg_attr(any(target_os="linux", target_os="android"), doc="```")]
#[cfg_attr(not(any(target_os="linux", target_os="android")), doc="```no_run")]
/// use uds_fork::{UnixSeqpacketListener, UnixSeqpacketConn, UnixSocketAddr};
///
/// let addr = UnixSocketAddr::new("@seqpacket example").unwrap();
/// let listener = UnixSeqpacketListener::bind_unix_addr(&addr)
///     .expect("create abstract seqpacket listener");
/// let _client = UnixSeqpacketConn::connect_unix_addr(&addr)
///     .expect("connect to abstract seqpacket listener");
/// let (_server, _addr) = listener.accept_unix_addr().unwrap();
/// ```
#[derive(Debug)]
#[repr(transparent)]
pub struct UnixSeqpacketConn 
{
    fd: OwnedFd,
}

impl From<OwnedFd> for UnixSeqpacketConn
{
    fn from(ofd: OwnedFd) -> Self 
    {
        let sa_fam = get_socket_family(&ofd).unwrap();
        let sa_type = get_socket_type(&ofd).unwrap() & 0x00000FFF;

        if sa_fam as i32 != libc::AF_UNIX || sa_type != libc::SOCK_SEQPACKET
        {
            panic!("assertion trap: provided FD is not AF_UNIX & SOCK_SEQPACKET, {} {}", 
                sa_fam, sa_type);
        }

        return UnixSeqpacketConn{ fd: ofd };
    }
}

impl From<UnixSeqpacketConn> for OwnedFd
{
    fn from(value: UnixSeqpacketConn) -> Self 
    {
        return value.fd;
    }
}

impl FromRawFd for UnixSeqpacketConn
{
    unsafe 
    fn from_raw_fd(fd: RawFd) -> Self 
    {
        UnixSeqpacketConn::from( unsafe { OwnedFd::from_raw_fd(fd) } )
    }
}

impl AsRawFd for UnixSeqpacketConn
{
    fn as_raw_fd(&self) -> RawFd 
    {
        self.fd.as_raw_fd()
    }
}
impl IntoRawFd for UnixSeqpacketConn
{
    fn into_raw_fd(self) -> RawFd 
    {
        self.fd.into_raw_fd()
    }
}

impl AsFd for UnixSeqpacketConn
{
    fn as_fd(&self) -> BorrowedFd<'_> 
    {
        self.fd.as_fd()
    }
}

impl UnixSeqpacketConn 
{
    /// Connects to an unix seqpacket server listening at `path`.
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
        let socket = Socket::<SocketSeqPkt>::new(false)?;
        socket.set_unix_peer_addr(addr)?;
        
        return Ok(UnixSeqpacketConn { fd: socket.into() });
    }
    
    /// Binds to an address before connecting to a listening seqpacet socket.
    pub 
    fn connect_from_to_unix_addr(from: &UnixSocketAddr,  to: &UnixSocketAddr) -> Result<Self, io::Error> 
    {
        let socket = Socket::<SocketSeqPkt>::new(false)?;
        socket.set_unix_local_addr(from)?;
        socket.set_unix_peer_addr(to)?;
        
        return Ok(UnixSeqpacketConn{ fd: socket.into() });
    }

    /// Creates a pair of unix-domain seqpacket conneections connected to each other.
    ///
    /// # Examples
    ///
    #[cfg_attr(not(target_vendor="apple"), doc="```")]
    #[cfg_attr(target_vendor="apple", doc="```no_run")]
    /// let (a, b) = uds_fork::UnixSeqpacketConn::pair().unwrap();
    /// assert!(a.local_unix_addr().unwrap().is_unnamed());
    /// assert!(b.local_unix_addr().unwrap().is_unnamed());
    ///
    /// a.send(b"hello").unwrap();
    /// b.recv(&mut[0; 20]).unwrap();
    /// ```
    pub 
    fn pair() -> Result<(Self, Self), io::Error> 
    {
        let pair = Socket::<SocketSeqPkt>::pair(false)?;
        
        return Ok(
            (
                UnixSeqpacketConn { fd: pair.0.into() },
                UnixSeqpacketConn { fd: pair.1.into() }
            )
        );
    }

    /// Returns the address of this side of the connection.
    pub 
    fn local_unix_addr(&self) -> Result<UnixSocketAddr, io::Error> 
    {
        get_unix_local_addr(&self)
    }

    /// Returns the address of the other side of the connection.
    pub 
    fn peer_unix_addr(&self) -> Result<UnixSocketAddr, io::Error> 
    {
        get_unix_peer_addr(&self)
    }

    /// Returns information about the process of the peer when the connection was established.
    ///
    /// See documentation of the returned type for details.
    pub 
    fn initial_peer_credentials(&self) -> Result<ConnCredentials, io::Error> 
    {
        peer_credentials(&self)
    }

    /// Returns the SELinux security context of the process that created the other
    /// end of this connection.
    ///
    /// Will return an error on other operating systems than Linux or Android,
    /// and also if running inside kubernetes.
    /// On success the number of bytes used is returned. (like `Read`)
    ///
    /// The default security context is `unconfined`, without any trailing NUL.  
    /// A buffor of 50 bytes is probably always big enough.
    pub 
    fn initial_peer_selinux_context(&self,  buf: &mut[u8]) -> Result<usize, io::Error> 
    {
        selinux_context(&self, buf)
    }


    /// Sends a packet to the peer.
    pub 
    fn send(&self, packet: &[u8]) -> Result<usize, io::Error> 
    {
        let ptr = packet.as_ptr() as *const c_void;
        let flags = MSG_NOSIGNAL | MSG_EOR;
        let sent = cvt_r!(unsafe { send(self.fd.as_raw_fd(), ptr, packet.len(), flags) })?;
        
        
        return Ok(sent as usize);
    }

    /// Sends a packet to the peer.
    pub 
    fn send_flags(&self,  packet: &[u8], flags: i32) -> Result<usize, io::Error> 
    {
        let ptr = packet.as_ptr() as *const c_void;
        let sent = cvt_r!(unsafe { send(self.fd.as_raw_fd(), ptr, packet.len(), flags) })?;
        
        return Ok(sent as usize);
    }

    /// Receives a packet from the peer.
    pub 
    fn recv(&self, buffer: &mut[u8]) -> Result<usize, io::Error> 
    {
        let ptr = buffer.as_ptr() as *mut c_void;
        let received = cvt_r!(unsafe { recv(self.fd.as_raw_fd(), ptr, buffer.len(), MSG_NOSIGNAL) })?;
        
        return Ok(received as usize);
    }

    /// Sends a packet assembled from multiple byte slices.
    pub 
    fn send_vectored(&self,  slices: &[IoSlice]) -> Result<usize, io::Error> 
    {
        // Can't use writev() because we need to pass flags,
        // and the flags accepted by pwritev2() aren't the one we need to pass.
        send_ancillary(&self, None, MSG_EOR, slices, Vec::new(), None)
    }
    /// Reads a packet into multiple buffers.
    ///
    /// The returned `bool` indicates whether the packet was truncated due to
    /// too short buffers.
    pub 
    fn recv_vectored(&self,  buffers: &mut[IoSliceMut]) -> Result<(usize, bool), io::Error> 
    {
        recv_ancillary(&self, None, 0, buffers, &mut[])
            .map(|(bytes, ancillary)| (bytes, ancillary.message_truncated()) )
    }

    /// Sends a packet with associated file descriptors.
    pub 
    fn send_fds(&self, bytes: &[u8], fds: Vec<OwnedFd>) -> Result<usize, io::Error> 
    {
        send_ancillary(&self, None, MSG_EOR, &[IoSlice::new(bytes)], fds, None)
    }

    /// Receives a packet and associated file descriptors.
    pub 
    fn recv_fds(&self, byte_buffer: &mut[u8], fd_buffer: &mut Vec<OwnedFd>) -> Result<(usize, bool, usize), io::Error> 
    {
        recv_fds(&self, None, &mut[IoSliceMut::new(byte_buffer)], Some(fd_buffer))
    }

    /// Receives a packet without removing it from the incoming queue.
    ///
    /// # Examples
    ///
    #[cfg_attr(not(target_vendor="apple"), doc="```")]
    #[cfg_attr(target_vendor="apple", doc="```no_run")]
    /// let (a, b) = uds_fork::UnixSeqpacketConn::pair().unwrap();
    /// a.send(b"hello").unwrap();
    /// let mut buf = [0u8; 10];
    /// assert_eq!(b.peek(&mut buf[..1]).unwrap(), 1);
    /// assert_eq!(&buf[..2], &[b'h', 0]);
    /// assert_eq!(b.peek(&mut buf).unwrap(), 5);
    /// assert_eq!(&buf[..5], b"hello");
    /// assert_eq!(b.recv(&mut buf).unwrap(), 5);
    /// assert_eq!(&buf[..5], b"hello");
    /// ```
    pub 
    fn peek(&self,  buffer: &mut[u8]) -> Result<usize, io::Error> 
    {
        let ptr = buffer.as_ptr() as *mut c_void;
        let flags = MSG_NOSIGNAL | MSG_PEEK;
        let received = cvt_r!(unsafe { recv(self.fd.as_raw_fd(), ptr, buffer.len(), flags) })?;
        
        return Ok(received as usize);
    }

    /// Receives a packet without removing it from the incoming queue.
    ///
    /// The returned `bool` indicates whether the packet was truncated due to
    /// the combined buffers being too small.
    pub 
    fn peek_vectored(&self,  buffers: &mut[IoSliceMut]) -> Result<(usize, bool), io::Error> 
    {
        recv_ancillary(&self, None, MSG_PEEK, buffers, &mut[])
            .map(|(bytes, ancillary)| (bytes, ancillary.message_truncated()) )
    }

    /// Returns the value of the `SO_ERROR` option.
    ///
    /// This might only provide errors generated from nonblocking `connect()`s,
    /// which this library doesn't support. It is therefore unlikely to be 
    /// useful, but is provided for parity with stream counterpart in std.
    ///
    /// # Examples
    ///
    #[cfg_attr(not(target_vendor="apple"), doc="```")]
    #[cfg_attr(target_vendor="apple", doc="```no_run")]
    /// let (a, b) = uds_fork::UnixSeqpacketConn::pair().unwrap();
    /// drop(b);
    ///
    /// assert!(a.send(b"anyone there?").is_err());
    /// assert!(a.take_error().unwrap().is_none());
    /// ```
    pub 
    fn take_error(&self) -> Result<Option<io::Error>, io::Error> 
    {
        take_error(&self)
    }


    /// Creates a new file descriptor also pointing to this side of this connection.
    ///
    /// # Examples
    ///
    /// Both new and old can send and receive, and share queues:
    ///
    #[cfg_attr(not(target_vendor="apple"), doc="```")]
    #[cfg_attr(target_vendor="apple", doc="```no_run")]
    /// let (a1, b) = uds_fork::nonblocking::UnixSeqpacketConn::pair().unwrap();
    /// let a2 = a1.try_clone().unwrap();
    ///
    /// a1.send(b"first").unwrap();
    /// a2.send(b"second").unwrap();
    ///
    /// let mut buf = [0u8; 20];
    /// let len = b.recv(&mut buf).unwrap();
    /// assert_eq!(&buf[..len], b"first");
    /// b.send(b"hello first").unwrap();
    /// let len = b.recv(&mut buf).unwrap();
    /// assert_eq!(&buf[..len], b"second");
    /// b.send(b"hello second").unwrap();
    ///
    /// let len = a2.recv(&mut buf).unwrap();
    /// assert_eq!(&buf[..len], b"hello first");
    /// let len = a1.recv(&mut buf).unwrap();
    /// assert_eq!(&buf[..len], b"hello second");
    /// ```
    ///
    /// Clone can still be used after the first one has been closed:
    ///
    #[cfg_attr(not(target_vendor="apple"), doc="```")]
    #[cfg_attr(target_vendor="apple", doc="```no_run")]
    /// let (a, b1) = uds_fork::nonblocking::UnixSeqpacketConn::pair().unwrap();
    /// a.send(b"hello").unwrap();
    ///
    /// let b2 = b1.try_clone().unwrap();
    /// drop(b1);
    /// assert_eq!(b2.recv(&mut[0; 10]).unwrap(), "hello".len());
    /// ```
    pub 
    fn try_clone(&self) -> Result<Self, io::Error> 
    {
        let cloned = Socket::<SocketSeqPkt>::try_clone_from(self)?;

        return Ok(UnixSeqpacketConn { fd: cloned.into() });
    }

    /// Sets the read timeout to the duration specified.
    ///
    /// If the value specified is `None`, then `recv()` and its variants will
    /// block indefinitely.  
    /// An error is returned if the duration is zero.
    ///
    /// The duration is rounded to microsecond precission.
    /// Currently it's rounded down except if that would make it all zero.
    ///
    /// # Operating System Support
    ///
    /// On Illumos (and pressumably also Solaris) timeouts appears not to work
    /// for unix domain sockets.
    ///
    /// # Examples
    ///
    #[cfg_attr(not(any(target_vendor="apple", target_os="illumos", target_os="solaris")), doc="```")]
    #[cfg_attr(any(target_vendor="apple", target_os="illumos", target_os="solaris"), doc="```no_run")]
    /// use std::io::ErrorKind;
    /// use std::time::Duration;
    /// use uds_fork::UnixSeqpacketConn;
    ///
    /// let (a, b) = UnixSeqpacketConn::pair().unwrap();
    /// a.set_read_timeout(Some(Duration::new(0, 2_000_000))).unwrap();
    /// let error = a.recv(&mut[0; 1024]).unwrap_err();
    /// assert_eq!(error.kind(), ErrorKind::WouldBlock);
    /// ```
    pub 
    fn set_read_timeout(&self, timeout: Option<Duration>) -> Result<(), io::Error> 
    {
        set_timeout(self.fd.as_fd(), TimeoutDirection::Read, timeout)
    }

    /// Returns the read timeout of this socket.
    ///
    /// `None` is returned if there is no timeout.
    ///
    /// Note that subsecond parts might have been be rounded by the OS
    /// (in addition to the rounding to microsecond in `set_read_timeout()`).
    ///
    /// # Examples
    ///
    #[cfg_attr(not(any(target_vendor="apple", target_os="illumos", target_os="solaris")), doc="```")]
    #[cfg_attr(any(target_vendor="apple", target_os="illumos", target_os="solaris"), doc="```no_run")]
    /// use uds_fork::UnixSeqpacketConn;
    /// use std::time::Duration;
    ///
    /// let timeout = Some(Duration::new(2, 0));
    /// let conn = UnixSeqpacketConn::pair().unwrap().0;
    /// conn.set_read_timeout(timeout).unwrap();
    /// assert_eq!(conn.read_timeout().unwrap(), timeout);
    /// ```
    pub 
    fn read_timeout(&self) -> Result<Option<Duration>, io::Error> 
    {
        get_timeout(self.fd.as_fd(), TimeoutDirection::Read)
    }

    /// Sets the write timeout to the duration specified.
    ///
    /// If the value specified is `None`, then `send()` and its variants will
    /// block indefinitely.  
    /// An error is returned if the duration is zero.
    ///
    /// # Operating System Support
    ///
    /// On Illumos (and pressumably also Solaris) timeouts appears not to work
    /// for unix domain sockets.
    ///
    /// # Examples
    ///
    #[cfg_attr(not(any(target_vendor="apple", target_os="illumos", target_os="solaris")), doc="```")]
    #[cfg_attr(any(target_vendor="apple", target_os="illumos", target_os="solaris"), doc="```no_run")]
    /// # use std::io::ErrorKind;
    /// # use std::time::Duration;
    /// # use uds_fork::UnixSeqpacketConn;
    /// #
    /// let (conn, _other) = UnixSeqpacketConn::pair().unwrap();
    /// conn.set_write_timeout(Some(Duration::new(0, 500 * 1000))).unwrap();
    /// loop {
    ///     if let Err(e) = conn.send(&[0; 1000]) {
    ///         assert_eq!(e.kind(), ErrorKind::WouldBlock, "{}", e);
    ///         break
    ///     }
    /// }
    /// ```
    pub 
    fn set_write_timeout(&self,  timeout: Option<Duration>)-> Result<(), io::Error> 
    {
        set_timeout(self.fd.as_fd(), TimeoutDirection::Write, timeout)
    }

    /// Returns the write timeout of this socket.
    ///
    /// `None` is returned if there is no timeout.
    ///
    /// # Examples
    ///
    #[cfg_attr(not(target_vendor="apple"), doc="```")]
    #[cfg_attr(target_vendor="apple", doc="```no_run")]
    /// let conn = uds_fork::UnixSeqpacketConn::pair().unwrap().0;
    /// assert!(conn.write_timeout().unwrap().is_none());
    /// ```
    pub 
    fn write_timeout(&self) -> Result<Option<Duration>, io::Error> 
    {
        get_timeout(self.fd.as_fd(), TimeoutDirection::Write)
    }

    /// Enables or disables nonblocking mode.
    ///
    /// Consider using the nonblocking variant of this type instead.
    /// This method mainly exists for feature parity with std's `UnixStream`.
    ///
    /// # Examples
    ///
    /// Trying to receive when there are no packets waiting:
    ///
    #[cfg_attr(not(target_vendor="apple"), doc="```")]
    #[cfg_attr(target_vendor="apple", doc="```no_run")]
    /// # use std::io::ErrorKind;
    /// # use uds_fork::UnixSeqpacketConn;
    /// let (a, b) = UnixSeqpacketConn::pair().expect("create seqpacket pair");
    /// a.set_nonblocking(true).unwrap();
    /// assert_eq!(a.recv(&mut[0; 20]).unwrap_err().kind(), ErrorKind::WouldBlock);
    /// ```
    ///
    /// Trying to send when the OS buffer for the connection is full:
    ///
    #[cfg_attr(not(target_vendor="apple"), doc="```")]
    #[cfg_attr(target_vendor="apple", doc="```no_run")]
    /// # use std::io::ErrorKind;
    /// # use uds_fork::UnixSeqpacketConn;
    /// let (a, b) = UnixSeqpacketConn::pair().expect("create seqpacket pair");
    /// a.set_nonblocking(true).unwrap();
    /// loop {
    ///     if let Err(error) = a.send(&[b'#'; 1000]) {
    ///         assert_eq!(error.kind(), ErrorKind::WouldBlock);
    ///         break;
    ///     }
    /// }
    /// ```
    pub 
    fn set_nonblocking(&self,  nonblocking: bool) -> Result<(), io::Error> 
    {
        set_nonblocking(&self, nonblocking)
    }

    /// Shuts down the read, write, or both halves of this connection.
    pub 
    fn shutdown(&self, how: Shutdown) -> io::Result<()> 
    {
        let how = 
            match how 
            {
                Shutdown::Read => libc::SHUT_RD,
                Shutdown::Write => libc::SHUT_WR,
                Shutdown::Both => libc::SHUT_RDWR,
            };

        unsafe { cvt!(libc::shutdown(self.as_raw_fd(), how)) }?;
        
        return Ok(());
    }
}



/// An unix domain listener for sequential packet connections.
///
/// See [`UnixSeqpacketConn`](struct.UnixSeqpacketConn.html) for a description
/// of this type of connection.
///
/// # Examples
///
#[cfg_attr(not(target_vendor="apple"), doc="```")]
#[cfg_attr(target_vendor="apple", doc="```no_run")]
/// let file_path = "/tmp/seqpacket_listener.socket";
/// let _ = std::fs::remove_file(file_path);
/// let listener = uds_fork::UnixSeqpacketListener::bind(file_path)
///     .expect("Create seqpacket listener");
/// let _client = uds_fork::UnixSeqpacketConn::connect(file_path).unwrap();
/// let (conn, _addr) = listener.accept_unix_addr().unwrap();
/// conn.send(b"Welcome").unwrap();
/// # std::fs::remove_file(file_path).unwrap();
/// ```
#[derive(Debug)]
#[repr(transparent)]
pub struct UnixSeqpacketListener 
{
    fd: OwnedFd
}


impl From<OwnedFd> for UnixSeqpacketListener
{
    fn from(ofd: OwnedFd) -> Self 
    {
        let sa_fam = get_socket_family(&ofd).unwrap();
        let sa_type = get_socket_type(&ofd).unwrap() & 0x00000FFF;

        if sa_fam as i32 != libc::AF_UNIX || sa_type != libc::SOCK_SEQPACKET
        {
            panic!("assertion trap: provided FD is not AF_UNIX & SOCK_SEQPACKET, {} {}", 
                sa_fam, sa_type);
        }

        return UnixSeqpacketListener{ fd: ofd };
    }
}

impl From<UnixSeqpacketListener> for OwnedFd
{
    fn from(value: UnixSeqpacketListener) -> Self 
    {
        return value.fd;
    }
}

impl FromRawFd for UnixSeqpacketListener
{
    unsafe 
    fn from_raw_fd(fd: RawFd) -> Self 
    {
        UnixSeqpacketListener::from( unsafe { OwnedFd::from_raw_fd(fd) } )
    }
}

impl AsRawFd for UnixSeqpacketListener
{
    fn as_raw_fd(&self) -> RawFd 
    {
        self.fd.as_raw_fd()
    }
}

impl IntoRawFd for UnixSeqpacketListener
{
    fn into_raw_fd(self) -> RawFd 
    {
        self.fd.into_raw_fd()
    }
}

impl AsFd for UnixSeqpacketListener
{
    fn as_fd(&self) -> BorrowedFd<'_> 
    {
        self.fd.as_fd()
    }
}

impl UnixSeqpacketListener 
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
        let socket = Socket::<SocketSeqPkt>::new(false)?;

        socket.set_unix_local_addr(addr)?;
        socket.start_listening()?;
        
        return Ok(UnixSeqpacketListener { fd: socket.into() });
    }

    /// Returns the address the socket is listening on.
    pub 
    fn local_unix_addr(&self) -> Result<UnixSocketAddr, io::Error> 
    {
        get_unix_local_addr(&self)
    }

    /// Accepts a new incoming connection to this listener.
    pub 
    fn accept_unix_addr(&self)-> Result<(UnixSeqpacketConn, UnixSocketAddr), io::Error> 
    {
        let (socket, addr) = Socket::<SocketSeqPkt>::accept_from(&self, false)?;
        let conn = UnixSeqpacketConn { fd: socket.into() };
        
        return Ok((conn, addr));
    }

    /// Returns the value of the `SO_ERROR` option.
    ///
    /// This might never produce any errors for listeners. It is therefore
    /// unlikely to be useful, but is provided for parity with
    /// `std::unix::net::UnixListener`.
    pub 
    fn take_error(&self) -> Result<Option<io::Error>, io::Error> 
    {
        take_error(&self)
    }

    /// Creates a new file descriptor listening for the same connections.
    pub 
    fn try_clone(&self) -> Result<Self, io::Error> 
    {
        let cloned = Socket::<SocketSeqPkt>::try_clone_from(&self)?;
        
        return Ok(UnixSeqpacketListener { fd: cloned.into() });
    }

    /// Sets a maximum duration to wait in a single `accept()` on this socket.
    ///
    /// `None` disables a previously set timeout.
    /// An error is returned if the duration is zero.
    ///
    /// # Operating System Support
    ///
    /// Only Linux appers to apply timeouts to `accept()`.  
    /// On macOS, FreeBSD and NetBSD, timeouts are silently ignored.  
    /// On Illumos setting timeouts for all unix domain sockets silently fails.
    ///
    /// On OSes where timeouts are known to not work, this function will
    /// return an error even if setting the timeout didn't fail.
    ///
    /// # Examples
    ///
    #[cfg_attr(any(target_os="linux", target_os="android"), doc="```")]
    #[cfg_attr(not(any(target_os="linux", target_os="android")), doc="```no_run")]
    /// # use uds_fork::{UnixSeqpacketListener, UnixSocketAddr};
    /// # use std::io::ErrorKind;
    /// # use std::time::Duration;
    /// #
    /// # let addr = UnixSocketAddr::new("@set_timeout").unwrap();
    /// let listener = UnixSeqpacketListener::bind_unix_addr(&addr).unwrap();
    /// listener.set_timeout(Some(Duration::new(0, 200_000_000))).unwrap();
    /// let err = listener.accept_unix_addr().unwrap_err();
    /// assert_eq!(err.kind(), ErrorKind::WouldBlock);
    /// ```
    pub 
    fn set_timeout(&self,  timeout: Option<Duration>) -> Result<(), io::Error> 
    {
        let res = set_timeout(&self, TimeoutDirection::Read, timeout);

        #[cfg(any(
                target_vendor="apple", target_os="freebsd",
                target_os="netbsd",
                target_os="illumos", target_os="solaris",
            ))]
        {
            if res.is_ok() == true && timeout.is_some() == true
            {
                return Err(
                    io::Error::new(
                        ErrorKind::InvalidInput,
                        "listener timeouts are not supported on this OS"
                    )
                );
            }
        }

        return res;
    }

    /// Returns the timeout for `accept()` on this socket.
    ///
    /// `None` is returned if there is no timeout.
    ///
    /// Even if a timeout has is set, it is ignored by `accept()` on
    /// most operating systems except Linux.
    ///
    /// # Examples
    ///
    #[cfg_attr(any(target_os="linux", target_os="android"), doc="```")]
    #[cfg_attr(not(any(target_os="linux", target_os="android")), doc="```no_run")]
    /// # use uds_fork::{UnixSeqpacketListener, UnixSocketAddr};
    /// # use std::time::Duration;
    /// #
    /// # let addr = UnixSocketAddr::new("@timeout").unwrap();
    /// let listener = UnixSeqpacketListener::bind_unix_addr(&addr).unwrap();
    /// assert_eq!(listener.timeout().unwrap(), None);
    /// let timeout = Some(Duration::new(2, 0));
    /// listener.set_timeout(timeout).unwrap();
    /// assert_eq!(listener.timeout().unwrap(), timeout);
    /// ```
    pub 
    fn timeout(&self) -> Result<Option<Duration>, io::Error> 
    {
        get_timeout(&self, TimeoutDirection::Read)
    }

    /// Enables or disables nonblocking-ness of [`accept_unix_addr()`](#method.accept_unix addr).
    ///
    /// The returned connnections will still be in blocking mode regardsless.
    ///
    /// Consider using the nonblocking variant of this type instead;
    /// this method mostly exists for feature parity with std's `UnixListener`.
    ///
    /// # Examples
    ///
    #[cfg_attr(not(target_vendor="apple"), doc="```")]
    #[cfg_attr(target_vendor="apple", doc="```no_run")]
    /// # use std::io::ErrorKind;
    /// # use uds_fork::{UnixSocketAddr, UnixSeqpacketListener};
    /// 
    /// let file_path = "/tmp/nonblocking_seqpacket_listener1.socket";
    /// let addr = UnixSocketAddr::from_path(file_path).unwrap();
    /// let _ = std::fs::remove_file(file_path);
    /// let listener = UnixSeqpacketListener::bind_unix_addr(&addr).expect("create listener");
    /// listener.set_nonblocking(true).expect("enable noblocking mode");
    /// assert_eq!(listener.accept_unix_addr().unwrap_err().kind(), ErrorKind::WouldBlock);
    /// # std::fs::remove_file(file_path).expect("delete socket file");
    /// ```
    pub 
    fn set_nonblocking(&self,  nonblocking: bool) -> Result<(), io::Error> 
    {
        set_nonblocking(&self, nonblocking)
    }
}



/// A non-blocking unix domain sequential-packet connection.
///
/// Differs from [`uds_fork::UnixSeqpacketConn`](../struct.UnixSeqpacketConn.html)
/// in that all operations that send or receive data will return an `Error` of
/// kind `ErrorKind::WouldBlock` instead of blocking.
/// This is done by creating the socket as non-blocking, and not by passing
/// `MSG_DONTWAIT`. If creating this type from a raw file descriptor, ensure
/// the fd is set to nonblocking before using it through this type.
/// 
/// # Examples
///
/// Sending or receiving when it would block a normal socket:
///
#[cfg_attr(not(target_vendor="apple"), doc="```")]
#[cfg_attr(target_vendor="apple", doc="```no_run")]
/// use uds_fork::nonblocking::UnixSeqpacketConn;
/// use std::io::ErrorKind;
///
/// let (a, b) = UnixSeqpacketConn::pair().expect("create nonblocking seqpacket pair");
///
/// // trying to receive when there are no packets waiting
/// assert_eq!(a.recv(&mut[0]).unwrap_err().kind(), ErrorKind::WouldBlock);
///
/// // trying to send when the OS buffer for the connection is full
/// loop {
///     if let Err(error) = a.send(&[0u8; 1000]) {
///         assert_eq!(error.kind(), ErrorKind::WouldBlock);
///         break;
///     }
/// }
/// ```
//#[deprecated = "Use UnixSeqpacketListener set_nonblocking(true)!"]
#[derive(Debug)]
#[repr(transparent)]
pub struct NonblockingUnixSeqpacketConn 
{
    usc: UnixSeqpacketConn,
}

impl From<OwnedFd> for NonblockingUnixSeqpacketConn
{
    fn from(value: OwnedFd) -> Self 
    {
        let usc = UnixSeqpacketConn::from(value);
        usc.set_nonblocking(true).unwrap();

        return Self{ usc: usc };
    }
}

impl From<NonblockingUnixSeqpacketConn> for OwnedFd
{
    fn from(value: NonblockingUnixSeqpacketConn) -> Self 
    {
        return value.usc.fd;
    }
}

impl FromRawFd for NonblockingUnixSeqpacketConn
{
    unsafe 
    fn from_raw_fd(fd: RawFd) -> Self 
    {
        let usc = unsafe{ UnixSeqpacketConn::from_raw_fd(fd) };
        usc.set_nonblocking(true).unwrap();

        return Self{ usc: usc };
    }
}

impl AsRawFd for NonblockingUnixSeqpacketConn
{
    fn as_raw_fd(&self) -> RawFd 
    {
        self.usc.as_raw_fd()
    }
}
impl IntoRawFd for NonblockingUnixSeqpacketConn
{
    fn into_raw_fd(self) -> RawFd 
    {
        self.usc.into_raw_fd()
    }
}

impl AsFd for NonblockingUnixSeqpacketConn
{
    fn as_fd(&self) -> BorrowedFd<'_> 
    {
        self.usc.as_fd()
    }
}

impl Deref for NonblockingUnixSeqpacketConn
{
    type Target = UnixSeqpacketConn;

    fn deref(&self) -> &Self::Target 
    {
        &self.usc
    }
}

impl DerefMut for NonblockingUnixSeqpacketConn
{
    fn deref_mut(&mut self) -> &mut Self::Target 
    {
        &mut self.usc
    }
}

// can't Deref<Target=UnixSeqpacketConn> because that would include try_clone()
// and later set_(read|write)_timeout()
impl NonblockingUnixSeqpacketConn 
{
    /// Connects to an unix seqpacket server listening at `path`.
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
        let socket = Socket::<SocketSeqPkt>::new(true)?;
        socket.set_unix_peer_addr(addr)?;
        
        return Ok(
            NonblockingUnixSeqpacketConn 
            {
                usc: UnixSeqpacketConn { fd: socket.into() }
            }
        );
    }
    
    /// Binds to an address before connecting to a listening seqpacet socket.
    pub 
    fn connect_from_to_unix_addr(from: &UnixSocketAddr,  to: &UnixSocketAddr) -> Result<Self, io::Error> 
    {
        let socket = Socket::<SocketSeqPkt>::new(true)?;
        socket.set_unix_local_addr(from)?;
        socket.set_unix_peer_addr(to)?;
        
        return Ok(
            NonblockingUnixSeqpacketConn 
            {
                usc: UnixSeqpacketConn { fd: socket.into() }
            }
        );
    }

    /// Creates a pair of unix-domain seqpacket conneections connected to each other.
    ///
    /// # Examples
    ///
    #[cfg_attr(not(target_vendor="apple"), doc="```")]
    #[cfg_attr(target_vendor="apple", doc="```no_run")]
    /// let (a, b) = uds_fork::UnixSeqpacketConn::pair().unwrap();
    /// assert!(a.local_unix_addr().unwrap().is_unnamed());
    /// assert!(b.local_unix_addr().unwrap().is_unnamed());
    ///
    /// a.send(b"hello").unwrap();
    /// b.recv(&mut[0; 20]).unwrap();
    /// ```
    pub 
    fn pair() -> Result<(Self, Self), io::Error> 
    {
        let pair = Socket::<SocketSeqPkt>::pair(true)?;
        
        return Ok(
            (
                Self{ usc: UnixSeqpacketConn { fd: pair.0.into() } },
                Self{ usc: UnixSeqpacketConn { fd: pair.1.into() } },
            )
        );
    }

    pub 
    fn try_clone(&self) -> Result<Self, io::Error> 
    {
        let cloned = Socket::<SocketSeqPkt>::try_clone_from(self)?;

        return Ok(
            NonblockingUnixSeqpacketConn 
            {
                usc: UnixSeqpacketConn { fd: cloned.into() }
            }
        );
    }
}


/// A non-blocking unix domain listener for sequential-packet connections.
///
/// Differs from [`UnixSeqpacketListener`](../struct.UnixSeqpacketListener.html)
/// in that [`accept()`](struct.NonblockingUnixSeqpacketListener.html#method.accept)
/// returns non-blocking [connection sockets](struct.NonblockingUnixSeqpacketConn.html)
/// and doesn't block if no client `connect()`ions are pending.
///
/// This type can be used with mio if the `mio_08` feature is enabled:
///
/// ```toml
/// uds = { version = "x.y", features=["mio_08"] }
/// ```
///
/// # Examples
///
#[cfg_attr(not(target_vendor="apple"), doc="```")]
#[cfg_attr(target_vendor="apple", doc="```no_run")]
/// use uds_fork::nonblocking::{UnixSeqpacketListener, UnixSeqpacketConn};
/// use std::io::ErrorKind;
///
/// let file_path = "/tmp/nonblocking_seqpacket_listener2.socket";
/// 
/// let _ = std::fs::remove_file(file_path);
/// let listener = UnixSeqpacketListener::bind(file_path)
///     .expect("Cannot create nonblocking seqpacket listener");
///
/// // doesn't block if no connections are waiting:
/// assert_eq!(listener.accept_unix_addr().unwrap_err().kind(), ErrorKind::WouldBlock);
///
/// // returned connections are nonblocking:
/// let _client = UnixSeqpacketConn::connect(file_path).unwrap();
/// let (conn, _addr) = listener.accept_unix_addr().unwrap();
/// assert_eq!(conn.recv(&mut[0u8; 20]).unwrap_err().kind(), ErrorKind::WouldBlock);
/// #
/// # std::fs::remove_file(file_path).unwrap();
/// ```
#[derive(Debug)]
#[repr(transparent)]
pub struct NonblockingUnixSeqpacketListener 
{
    usl: UnixSeqpacketListener,
}

impl From<OwnedFd> for NonblockingUnixSeqpacketListener
{
    fn from(ofd: OwnedFd) -> Self 
    {
        let usl = UnixSeqpacketListener::from(ofd);
        usl.set_nonblocking(true).unwrap();

        return Self{ usl };
    }
}

impl FromRawFd for NonblockingUnixSeqpacketListener
{
    unsafe 
    fn from_raw_fd(fd: RawFd) -> Self 
    {
        let usl = unsafe{ UnixSeqpacketListener::from_raw_fd(fd) };
        usl.set_nonblocking(true).unwrap();

        return Self{ usl };
    }
}


impl From<NonblockingUnixSeqpacketListener> for OwnedFd
{
    fn from(value: NonblockingUnixSeqpacketListener) -> Self 
    {
        return value.usl.fd;
    }
}


impl AsRawFd for NonblockingUnixSeqpacketListener
{
    fn as_raw_fd(&self) -> RawFd 
    {
        self.usl.as_raw_fd()
    }
}

impl IntoRawFd for NonblockingUnixSeqpacketListener
{
    fn into_raw_fd(self) -> RawFd 
    {
        self.usl.into_raw_fd()
    }
}

impl AsFd for NonblockingUnixSeqpacketListener
{
    fn as_fd(&self) -> BorrowedFd<'_> 
    {
        self.usl.as_fd()
    }
}


impl Deref for NonblockingUnixSeqpacketListener
{
    type Target = UnixSeqpacketListener;

    fn deref(&self) -> &Self::Target 
    {
        &self.usl
    }
}

impl DerefMut for NonblockingUnixSeqpacketListener
{
    fn deref_mut(&mut self) -> &mut Self::Target 
    {
        &mut self.usl
    }
}

impl NonblockingUnixSeqpacketListener 
{
    /// Creates a socket that listens for seqpacket connections on the specified socket file.
    pub 
    fn bind<P: AsRef<Path>>(path: P) -> Result<Self, io::Error> 
    {
        let addr = UnixSocketAddr::from_path(&path)?;

        return Self::bind_unix_addr(&addr);
    }

    /// Creates a socket that listens for seqpacket connections on the specified address.
    pub 
    fn bind_unix_addr(addr: &UnixSocketAddr) -> Result<Self, io::Error> 
    {
        let socket = Socket::<SocketSeqPkt>::new(true)?;
        socket.set_unix_local_addr(addr)?;
        socket.start_listening()?;

        return Ok( Self{ usl: UnixSeqpacketListener{ fd: socket.into() }} );
    }

    /// Accepts a non-blocking connection, non-blockingly.
    ///
    /// # Examples
    ///
    /// Doesn't block if no connections are waiting:
    ///
    #[cfg_attr(not(target_vendor="apple"), doc="```")]
    #[cfg_attr(target_vendor="apple", doc="```no_run")]
    /// # use uds_fork::nonblocking::UnixSeqpacketListener;
    /// # use std::io::ErrorKind;
    /// #
    /// let file_path = "/tmp/nonblocking_seqpacket_listener3.socket";
    /// let _ = std::fs::remove_file(file_path);
    /// let listener = UnixSeqpacketListener::bind(file_path)
    ///     .expect("Cannot create nonblocking seqpacket listener");
    /// assert_eq!(listener.accept_unix_addr().unwrap_err().kind(), ErrorKind::WouldBlock);
    /// std::fs::remove_file(file_path).unwrap();
    /// ```
    pub 
    fn accept_unix_addr(&self) -> Result<(NonblockingUnixSeqpacketConn, UnixSocketAddr), io::Error> 
    {
        let (socket, addr) = Socket::<SocketSeqPkt>::accept_from(&self, true)?;
        let conn = NonblockingUnixSeqpacketConn { usc: UnixSeqpacketConn{ fd: socket.into() }};
        
        return Ok((conn, addr));
    }
}
