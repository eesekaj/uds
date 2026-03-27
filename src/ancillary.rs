#![allow(
    clippy::unnecessary_mut_passed, // CMSG_ macros only exist for *const
    clippy::useless_conversion, // not useless on all platforms
    clippy::match_overlapping_arm, // cumbersome to avoid when using inclusive ranges
    clippy::borrow_deref_ref, // avoid infinite loop in Borrow impl
    dead_code // TODO
)]

use std::ops::{Deref, DerefMut};
use std::borrow::{Borrow, BorrowMut, Cow};
use std::os::fd::{AsFd, AsRawFd, FromRawFd, OwnedFd};
use std::os::unix::io::RawFd;
use std::io::{self, ErrorKind, IoSlice, IoSliceMut};
use std::alloc::{self, Layout};
use std::convert::TryInto;
use std::{mem, ptr, slice};
use std::marker::PhantomData;

use libc::{c_int, c_uint, c_void};
use libc::{msghdr, iovec, cmsghdr, sockaddr, sockaddr_un};
use libc::{sendmsg, recvmsg};
//#[cfg(not(any(target_os="illumos", target_os="solaris")))]
use libc::{MSG_TRUNC, MSG_CTRUNC};
#[cfg(not(any(target_os="illumos", target_os="solaris")))]
use libc::{CMSG_SPACE, CMSG_LEN, CMSG_DATA, CMSG_FIRSTHDR, CMSG_NXTHDR};
//#[cfg(not(any(target_os="illumos", target_os="solaris")))]
use libc::{SOL_SOCKET, SCM_RIGHTS};
#[cfg(any(target_os="linux", target_os="android"))]
use libc::SCM_CREDENTIALS;
#[cfg(not(any(target_vendor="apple", target_os="illumos", target_os="solaris", target_os = "haiku")))]
use libc::MSG_CMSG_CLOEXEC;

use crate::helpers::*;
use crate::UnixSocketAddr;
use crate::credentials::{SendCredentials, ReceivedCredentials};
#[cfg(any(target_os="linux", target_os="android"))]
use crate::credentials::RawReceivedCredentials;

// Type of cmsghdr.cmsg_len, which varies between OSes and C libraries
// (can't get away with using ` as _` because we use the max value in some places.)
// cfg based on libc 0.2.82 source code.
#[cfg(any(
    all(target_os="linux", not(target_env="musl")),
    target_os="android",
    target_env="uclibc",
))]
type ControlLen = usize;
#[cfg(not(any(
    all(target_os="linux", not(target_env="musl")),
    target_os="android",
    target_env="uclibc",
)))]
type ControlLen = libc::socklen_t;

/// Safe wrapper around `sendmsg()`.
pub 
fn send_ancillary<FD: AsFd>(
    socket: FD,  
    to: Option<&UnixSocketAddr>,  
    flags: c_int,
    bytes: &[IoSlice],  
    fds: Vec<OwnedFd>,  
    creds: Option<SendCredentials>
) -> Result<usize, io::Error> 
{
    #[cfg(not(any(target_os="linux", target_os="android")))]
    let _ = creds; // silence `unused` warning
    unsafe 
    {
        let mut msg: msghdr = mem::zeroed();
        msg.msg_name = ptr::null_mut();
        msg.msg_namelen = 0;
        msg.msg_iov = bytes.as_ptr() as *mut iovec;
        msg.msg_iovlen = 
            bytes.len().try_into() 
                .map_err(|e|
                    io::Error::new(ErrorKind::InvalidInput, 
                        format!("too many byte slices {}", e))
                )?;

        msg.msg_flags = 0;
        msg.msg_control = ptr::null_mut();
        msg.msg_controllen = 0;

        if let Some(addr) = to 
        {
            let (addr, len) = addr.as_raw();
            msg.msg_name = addr as *const sockaddr_un as *const c_void as *mut c_void;
            msg.msg_namelen = len;
        }

        let mut needed_capacity = 0;

        #[cfg(any(target_os="linux", target_os="android"))]
        let creds = 
            creds.map(
                |creds| 
                {
                    let creds = creds.into_raw();
                    needed_capacity += CMSG_SPACE(mem::size_of_val(&creds) as u32);
                    creds
                }
            );

        if fds.len() > 0 
        {
            if fds.len() > 0xff_ff_ff 
            {
                // need to prevent truncation.
                // I use a lower limit in case the macros don't handle overflow.
                return Err(
                    io::Error::new(ErrorKind::InvalidInput, "too many file descriptors")
                );
            }
            #[cfg(not(any(target_os="illumos", target_os="solaris")))] 
            {
                needed_capacity += CMSG_SPACE(mem::size_of_val::<[OwnedFd]>(&fds) as u32);
            }
            #[cfg(any(target_os="illumos", target_os="solaris"))] 
            {
                return Err(
                    io::Error::new(
                        ErrorKind::Other,
                        "ancillary data support is not implemented yet for Illumos or Solaris"
                    )
                );
            }
        }

        // stack buffer which should be big enough for most scenarios
        #[repr(C, align(8))]
        struct AncillaryFixedBuf<const N: usize>(/*for alignment*/[u8; N]);
        //const anc_cap = AncillaryBuf::MAX_STACK_CAPACITY / (mem::size_of::<cmsghdr>() + mem::size_of::<OwnedFd>());

        let ancillary_buf = 
            AncillaryFixedBuf( [0_u8; unsafe { CMSG_SPACE(60*size_of::<RawFd>() as u32) as usize}] );
        
        //AncillaryFixedBuf([], [mem::zeroed(); AncillaryBuf::MAX_STACK_CAPACITY / mem::size_of::<cmsghdr>()]);

        msg.msg_controllen = needed_capacity as ControlLen;

        let cap: Cow<'_, [u8]> = 
            if needed_capacity as usize >= mem::size_of_val(&ancillary_buf)
            {
                let heap_buf = vec![0_u64; needed_capacity as usize];

                assert_eq!(heap_buf.as_ptr() as usize % mem::align_of::<cmsghdr>(), 0, 
                    "assertion trap: ancillary_buf in heap is not aligned! {:p}", heap_buf.as_ptr());

                let (p, sz, cap) = heap_buf.into_raw_parts();
                let heap_buf = Vec::<u8>::from_raw_parts(p.cast(), sz, cap);

                assert_eq!(heap_buf.as_ptr() as usize % mem::align_of::<cmsghdr>(), 0, 
                    "assertion trap: ancillary_buf in heap is not aligned! {:p}", heap_buf.as_ptr());

                Cow::Owned(heap_buf)
            }
            else 
            {
                assert_eq!(ancillary_buf.0.as_ptr() as usize % mem::align_of::<cmsghdr>(), 0, "assertion trap: ancillary_buf is not aligned!");

                Cow::Borrowed(ancillary_buf.0.as_slice())    
            };

        if needed_capacity != 0 
        {
            msg.msg_control = cap.as_ptr() as *mut c_void;

            #[cfg(not(any(target_os="illumos", target_os="solaris")))] 
            {
                let header_ptr = CMSG_FIRSTHDR(&mut msg);
                assert!(!header_ptr.is_null(), "CMSG_FIRSTHDR returned unexpected NULL pointer");

                #[allow(unused_mut)]
                let mut header = &mut*header_ptr;
                
                #[cfg(any(target_os="linux", target_os="android"))] 
                {
                    if let Some(creds) = creds 
                    {
                        use libc::ucred;

                        header.cmsg_level = SOL_SOCKET;
                        header.cmsg_type = SCM_CREDENTIALS;
                        header.cmsg_len = CMSG_LEN(mem::size_of_val(&creds) as u32) as ControlLen;
                        
                        let data = CMSG_DATA(header) as *mut c_void as *mut ucred;

                        if data.is_aligned() == false
                        {
                            ptr::write_unaligned(data, creds);
                        }
                        else
                        {
                            ptr::write(data, creds);
                        }
                       // *(CMSG_DATA(header) as *mut c_void as *mut _) = creds;
                        
                        let header_ptr = CMSG_NXTHDR(&mut msg, header);
                        if fds.len() > 0 
                        {
                            assert_eq!(header_ptr.is_null(), false, "CMSG_NXTHDR returned unexpected NULL pointer");
                        
                            header = &mut*header_ptr;
                        }
                    }
                }

                if fds.len() > 0 
                {
                    use std::os::fd::IntoRawFd;

                    header.cmsg_level = SOL_SOCKET;
                    header.cmsg_type = SCM_RIGHTS;
                    header.cmsg_len = CMSG_LEN(mem::size_of_val::<[OwnedFd]>(&fds) as u32) as ControlLen;
                    
                    let mut dst = CMSG_DATA(header) as *mut c_void as *mut RawFd;
                    
                    for fd in fds.into_iter().map(|fd| fd.into_raw_fd()) 
                    {
                        if dst.is_aligned() == false
                        {
                            ptr::write_unaligned(dst, fd);
                        }
                        else
                        {
                            ptr::write(dst, fd);
                        }

                        dst = dst.add(1);
                    }
                }
            }
        }

        let result = 
            cvt_r!(sendmsg(socket.as_fd().as_raw_fd(), &msg, flags | MSG_NOSIGNAL));

        result.map(|sent| sent as usize )
    }
}



/// An ancillary data buffer that supports any capacity.
///
/// For reasonable ancillary capacities it uses a stack-based array.
#[repr(C)]
#[derive(Debug)]
pub struct AncillaryBuf 
{
    capacity: ControlLen,
    ptr: *mut u8,
    _align: [cmsghdr; 0],
    on_stack: [u8; Self::MAX_STACK_CAPACITY],
}
impl Drop for AncillaryBuf 
{
    fn drop(&mut self) 
    {
        unsafe 
        {
            if self.capacity as usize > Self::MAX_STACK_CAPACITY 
            {
                let layout = 
                    Layout::from_size_align(self.capacity as usize, mem::align_of::<cmsghdr>())
                        .unwrap();

                alloc::dealloc(self.ptr as *mut u8, layout);
            }
        }
    }
}
impl AncillaryBuf 
{
    pub const MAX_STACK_CAPACITY: usize = 1024; //256;

    pub const MAX_CAPACITY: usize = ControlLen::max_value() as usize;

    pub 
    fn with_capacity(bytes: usize) -> io::Result<Self> 
    {
        return Ok(
            Self 
            {
                capacity: 
                    bytes as ControlLen,
                ptr: 
                    match bytes 
                    {
                        0..=Self::MAX_STACK_CAPACITY => 
                            ptr::null_mut(),
                        0..=Self::MAX_CAPACITY => 
                            unsafe 
                            {
                                let layout = 
                                    Layout::from_size_align(
                                        bytes as usize,
                                        mem::align_of::<cmsghdr>()
                                    )
                                    .unwrap();

                                alloc::alloc_zeroed(layout)
                            },
                        _ => 
                            return 
                                Err(
                                    io::Error::new(
                                        ErrorKind::OutOfMemory, 
                                        format!("capacity is too high {}", bytes)
                                    )
                                )
                    },
                _align: 
                    [],
                on_stack: 
                    [0; Self::MAX_STACK_CAPACITY],
            }
        );
    }

    pub 
    fn with_fd_capacity(num_fds: usize) -> io::Result<Self>
    {
        #[cfg(not(any(target_os="illumos", target_os="solaris")))]
        unsafe 
        {
            // To prevent truncation or overflow (in CMSG macros or elsewhere)
            // cmsghdr having bigger alignment than RawFd isn't a problem,
            //  as that doesn't affect the maximum capacity.
            // If the size of cmsghdr is not divisible by the size of RawFd
            //  (which could theoretically happen if all three cmsghdr fields
            //  are u16 or u8 somewher), then some bytes will not be usable.
            //  But dividing by the size of RawFd silently takes care of that
            //  as it rounds down.
            // FIXME This should ideally be a constant, but it's not really a
            //  problem. (libc doesn't have a const_fn feature, probably
            //  because old compilers wouldn't be able to even parse it.
            let max_fds =
                (c_uint::max_value() - CMSG_SPACE(0)) as usize / mem::size_of::<RawFd>();

            if num_fds == 0 
            {
                return Self::with_capacity(0)
            } 
            else if num_fds <= max_fds 
            {
                let payload_bytes = num_fds * mem::size_of::<RawFd>();
                
                return 
                    Self::with_capacity(CMSG_SPACE(payload_bytes as c_uint) as usize)
            } 
            else 
            {
                return Err(
                    io::Error::new(
                        ErrorKind::FileTooLarge, 
                        format!("too many file descriptors for ancillary buffer length, max: {} req: {}",
                            max_fds, num_fds)
                    )
                );
            }
        }
        #[cfg(any(target_os="illumos", target_os="solaris"))] {
            Self::with_capacity(num_fds) // any non-zero value is not supported
        }
    }
}
impl Default for AncillaryBuf 
{
    fn default() -> Self 
    {
        Self 
        {
            capacity: Self::MAX_STACK_CAPACITY as ControlLen,
            ptr: ptr::null_mut(),
            _align: [],
            on_stack: [0; Self::MAX_STACK_CAPACITY],
        }
    }
}

impl Deref for AncillaryBuf 
{
    type Target = [u8];

    fn deref(&self) -> &[u8] 
    {
        unsafe 
        {
            self.on_stack.get(..self.capacity as usize)
                .unwrap_or_else(|| slice::from_raw_parts(self.ptr, self.capacity as usize) )
        }
    }
}
impl DerefMut for AncillaryBuf 
{
    fn deref_mut(&mut self) -> &mut[u8] 
    {
        unsafe 
        {
            match self.on_stack.get_mut(..self.capacity as usize) 
            {
                Some(on_stack) => on_stack,
                None => slice::from_raw_parts_mut(self.ptr, self.capacity as usize)
            }
        }
    }
}
impl Borrow<[u8]> for AncillaryBuf 
{
    fn borrow(&self) -> &[u8] 
    {
        &*self
    }
}
impl BorrowMut<[u8]> for AncillaryBuf 
{
    fn borrow_mut(&mut self) -> &mut[u8] 
    {
        &mut*self
    }
}
impl AsRef<[u8]> for AncillaryBuf 
{
    fn as_ref(&self) -> &[u8] 
    {
        &*self
    }
}
impl AsMut<[u8]> for AncillaryBuf 
{
    fn as_mut(&mut self) -> &mut[u8] 
    {
        &mut*self
    }
}

/// One ancillary message produced by [`Ancillary`](#struct.Ancillary)
#[derive(Debug)]
pub enum AncillaryItem
{
    /// One or more file descriptors sent by the peer.
    ///
    /// Consumer of the iterator is responsible for closing them.
    Fds(Vec<OwnedFd>),

    /// Credentials of the sending process.
    #[allow(unused)]
    Credentials(ReceivedCredentials),

    //Timestamp(),
    //SecurityContext(&'a[u8]),
    /// An unknown or unsupported ancillary message type was received.
    ///
    /// It's up to you whether to ignore or treat as an error.
    Unsupported
}

impl AncillaryItem
{
    /// Creates a new [`FdSlice`] with the lifetime from a `unaligned_ptr` and a `len`.
    ///
    /// # Safety
    /// The unaligned_ptr does not need to be properly aligned, but it needs to point to at least `len` [`RawFd`]s.
    /// The unaligned_ptr may not be null.
    unsafe 
    fn new_fds(unaligned_ptr: *const RawFd, len: usize) -> Self 
    {
        debug_assert!(!unaligned_ptr.is_null(), "No NULL pointer for FdSlice");
        
        let owned_fd_list = 
            unsafe { slice::from_raw_parts(unaligned_ptr, len) }
                .into_iter()
                .map(|fd| unsafe{ OwnedFd::from_raw_fd(*fd)} )
                .collect::<Vec<OwnedFd>>();
        
        return Self::Fds(owned_fd_list);
    }
}

/// An iterator over ancillary messages received with `recv_ancillary()`.
#[derive(Debug)]
pub struct Ancillary<'a>
{
    // addr and bytes are not used here:
    // * addr is usually placed on the stack by the calling wrapper method,
    //   which means that its lifetime ends when this struct is returned.
    // * the iovec is incremented by Linux, but possibly not others.
    msg: msghdr,

    _ancillary_buf: PhantomData<&'a[u8]>,
    /// The next message, initialized with CMSG_FIRSTHDR()
    #[cfg(not(any(target_os="illumos", target_os="solaris")))]
    next_message: *mut cmsghdr,
}



impl<'a> Iterator for Ancillary<'a>
{
    type Item = AncillaryItem;

    #[cfg(not(any(target_os="illumos", target_os="solaris")))]
    fn next(&mut self) -> Option<AncillaryItem> 
    {
        unsafe 
        {
            use std::mem::MaybeUninit;

            if self.next_message.is_null() 
            {
                return None;
            }

            let msg_bytes = (*self.next_message).cmsg_len as usize;
            let payload_bytes = msg_bytes - CMSG_LEN(0) as usize;
            let msg = 
                if self.next_message.is_aligned() == false
                {
                    self.next_message.read_unaligned()
                }
                else
                {
                    self.next_message.read()
                };

            let item = 
                match (msg.cmsg_level, msg.cmsg_type) 
                {
                    (SOL_SOCKET, SCM_RIGHTS) => 
                    {
                        let num_fds = payload_bytes / mem::size_of::<RawFd>();
                        // pointer is aligned due to the cmsg header
                        let first_fd = CMSG_DATA(self.next_message) as *const c_void;
                        let first_fd = first_fd.cast::<RawFd>();
                        // consume onece the FD's
                        AncillaryItem::new_fds(first_fd, num_fds)
                    }
                    #[cfg(any(target_os="linux", target_os="android"))]
                    (SOL_SOCKET, SCM_CREDENTIALS) => 
                    {
                        let creds_ptr = CMSG_DATA(self.next_message) as *const c_void;

                        debug_assert!(
                            creds_ptr as usize & (mem::align_of::<RawReceivedCredentials>()-1) == 0,
                            "CMSG_DATA() is aligned"
                        );

                        let creds_ptr = creds_ptr as *const RawReceivedCredentials;

                        let creds = 
                            if creds_ptr.is_aligned() == false
                            {
                                creds_ptr.read_unaligned()
                            }
                            else
                            {
                                creds_ptr.read()
                            };

                        AncillaryItem::Credentials(ReceivedCredentials::from_raw(creds))
                    }
                    _ => 
                        AncillaryItem::Unsupported,
                };

            self.next_message = CMSG_NXTHDR(&mut self.msg, self.next_message);
            
            return Some(item);
        }
    }

    #[cfg(any(target_os="illumos", target_os="solaris"))]
    fn next(&mut self) -> Option<Self::Item> 
    {
        None
    }
}

impl<'a> Drop for Ancillary<'a>
{
    fn drop(&mut self) 
    {
        // close all remaining file descriptors
        for ancillary in self 
        {
            drop(ancillary);
        }
    }
}
impl<'a> Ancillary<'a>
{
    /// Returns `true` if the non-ancillary part of the datagram or packet was truncated.
    ///
    /// If the provided byte buffer(s) are shorter than the datagram or packet
    /// that was sent, the bytes that couldn't be stored are discarded.
    ///
    /// This function is not meaningful for streams.
    pub 
    fn message_truncated(&self) -> bool 
    {
        self.msg.msg_flags & MSG_TRUNC != 0
    }

    /// Returns `true` if ancillary messages were dropped due to a too short ancillary buffer.
    #[allow(unused)] // type is not yet exposed
    pub 
    fn ancillary_truncated(&self) -> bool 
    {
        self.msg.msg_flags & MSG_CTRUNC != 0
    }
}

/// A safe (but incomplete) wrapper around `recvmsg()`.
pub 
fn recv_ancillary<'ancillary_buf, FD: AsFd>(
    socket: FD,  
    from: Option<&mut UnixSocketAddr>,  
    mut flags: c_int,
    bufs: &mut[IoSliceMut],  
    ancillary_buf: &'ancillary_buf mut[u8],
) -> Result<(usize, Ancillary<'ancillary_buf>), io::Error> 
{
    unsafe 
    {
        let mut msg: msghdr = mem::zeroed();
        msg.msg_name = ptr::null_mut();
        msg.msg_namelen = 0;
        msg.msg_iov = bufs.as_mut_ptr() as *mut iovec;
        msg.msg_iovlen = 
            bufs.len().try_into()
                .map_err(|_|
                    io::Error::new(ErrorKind::InvalidInput, "too many content buffers")
                )?;

        msg.msg_flags = 0;
        msg.msg_control = ptr::null_mut();
        msg.msg_controllen = 0;

        if ancillary_buf.len() > 0 
        {
            #[cfg(any(target_os="illumos", target_os="solaris"))] 
            {
                return Err(io::Error::new(
                    ErrorKind::Other,
                    "ancillary message support is not implemented yet on Illumos or Solaris, sorry"
                ))
            }

            if ancillary_buf.as_ptr() as usize % mem::align_of::<cmsghdr>() != 0 
            {
                return Err(
                    io::Error::new(ErrorKind::InvalidInput, "ancillary buffer is not properly aligned")
                );
            }

            if ancillary_buf.len() > ControlLen::max_value() as usize 
            {
                return Err(
                    io::Error::new(ErrorKind::InvalidInput, "ancillary buffer is too big")
                );
            }

            msg.msg_control = ancillary_buf.as_mut_ptr() as *mut c_void;
            msg.msg_controllen = ancillary_buf.len() as ControlLen;
        }

        flags |= MSG_NOSIGNAL;
        #[cfg(not(any(target_vendor="apple", target_os="illumos", target_os="solaris", target_os = "haiku")))] 
        {
            flags |= MSG_CMSG_CLOEXEC;
        }

        let received = 
            match from 
            {
                Some(addrbuf) => 
                {
                    let (received, addr) = 
                        UnixSocketAddr::new_from_ffi(
                            |addr, len| 
                            {
                                msg.msg_name = addr as *mut sockaddr as *mut c_void;
                                msg.msg_namelen = *len;
                                let received = cvt_r!(recvmsg(socket.as_fd().as_raw_fd(), &mut msg, flags))? as usize;
                                *len = msg.msg_namelen;

                                Ok(received)
                            }
                        )?;

                    *addrbuf = addr;

                    received
                }
                None => 
                    cvt_r!( recvmsg(socket.as_fd().as_raw_fd(), &mut msg, flags) )? as usize
            };

        let ancillary_iterator = 
            Ancillary 
            {
                msg,
                _ancillary_buf: PhantomData,
                #[cfg(not(any(target_os="illumos", target_os="solaris")))]
                next_message: CMSG_FIRSTHDR(&msg),
            };

        return Ok((received, ancillary_iterator));
    }
}

pub 
fn recv_fds<FD: AsFd>(
    fd: FD,  
    from: Option<&mut UnixSocketAddr>,
    bufs: &mut[IoSliceMut],  
    mut fd_buf: Option<&mut Vec<OwnedFd>>
) -> Result<(usize, bool, usize), io::Error> 
{
    let mut ancillary_buf = 
        AncillaryBuf::with_fd_capacity(
            fd_buf.as_ref().map_or(0, |f| f.capacity())
        )?;    

    let (num_bytes, ancillary) = 
        recv_ancillary(fd, from, 0, bufs, &mut ancillary_buf)?;

    let msg_truc = ancillary.message_truncated();

    for message in ancillary 
    {
        if let AncillaryItem::Fds(fds) = message 
        {
            // Due to alignment of cmsg_len in glibc the minimum payload
            // capacity is on Linux (and probably Android) 8 bytes,
            // which means we might receive two file descriptors even though
            // we only want one.
            let (cap, len) = 
                fd_buf
                    .as_ref()
                    .map_or((0, 0), |f| (f.capacity(), f.len()));

            let can_keep = fds.len().min(cap - len);

            for (ofd, _) in fds.into_iter().zip(0..can_keep) 
            {
                #[cfg(any(target_vendor="apple", target_os="freebsd"))] 
                {
                    // set cloexec
                    // This is necessary on FreeBSD as MSG_CMSG_CLOEXEC
                    // appears to have no effect.
                    // FIXME this should be done in a separate iteration
                    // when the fds are received, and not after user code
                    // has had a chance to run.
                    // SAFETY: It's safe to create FdSlice twice from valid values. The values are valid.   
                    let _ = set_cloexec(&ofd, true);

                    
                }

                fd_buf.as_mut().unwrap().push( ofd );
            }

            // the rest of the OwnedFd will be dropped automatically
        }
    }
    
    return 
        Ok((num_bytes, msg_truc, fd_buf.as_ref().map_or(0, |f| f.len())));
}

/*
#[cfg(test)]
mod tests
{
    use std::{io::IoSliceMut, os::fd::{OwnedFd, RawFd}};

    use libc::getpid;

    use crate::{UnixSeqpacketConn, ancillary::{AncillaryBuf, AncillaryItem, recv_ancillary, send_ancillary}, credentials::SendCredentials};


    #[cfg_attr(
        any(
            target_os="linux", target_os="android",
            target_os="freebsd", target_os="dragonfly",
            target_os="openbsd", target_os="netbsd",
            target_os="illumos", target_os="solaris"
        ),
        test
    )]
    fn peer_credentials_of_seqpacket_pair2() {
        let (a, b) = UnixSeqpacketConn::pair().expect("create unix seqpacket pair");
        let (a2, b2) = UnixSeqpacketConn::pair().map(|(a, b)| (OwnedFd::from(a), OwnedFd::from(b))).expect("create stream socket pair");
        let creds = SendCredentials::Custom { pid: getpid(), uid: (), gid: () }

        send_ancillary(&a, None, 0, &[], vec![], Some(creds)).unwrap();

        let mut fd_buf: Vec<OwnedFd> = Vec::with_capacity(2);

        let mut ancillary_buf = 
            AncillaryBuf::with_fd_capacity(
                fd_buf.capacity()
            ).unwrap();    
        let mut slicebuf = vec![0u8; 64];
        let (num_bytes, ancillary) = 
            recv_ancillary(&b, None, 0, &mut[IoSliceMut::new(&mut slicebuf)], &mut ancillary_buf).unwrap();

        println!("ffff");

        for message in ancillary 
        {
            if let AncillaryItem::Fds(fds) = message 
            {
                println!("fd");
            }
            else if let AncillaryItem::Credentials(d) = message
            {
                println!("creds");
            }
        }
    }
}*/
