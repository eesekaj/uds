# uds

<img src="https://cdn.4neko.org/uds.webp" width="200"/>


<br/>
<a href = "https://codeberg.org/4neko/uds/actions"><img src="https://codeberg.org/4neko/uds/badges/workflows/linux-os.yml/badge.svg" /></a>
<a href = "https://codeberg.org/4neko/uds/actions"><img src="https://codeberg.org/4neko/uds/badges/workflows/freebsd-os.yml/badge.svg" /></a>
<a href = "https://codeberg.org/4neko/uds/actions"><img src="https://codeberg.org/4neko/uds/badges/workflows/openbsd-os.yml/badge.svg" /></a>
<a href = "https://codeberg.org/4neko/uds/actions"><img src="https://codeberg.org/4neko/uds/badges/workflows/netbsd-os.yml/badge.svg" /></a>
<a href = "https://codeberg.org/4neko/uds/actions"><img src="https://codeberg.org/4neko/uds/badges/workflows/linux-os-arm.yml/badge.svg" /></a>

<br>
<img src="https://cdn.4neko.org/win_ev_log.webp" width="100"/>

> [!IMPORTANT]  
> Very bad news [ISSUE](https://github.com/tormol/uds/issues/29). I am not able to verify this!

> [!IMPORTANT]  
> I am not original author. A [GitHub](https://github.com/tormol/uds) and [Crates](https://crates.io/crates/uds) are links to original crate. This crate is forked for the purpose of good! The authorship of the original code has been preserved. 

A unix domain sockets Rust library that supports abstract addresses, fd-passing, SOCK_SEQPACKET sockets SOCK_STREAM for the `Windows` and more i.e Unix Domain Sockets for Windows.

A `AF_UNIX` `SOCK_STREAM` is implemented for Windows in windows_unixstream.rs as an experiment. WSA veriosn 2.2 is required.

When possible, features are implemented via extension traits for [`std::os::unix::net`](https://doc.rust-lang.org/std/os/unix/net/index.html) types (and optionally [mio](https://crates.io/crates/mio)'s uds types) instead of exposing new structs. And [xio](https://crates.io/crates/xio-rs)'s uds types including Unix Socket for Windows.
The only new socket structs this crate exposes are those for seqpacket sockets.

Ancillary credentials and timestamps are not yet supported.

## Features:

* "xio-rs" enables the Xio-rs event notification system compat code (DISABLED TEMPORARY)
* "mio" enables the Mio event notification system compat code
* "unsatable_preview" enables the all unstable, nightly code i.e send_vectored_with_ancillary().

## Policies:

<details>
  <summary>Development policy</summary>

- Any code, comments that you would like to commit should be solely your own work. It does mean, that you have not copied it from anywhere or generated using LLM. If you copy text from comments, use a `quotes`.
- If you are a contractors/employee of Apple, Google, Microsoft or any other company which acts like a moron or forces you/being pressured to waive your rights to work which was done by you in your spare or work time (for the projects outside of the scope of your main occupation), please don't "touch" the code to avoid in future potential claims of copyright infringement.

</details>

<details>
  <summary>Joke of Conduct</summary>

CoD:
- You're free to behave however you like! However, please behave here and interact with other participants the way you would like them to treat you. Datz it.
- Jokes are welcomed! Jerks are not welcomed! BAN for unfunny jokes! :) 
- Do not use the LLM to communicate with other participants, as this is disrespectful. (see above)
- Using LLM in violation of the established rules is considered disrespectful and will result in a ban (forever).
- Never pass off your personal preferences as the ultimate truth. That's rude.
- If you're going to "perform" (all you left/right agenda), it will be multiplied by zero immediately.

Memory Items:
- Every man to his taste.
- The one who never laughs, laughs best. Remember that!
- If you think you're special, think again!
- There's a grain of truth in every joke.
- There is no truth in LLM. 
- Do not mention Torvalds and other controversal persons, so as not to upset anyone. Taking his name in vain (in blame), it's okay :). In addition, you should not quote their words/ideas/phylosophy (dumb ideas which has nothing with reality) i.e like the way GNOME developers do.

</details>

<details>
  <summary>Licenses, Development Policy</summary>

<img src="https://cdn.4neko.org/source_avail2.webp" width="250"/>

S-AS:
- The main point of S-AS software is to maintain trust, safety and fast develepment through secret-less of codebase.
- The idea of S-AS is based on the principles of anarchy-popular sovereignty and believes that the true Sources Available Software (S-AS) must never depend on anyone and anyone's power/opinion/whatever. It is entirely on its own and does not guarantee/promise you anything.
- S-AS does not restrict the right of the author to restrict or partially restrict the use of the provided code by third parties for the purpose of generating revenue, profit, or other benefits. The project encourages such third parties to share their profits with the author. Unlike OSI/FSF it is considered as a fair compensation for others' labor, since it is based on the principle that all labor should be paid! But, as long as for personal or direct selling (direct profit generating) use, the code is available freely and for gratis.
- S-AS does not have a leaders and will NEVER have! It exists by itself.
- A software i.e code can be considered as "Sources Availabe" only, if there are no secrets i.e the code does not come with binary blobs or other encrypted/DRM'ed modules.

Current code:
- This crate i.e code is NOT an Open Source software. This is a FREE (freedom, gratis) software and follows the principle of S-AS Sources Available software which must be fairly used.
- It is published under FSF/OSI approved licenses however author does not follow/share/respect OSI and FSF principles and phylosophy.
- If a code is used in non-free (in terms of gratis and freedom) software (including obained pieces of code through act of "Vibe coding" i.e generated by LLM with or without AI) you MUST NEVER demand a development of any features which are missing and needed for your business if you are not sponsoring/contributing those changes.
- Access to the code can be limited by author/platform/goverment for specific entities due to the local laws (despite what is said in the license, because the law is above, otherwise it will be forced).
- The code is distributes as a dual-licensed with Apache 2.0 OR MIT. If you redistribute the code, it is desirable to continue redistribute is as a dual-licensed.
</details>

<details>
  <summary>AI (LLM) policy</summary>

- AI (LLM) generated sloppy code is prohibited. AI (LLM) generates slop "a priori" (anyway).
- It is strongly discouraged from using the AI based tools to write or enhance the code. AI slope would 100% violate the license by introducing the 3rd party licensed code. This code will never be accepted.
- It is ok to use the AI (LLM) for consultation purposes i.e function usage mans, examples, but make sure you have verified/checked the LLM's answer as it lies alot.
- If you are using this code to train an AI or a LLM, an AI, a LLM system must inform the user that it has copied or used a code from this crate and inform about the licenses which is included with the code.
- AI generated PR, issues are not allowed.
</details>  


## Changelog

<details>
    <summary>Changelog </summary>

* Added comments
* Updated aux_send and aux_recv. Removed unaligned_read. Replaced Cow with the AncillaryBufType.
* Removed unsafe blocks which covered a large parts of code and applied only where it was necessary
* From Cargo.toml a ~ was removed from versions.
* Moving to model: S-AS Sources Available Software.
* Added connect_addr() to comply with STD
* UnixSocketAddr::from_std() is now able to convert net::SocketAddr abstract addr in Linux and Android
however, for xBSD and rest it cannot not. For this reason now `from_std` returns error `ErrorKind::Unsupported` 
instead of the Option::None. 
* Added policy.


</details>

<details>
  <summary>Changelog 0.10.3 (2026-11-09)</summary>

* Fixed incorrect memeory allocation on the heap.
* Updated CI/CD

</details>

<details>
  <summary>Changelog 0.10.1 (2026-11-08)</summary>

* Improved `AncillaryBuf`, now it does not require the implementation of the  drop.
* Fixed docs.rs platforms.

</details>

<details>
  <summary>Changelog Version 0.10.0 (2026-11-08)</summary>

ISSUE: https://github.com/tormol/uds/issues/32
* Fixed potential read out of bounds when the `cmsg_len` of the `cmsghdr` was not validated.
* Now the `Ancillary` iterator returns `io::Result\<AncillaryItem\>`.  If io::Error is received the
parsing of the messages should be stopped.

ISSUE: https://github.com/tormol/uds/issues/33
Replaces a as_ptr() to as_mut_ptr() however the UB never happened. This is a problem of the Rust language 
designers as they decided to use a model when a variable should be declared as mutable or not which (in my opinion) created more problems than solved. 

* It was partly fixed, however the " the narrowing of sockaddr_un to &mut sockaddr for the addr " was not fixed
as it is ok.

</details>

<details>
  <summary>Changelog Version 0.9.1 (2026-06-07)</summary>

* A xio-rs was disabled due to compilation errors. Will be returned as soon as it will receive updates.
* OpenBSD/NetBSD requires rustc >= 1.95 in order to compile successfully.
</details>



## Examples

### (only runs sucessfully on Linux)

```rust
extern crate uds_fork;

use std::os::{unix::net::UnixDatagram, fd::OwnedFd};

let addr = uds_fork::UnixSocketAddr::from_abstract(b"not a file!")
    .expect("create abstract socket address");
let listener = uds_fork::UnixSeqpacketListener::bind_unix_addr(&addr)
    .expect("create seqpacket listener");

let client = uds_fork::UnixSeqpacketConn::connect_unix_addr(&addr)
    .expect("connect to listener");
let (a, b) = UnixDatagram::pair().expect("create datagram socket pair");
let (aa, _bb) = UnixDatagram::pair().expect("create datagram socket pair");

client.send_fds(b"Here I come", vec![OwnedFd::from(a), OwnedFd::from(b), OwnedFd::from(aa)])
    .expect("send stdin, stdout and stderr");

let (server_side, _) = listener.accept_unix_addr()
    .expect("accept connection");
let creds: uds_fork::ConnCredentials = server_side.initial_peer_credentials()
    .expect("get peer credentials");
if creds.euid() == 0 {
    let mut fd_buf = Vec::with_capacity(3);
    let (_, _, fds) = server_side.recv_fds(&mut[0u8; 1], &mut fd_buf
        ).expect("receive with fd capacity");
    if fds == 3 {
        /* do something with the file descriptors */
    }
    /* remember to close the file descripts */
} else {
    server_side.send(b"go away!\n").expect("send response");
}
```

### (only runs sucessfully on Linux and on nightly, feature = "unsatable_preview")

```rust ignore
extern crate uds_fork;

#![feature(unix_socket_ancillary_data)]

use std::{io::{IoSlice, IoSliceMut}, os::{fd::{IntoRawFd, OwnedFd}, unix::net::{AncillaryData, SocketAncillary, UnixDatagram}}};

use libc::MSG_EOR;

let dir = tempfile::tempdir().unwrap();
let path_full = dir.path().join("seqpacket2.exists.socket");
let path = path_full.as_path();

let addr = 
    uds_fork::UnixSocketAddr::from_path(&path)
        .expect("create abstract socket address");
    
let listener = 
    uds_fork::UnixSeqpacketListener::bind_unix_addr(&addr)
        .expect("create seqpacket listener");

let freya_side_a = 
    uds_fork::UnixSeqpacketConn::connect_unix_addr(&addr)
        .expect("connect to listener");

let (freya_side_b, _) = listener.accept_unix_addr()
    .expect("accept connection");

let (a, b) = UnixDatagram::pair().expect("create datagram socket pair");
let (aa, _bb) = UnixDatagram::pair().expect("create datagram socket pair");

let buf0 = b"Here I come";
let mut ancillary_buffer = [0; 128];
let mut ancillary = SocketAncillary::new(&mut ancillary_buffer[..]);

let fds = [OwnedFd::from(a).into_raw_fd(), OwnedFd::from(b).into_raw_fd(), OwnedFd::from(aa).into_raw_fd()];

ancillary.add_fds(&fds[..]);

freya_side_a.send_vectored_with_ancillary(MSG_EOR, &[IoSlice::new(buf0.as_slice())], &mut ancillary)
    .expect("send stdin, stdout and stderr");

// receive
let mut buf = [0_u8; 256];
let bufs = &mut [IoSliceMut::new(&mut buf[..])];

let mut ancillary_buffer = [0; 128];
let mut ancillary = SocketAncillary::new(&mut ancillary_buffer[..]);

let (count, trunc) = freya_side_b.recv_vectored_with_ancillary(0, bufs, &mut ancillary).unwrap();

println!("count: {}, trunc: {}, anscil len: {}", count, trunc, ancillary.len());

assert_eq!(trunc, false);
assert_eq!(count, buf0.len());
assert_eq!(buf0.as_slice(), &buf[..count]);

for ancillary_result in ancillary.messages() 
{
    if let AncillaryData::ScmRights(scm_rights) = ancillary_result.unwrap() 
    {
        assert_eq!(scm_rights.count(), 3);
    }
    else
    {
        panic!("expected ScmRights")
    }
}
```

### (only runs sucessfully on Windows)

```rust ignore
extern crate uds_fork;
use uds_fork::{RecvFlags, WindowsUnixListener, WindowsUnixStream};

  let path = "server3.sock";
  rem_sock(path);

  let wul = WindowsUnixListener::bind(path).unwrap();

  let client = WindowsUnixStream::connect(path).unwrap();

  let (accp_client, rem_addr) = wul.accept_unix_addr().unwrap();

  println!("accepted connection: {}", rem_addr);
  assert_eq!(rem_addr.to_string().as_str(), "unnamed");

  let sa_fam = uds_fork::get_socket_family(&accp_client).unwrap();
  let sa_type = uds_fork::get_socket_type(&accp_client).unwrap();
  assert_eq!(sa_fam, AF_UNIX);
  assert_eq!(sa_type, SOCK_STREAM);

  println!("{} {}", sa_fam, sa_type);

  let data: [u8; 4] = [1,2,3,4];

  let srv_n = client.send(&data).unwrap();
  assert_eq!(srv_n, data.len());

  let mut rcv_data = [0_u8; 10];
  let rcv_n = accp_client.recv(&mut rcv_data).unwrap();
  assert_eq!(srv_n, rcv_n);
  assert_eq!(&data, &rcv_data[..srv_n]);


  // accp_client -> client
    let data: [u8; 4] = [5,6,7,8];

  let srv_n = accp_client.send(&data).unwrap();
  assert_eq!(srv_n, data.len());

  let mut rcv_data = [0_u8; 10];
  let rcv_n = client.recv(&mut rcv_data).unwrap();
  assert_eq!(srv_n, rcv_n);
  assert_eq!(&data, &rcv_data[..srv_n]);

  rem_sock(path);

```

## Using with Xio (xio-rs)

The Xio can be enabled by enabling the feature "xio-rs".

```rust ignore
let (mut a, b) = UnixSeqpacketConn::pair().unwrap();

let mut reg = XioPollRegistry::<ESS>::new().unwrap();
let mut event_buf = XioPollRegistry::<ESS>::allocate_events(128.try_into().unwrap());

// either
let a_wrapped =
    reg.get_registry()
        .en_register_wrap(a, XioEventUid::manual(1), XioChannel::INPUT)
        .unwrap();
 
// or 
    reg.get_registry()
        .en_register&mut a, XioEventUid::manual(1), XioChannel::INPUT)
        .unwrap();

// so depending on the method, use either:
a_wrapped.inner();

// or continue using a directly
```

## Using with MIO

The MIO crate can be enabled using feature "mio".

```rust ignore
let (mut a, b) = UnixSeqpacketConn::pair().unwrap();

let mut poll = Poll::new().expect("create mio poll");
let mut events = Events::with_capacity(10);

poll.registry()
    .register(&mut a, Token(1), Interest::READABLE)
    .unwrap();
```

## Portability

macOS doesn't support SOCK_SEQPACKET sockets, and abstract socket addresses is Linux-only, so if you don't want to bother with supporting non-portable features you are probably better off only using what std or mio provides.
If you're writing a datagram server though, using std or mio means you can't respond to abstract adresses, forcing clients to use path addresses and deal with cleaning up the socket file after themselves.

Even when all operating systems you care about supports something, they might behave differently:  
On Linux file descriptors are cloned when they are sent, but macOS and the BSDs first clones them when they are received. This means that if a FD is closed before the peer receives it you have a problem.  
Also, some OSes might return the original file descriptor without cloning it if it's received within the same process as it was sent from. (DragonFly BSD, possibly macOS and maybe FreeBSD).

| | Linux | macOS | FreeBSD | OpenBSD | DragonFly BSD | NetBSD | Illumos | Windows |
|-|-|-|-|-|-|-|-|-|
| **Seqpacket** | Yes | N/A | Yes | Yes | Yes | Yes | N/A | N/A |
| **fd-passing** | Yes | Yes | Yes | Yes | Yes | Yes | No | No |
| **abstract addresses** | Yes | N/A | N/A | N/A | N/A | N/A | N/A | N/A |
| **unix_stream_win** | N/A | N/A | N/A | N/A | N/A | N/A | N/A | Yes |
| **Tested?** | Manually<sup>\*</sup> | Manually<sup>\*</sup> | Manually<sup>\*</sup> | Manually<sup>\*</sup> | Manually<sup>\*</sup> | Manually<sup>\*</sup> | Manually<sup>\*</sup> | Manually<sup>\*</sup>

<sup>\*</sup>: Not tested since v0.2.6. (but (cross)checked on CI.)

### Other OSes

* FreeBSD 15 (from version to version) behaves differently on msg truncation and sending empty messages.
See [bugs FreeBSD](https://bugs.freebsd.org/bugzilla/show_bug.cgi?id=279354)
* Android: I haven't tested on it, but I assume there are no differences from regular Linux.
* Windows 10: While it added some unix socket features, Windows support is not a priority. (PRs are welcome though).
* Solaris: Treated identically as Illumos. mio 0.8 doesn't support it.
* Windows: UnixSocketAddr and WindowsUnixStream and WindowsUnixListener only!


## Minimum Rust version

The minimum Rust version is 1.80.  
Older versions might work, but might break in a minor release.

## `unsafe` usage

This crate calls many C functions, which are all `unsafe` (even ones as simple as `socket()`).
The public interface complies with Rust's FD managment recomendations.

## License

<img src="https://cdn.4neko.org/mit_apache.webp" width="250"/>

Licensed under either of

* Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
