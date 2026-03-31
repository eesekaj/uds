# uds

<img src="https://cdn.4neko.org/win_ev_log.webp" width="150"/>

> [!IMPORTANT]  
> Very bad news [ISSUE](https://github.com/tormol/uds/issues/29). I am not able to verify this!

> [!IMPORTANT]  
> I am not original author. A [GitHub](https://github.com/tormol/uds) and [Crates](https://crates.io/crates/uds) are links to original crate. This crate is forked!


A unix domain sockets Rust library that supports abstract addresses, fd-passing, SOCK_SEQPACKET sockets SOCK_STREAM for the `Windows` and more i.e Unix Domain Sockets for Windows.

A `AF_UNIX` `SOCK_STREAM` is implemented for Windows in windows_unixstream.rs as an experiment. WSA veriosn 2.2 is required.

When possible, features are implemented via extension traits for [`std::os::unix::net`](https://doc.rust-lang.org/std/os/unix/net/index.html) types (and optionally [mio](https://crates.io/crates/mio)'s uds types) instead of exposing new structs. And [xio](https://crates.io/crates/xio-rs)'s uds types including Unix Socket for Windows.
The only new socket structs this crate exposes are those for seqpacket sockets.

Ancillary credentials and timestamps are not yet supported.

## Features:

* "xio-rs" enables the Xio-rs event notification system compat code
* "mio" enables the Mio event notification system compat code

## Changelog


<details>
  <summary>Changelog </summary>

* (fixed) Cargo.toml docs.rs(<--- crap crap crap) wrong docs targets.

</details>


<details>
  <summary>Changelog Version 0.7.5 (2026-03-31)</summary>

* (fixed) Cargo.toml docs.rs(<--- crap) wrong docs targets.

</details>

<details>
  <summary>Changelog Version 0.7.4 (2026-03-31) </summary>

* (fixed) in the `addr.rs` a  `from_sockaddr_storage` a new_unspecified() is returned when `len < path_offset()`.
* ? add a windows as a target, so it will appear in the docs

</details>

<details>
  <summary>Changelog Version 0.7.3 (2026-03-26) </summary>

* Fixed a potential memory unligned access at send_ancillary() and recv_ancillary part in ancilliary.rs
* Added temp dir in tests to avoid leaving the sockets.

</details>

<details>
  <summary>Changelog Version 0.7.2 (2026-03-24)</summary>

* Fixed docs.rs wrong crate name feature

</details>

<details>
  <summary>Changelog Version 0.7.1 (2026-03-21) </summary>

* Hotfix: Cargo.toml default features. Removed default items.
* Updated Cargo.toml versions of the deps.
* Added 'Incoming' iterator for `UnixSeqpacketListener`
* Added 'Incoming' iterator for `WindowsUnixListener`.
* Added additional functionality including socket pair for `WindowsUnixSocket`.

</details>

<details>
  <summary>Changelog Version 0.7.0 (2026-03-21) </summary>

* A xio was added to the crate.
* A mio was returned to the crate.

</details>

<details>
  <summary>Changelog Version 0.6.1 (2026-02-04)</summary>

* Fixed release date of previous version
* Added more info and comments.

</details>

<details>
  <summary>Changelog Version 0.6.0 (2026-01-17)</summary>

* The crate's `addr.rs` is used as dependancy, so this crate can be used on Windows to utilize the `UnixSocketAddr`.
* Added experimental support for unixstream in Windows i.e AF_UNIX SOCK_STREAM.

</details>

<details>
  <summary>Changelog Version 0.5.4 (2026-01-26)</summary>

* Added missing implementation of `Deref` for `NonblockingUnixSeqpacketListener`.
* Fixed `address already in use` problems in docs.

</details>

<details>
  <summary>Changelog Version 0.5.3 (2026-01-25)</summary>

* Added from OwnedFd and from RawFd and from Self to OwnedFd. Functions which performs conversion from OwnedFd to Self perform check of the socket type.
* `NonblockingUnixSeqpacketListener` and `NonblockingUnixSeqpacketConn` is now have inside an instance of `UnixSeqpacketConn` and `UnixSeqpacketListener` respectivly which is set to non-blocking.
* Reorganised some functions

</details>

<details>
  <summary>Changelog Version 0.5.2 (2026-01-21)</summary>

* Fixed compilation errors on OpenBSD
* Fixed one test problem (related to what kernel returns)

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
* Android: I haven't tested on it, but I assume there are no differences from regular Linux.
* Windows 10: While it added some unix socket features, Windows support is not a priority. (PRs are welcome though).
* Solaris: Treated identically as Illumos. mio 0.8 doesn't support it.
* Windows: UnixSocketAddr and WindowsUnixStream and WindowsUnixListener only!


## Minimum Rust version

The minimum Rust version is 1.63.  
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
