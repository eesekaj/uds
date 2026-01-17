# uds

<img src="https://cdn.4neko.org/win_ev_log.webp" width="150"/>

> [!IMPORTANT]  
> I am not an original author. A (https://github.com/tormol/uds)[GitHub] (https://crates.io/crates/uds)[Crates] are links to original crate.

> [!IMPORTANT]  
> Since author is not responding on issues at his github page, I decided to fork the crate.

A unix domain sockets Rust library that supports abstract addresses, fd-passing, SOCK_SEQPACKET sockets and more.

When possible, features are implemented via extension traits for [`std::os::unix::net`](https://doc.rust-lang.org/std/os/unix/net/index.html) types (and optionally [mio](https://crates.io/crates/mio)'s uds types) instead of exposing new structs.
The only new socket structs this crate exposes are those for seqpacket sockets.

Ancillary credentials and timestamps are not yet supported.

## Example

(only runs sucessfully on Linux)

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

## Portability

macOS doesn't support SOCK_SEQPACKET sockets, and abstract socket addresses is Linux-only, so if you don't want to bother with supporting non-portable features you are probably better off only using what std or mio provides.
If you're writing a datagram server though, using std or mio means you can't respond to abstract adresses, forcing clients to use path addresses and deal with cleaning up the socket file after themselves.

Even when all operating systems you care about supports something, they might behave differently:  
On Linux file descriptors are cloned when they are sent, but macOS and the BSDs first clones them when they are received. This means that if a FD is closed before the peer receives it you have a problem.  
Also, some OSes might return the original file descriptor without cloning it if it's received within the same process as it was sent from. (DragonFly BSD, possibly macOS and maybe FreeBSD).

| | Linux | macOS | FreeBSD | OpenBSD | DragonFly BSD | NetBSD | Illumos |
|-|-|-|-|-|-|-|-|
| **Seqpacket** | Yes | N/A | Yes | Yes | Yes | Yes | N/A |
| **fd-passing** | Yes | Yes | Yes | Yes | Yes | Yes | No |
| **abstract addresses** | Yes | N/A | N/A | N/A | N/A | N/A | N/A |
| **Tested?** | Manually<sup>\*</sup> | Manually<sup>\*</sup> | Manually<sup>\*</sup> | Manually<sup>\*</sup> | Manually<sup>\*</sup> | Manually<sup>\*</sup> | Manually<sup>\*</sup> |

<sup>\*</sup>: Not tested since v0.2.6. (but (cross)checked on CI.)

### Other OSes

* Android: I haven't tested on it, but I assume there are no differences from regular Linux.
* Windows 10: While it added some unix socket features, Windows support is not a priority. (PRs are welcome though).
* Solaris: Treated identically as Illumos. mio 0.8 doesn't support it.


## Minimum Rust version

The minimum Rust version is 1.63.  
Older versions might work, but might break in a minor release.

## `unsafe` usage

This crate calls many C functions, which are all `unsafe` (even ones as simple as `socket()`).
The public interface is safe (except for `FromRawFd`), so if you find something unsound (even internal functions that aren't marked `unsafe`) please open an issue.

## License

<img src="https://cdn.4neko.org/mit_apache.webp" width="250"/>

Licensed under either of

* Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
