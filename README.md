[![pipeline](https://gitlab.com/d-e-s-o/neovim-ctrl/badges/master/pipeline.svg)](https://gitlab.com/d-e-s-o/neovim-ctrl/commits/master)
[![crates.io](https://img.shields.io/crates/v/neovim-ctrl.svg)](https://crates.io/crates/neovim-ctrl)
[![rustc](https://img.shields.io/badge/rustc-1.36+-blue.svg)](https://blog.rust-lang.org/2019/07/04/Rust-1.36.0.html)

neovim-ctrl
===========

- [Changelog](CHANGELOG.md)

**neovim-ctrl** is a program to find and interact with a Neovim instance
running in a particular terminal.

The program supports two commands:
- `find-socket` to discover the Unix domain socket of a running Neovim
- `change-window` to change the currently selected window/split based on
  a key sequence


Usage
-----

The program requires the TTY for which to find the (first) running
Neovim process the first argument.

```bash
# Find the path to the Unix domain socket for a nvim process on TTY
# /dev/pts/3:
$ nvim-ctrl find-socket /dev/pts/3
> /tmp/nvimfMfu99/0
```

```bash
# Send Ctrl-w-h to the Neovim on /dev/pts/7:
$ ctrlw=$(echo -n -e "\\x17")
$ nvim-ctrl change-window /dev/pts/7 "${ctrlw}h"
# Exit code 0 indicates that the window was actually changed.
$ echo $?
> 0

$ nvim-ctrl change-window /dev/pts/7 "${ctrlw}h"
> Error: nothing changed
# Exit code 1 means that no change happened.
$ echo $?
> 1
```
