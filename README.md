[![pipeline](https://github.com/d-e-s-o/neovim-ctrl/actions/workflows/test.yml/badge.svg?branch=main)](https://github.com/d-e-s-o/neovim-ctrl/actions/workflows/test.yml)
[![crates.io](https://img.shields.io/crates/v/neovim-ctrl.svg)](https://crates.io/crates/neovim-ctrl)
[![rustc](https://img.shields.io/badge/rustc-1.74+-blue.svg)](https://blog.rust-lang.org/2023/11/16/Rust-1.74.0/)

neovim-ctrl
===========

- [Changelog](CHANGELOG.md)

**neovim-ctrl** is a program to find and interact with a Neovim instance
running in a particular terminal. It works with Neovim 0.9.0 and higher.

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
