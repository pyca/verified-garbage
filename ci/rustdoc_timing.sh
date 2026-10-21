#!/usr/bin/env bash
# rustdoc also gates the unstable libtest arguments passed by Cargo.
export RUSTC_BOOTSTRAP=1
exec rustdoc "$@"
