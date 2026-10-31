# Source after restoring the build cache and configuring any cross/SDE runner.
# Only libtest needs bootstrap for --report-time. Giving it to Cargo would
# invalidate proc-macro2's build-script fingerprint and rebuild its dependents.
vg_test_target=${CARGO_BUILD_TARGET:-$(rustc -vV | sed -n 's/^host: //p')}
vg_test_runner=CARGO_TARGET_$(printf '%s' "$vg_test_target" | tr '[:lower:]-' '[:upper:]_')_RUNNER
export "$vg_test_runner=env RUSTC_BOOTSTRAP=1 ${!vg_test_runner-}"
unset vg_test_target vg_test_runner
# Cargo passes the same unstable test arguments to rustdoc. Scope bootstrap
# to rustdoc as well, so it never reaches dependency builds or their scripts.
if [ "${OS-}" = Windows_NT ]; then
  export RUSTDOC="$(cygpath -w "$PWD/ci/rustdoc_timing.cmd")"
else
  export RUSTDOC="$PWD/ci/rustdoc_timing.sh"
fi
# Hides durations that round to zero at libtest's millisecond precision, from
# a test run piped through it, streaming each line to the log as it comes:
# sed buffers its output to a pipe until it exits (only GNU's has -u), and
# mawk, Debian's awk, buffers its input even with fflush(). Perl is on every
# runner (Debian's essential perl-base, Git Bash's, macOS's).
vg_hide_zero_times() {
  perl -pe 'BEGIN { $| = 1 } s/ <0\.000s>//g'
}
