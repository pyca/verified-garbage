# The Linux userspaces CI runs its 32-bit and PPC64LE jobs and its
# lints in, built by .github/workflows/runner-images.yml, each natively on a
# 64-bit runner:
# * linux/386 (i686), on an x86-64 runner: x86's tests, natively;
# * linux/arm64 (armv7-cross), on an ARM64 runner: ARMv7's and Thumb's tests,
#   cross-compiled for armhf and run by ci/arm32-run, natively when the CPU
#   has AArch32 and under QEMU when it doesn't (as some runners' cores have
#   none, and can start no 32-bit container at all), and ARMv7's
#   benchmarks, cross-compiled and run natively;
# * linux/ppc64le (ppc64le), on a ppc64le runner: PPC64LE's tests, natively;
# * linux/amd64 (lint), on an x86-64 runner: rustfmt and Clippy for every
#   target the other jobs build (`rust-lint`, ci/rust_lint.py), with each
#   Linux target's C cross compiler and OpenSSL, which the benchmarks' build
#   scripts compile and read.
ARG TARGETARCH
ARG TARGETVARIANT

FROM debian:trixie-slim AS base

# Increment this to blow away the docker cache
ENV CACHE_BUSTER=1

# This is needed because otherwise `sys.getfilesystemencoding()` returns
# "ANSI_X3.4-1968".
ENV LANG=C.UTF-8

# Docker overlay filesystems can reject directory renames during toolchain
# updates with EXDEV. Allow rustup to copy the files in that case.
ENV RUSTUP_PERMIT_COPY_RENAME=1

# Don't unpack things nothing in CI uses: static OpenSSL and glibc (rustc
# links dynamically; libc_nonshared.a, which libc.so names, stays), gcc's LTO
# backend, and the sanitizer runtimes (hard deps of libgcc-dev).
RUN printf '%s\n' \
    'path-exclude=/usr/lib/*/libcrypto.a' \
    'path-exclude=/usr/lib/*/libssl.a' \
    'path-exclude=/usr/lib/*/libc.a' \
    'path-exclude=/usr/lib/*/libm.a' \
    'path-exclude=/usr/libexec/gcc/*/*/lto1' \
    'path-exclude=/usr/libexec/gcc-cross/*/*/lto1' \
    'path-exclude=/usr/bin/*-lto-dump-*' \
    'path-exclude=/usr/lib/*/libasan*' \
    'path-exclude=/usr/lib/*/libhwasan*' \
    'path-exclude=/usr/lib/*/liblsan*' \
    'path-exclude=/usr/lib/*/libtsan*' \
    'path-exclude=/usr/lib/*/libubsan*' \
    'path-exclude=/usr/lib/gcc/*/*/libasan*' \
    'path-exclude=/usr/lib/gcc/*/*/libhwasan*' \
    'path-exclude=/usr/lib/gcc/*/*/liblsan*' \
    'path-exclude=/usr/lib/gcc/*/*/libtsan*' \
    'path-exclude=/usr/lib/gcc/*/*/libubsan*' \
    > /etc/dpkg/dpkg.cfg.d/excludes-unused-dev-files

# Only what the jobs use:
# * in the 32-bit image, the runner's (64-bit) libc and libstdc++, so that
#   the Node binary GitHub Actions injects into the container for JS actions
#   can run;
# * in armv7-cross, the armhf cross-compiler, libc and OpenSSL, and qemu-arm
#   (see ci/arm32-run);
# * in lint, the cross-compiler, libc and OpenSSL of each other Linux
#   target's architecture;
# * gcc and libc6-dev, rustc's linker and the benchmarks' C build scripts
#   (with binutils' readelf);
# * git and ca-certificates, for actions/checkout;
# * python3, for the coverage export and the benchmark comparison;
# * zstd, for actions/cache (through Swatinem/rust-cache);
# * openssl, with which the benchmarks record OpenSSL's version (and which
#   ca-certificates depends on);
# * libssl-dev and pkg-config, for the benchmarks, which link OpenSSL
#   (rust-openssl).
RUN case "$(dpkg --print-architecture)" in \
        i386) foreign=amd64; packages="libc6:amd64 libstdc++6:amd64" ;; \
        arm64) foreign=armhf; packages="gcc-arm-linux-gnueabihf libc6-dev:armhf libssl-dev:armhf qemu-user" ;; \
        ppc64el) foreign=; packages= ;; \
        amd64) foreign="i386 arm64 armhf ppc64el riscv64"; \
            packages="gcc-i686-linux-gnu gcc-aarch64-linux-gnu gcc-arm-linux-gnueabihf gcc-powerpc64le-linux-gnu gcc-riscv64-linux-gnu"; \
            for a in $foreign; do packages="$packages libc6-dev:$a libssl-dev:$a"; done ;; \
        *) echo "unsupported architecture: $(dpkg --print-architecture)" >&2; exit 1 ;; \
    esac && \
    for a in $foreign; do dpkg --add-architecture "$a"; done && \
    apt-get -qq update && apt-get install -qq -y --no-install-recommends \
        $packages \
        gcc \
        libc6-dev \
        git \
        ca-certificates \
        python3 \
        openssl \
        libssl-dev \
        pkg-config \
        zstd && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists

# A complete, unstripped toolchain in a fixed home (the jobs' HOME is
# /github/home), so that the jobs' `rustup toolchain install` can update it
# in place. The host is the userspace's, not the kernel's, and the stable
# toolchain has every component and target the jobs install, so that they
# download nothing until stable changes. Deduplicate libLLVM and strip the
# big binaries (with llvm-strip; GNU strip breaks them), as the other runner
# images do. Of llvm-tools, CI runs only llvm-cov and llvm-profdata, and
# rustc links with the C compiler, but for x86-64 Linux, the lint image's
# host, with rust-lld (through gcc-ld/ld.lld): empty the others, which were
# half of the compressed image. Keep all files recorded in rustup's
# component manifests, though: deleting even unused files prevents rustup
# from uninstalling or updating the toolchain. Empty, too, the toolchain's
# documentation and the shared libraries in its lib/ but rustc's own
# (librustc_driver, libLLVM): rustc's proc macros, which only building rustc
# loads. Only the lint image needs clippy and rustfmt.
ENV RUSTUP_HOME=/usr/local/rustup \
    CARGO_HOME=/usr/local/cargo \
    PATH=/usr/local/cargo/bin:$PATH
RUN components=llvm-tools && \
    case "$(dpkg --print-architecture)" in \
        i386) host=i686-unknown-linux-gnu; targets= ;; \
        arm64) host=aarch64-unknown-linux-gnu; targets=armv7-unknown-linux-gnueabihf,thumbv7neon-unknown-linux-gnueabihf ;; \
        ppc64el) host=powerpc64le-unknown-linux-gnu; targets= ;; \
        amd64) host=x86_64-unknown-linux-gnu; components=clippy,rustfmt,llvm-tools; \
            targets=i686-unknown-linux-gnu,aarch64-unknown-linux-gnu,armv7-unknown-linux-gnueabihf,thumbv7neon-unknown-linux-gnueabihf,powerpc64le-unknown-linux-gnu,riscv64gc-unknown-linux-gnu,aarch64-apple-darwin,x86_64-pc-windows-msvc ;; \
    esac && \
    url="https://static.rust-lang.org/rustup/dist/$host/rustup-init" && \
    python3 -c 'import sys, urllib.request; urllib.request.urlretrieve(sys.argv[1], sys.argv[2])' "$url" /tmp/rustup-init && \
    python3 -c 'import sys, urllib.request; sys.stdout.write(urllib.request.urlopen(sys.argv[1]).read().decode().split()[0] + "  /tmp/rustup-init\n")' "$url.sha256" | sha256sum -c - && \
    chmod +x /tmp/rustup-init && \
    /tmp/rustup-init -y --no-modify-path --profile minimal --default-host "$host" \
        --default-toolchain stable --component "$components" \
        ${targets:+--target "$targets"} && \
    rm /tmp/rustup-init && \
    sysroot="$(rustc --print sysroot)" && \
    cd "$sysroot/lib/rustlib/$host" && \
    for lib in lib/libLLVM*; do \
        if [ ! -L "$lib" ] && cmp -s "$lib" "$sysroot/lib/${lib#lib/}"; then \
            ln -sf "../../../${lib#lib/}" "$lib"; \
        fi; \
    done && \
    for f in "$sysroot/bin/cargo" "$sysroot/bin/rustc" \
             "$sysroot/bin/clippy-driver" "$sysroot/bin/cargo-clippy" \
             "$sysroot/bin/rustfmt" "$sysroot/bin/cargo-fmt" \
             "$sysroot"/lib/librustc_driver-*.so "$sysroot"/lib/libLLVM.so.* \
             "$CARGO_HOME/bin/rustup" \
             bin/rust-lld bin/llvm-cov bin/llvm-profdata; do \
        if [ -f "$f" ]; then bin/llvm-strip --strip-all "$f"; fi; \
    done && \
    for f in bin/*; do \
        case "${f#bin/}" in \
            llvm-cov|llvm-profdata) ;; \
            rust-lld) if [ "$host" != x86_64-unknown-linux-gnu ]; then : > "$f"; fi ;; \
            *) if [ -f "$f" ]; then : > "$f"; fi ;; \
        esac; \
    done && \
    for f in "$sysroot"/share/doc/rust/* "$sysroot"/lib/lib*.so; do \
        case "${f##*/}" in \
            librustc_driver-*|libLLVM*) ;; \
            *) if [ -f "$f" ]; then : > "$f"; fi ;; \
        esac; \
    done && \
    rustc -vV && cargo -V

# Each platform's image is the stage named after it (by BuildKit's
# TARGETARCH and TARGETVARIANT): armv7-cross's Cargo builds for ARMv7 unless
# told otherwise (the Thumb job sets CARGO_BUILD_TARGET), links with the
# cross-compiler, and runs the 32-bit programs through ci/arm32-run;
# pkg-config finds the armhf OpenSSL for openssl-sys (the benchmarks). In
# lint, pkg-config finds each Linux target's OpenSSL, for openssl-sys's
# build script, which only reads its headers there: Clippy links nothing.
FROM base AS image-386
FROM base AS image-ppc64le
FROM base AS image-arm64
COPY arm32-run /usr/local/bin/arm32-run
ENV CARGO_BUILD_TARGET=armv7-unknown-linux-gnueabihf \
    CARGO_TARGET_ARMV7_UNKNOWN_LINUX_GNUEABIHF_LINKER=arm-linux-gnueabihf-gcc \
    CARGO_TARGET_ARMV7_UNKNOWN_LINUX_GNUEABIHF_RUNNER=/usr/local/bin/arm32-run \
    CARGO_TARGET_THUMBV7NEON_UNKNOWN_LINUX_GNUEABIHF_LINKER=arm-linux-gnueabihf-gcc \
    CARGO_TARGET_THUMBV7NEON_UNKNOWN_LINUX_GNUEABIHF_RUNNER=/usr/local/bin/arm32-run \
    PKG_CONFIG_ALLOW_CROSS=1 \
    PKG_CONFIG_LIBDIR_armv7_unknown_linux_gnueabihf=/usr/lib/arm-linux-gnueabihf/pkgconfig:/usr/share/pkgconfig
FROM base AS image-amd64
ENV PKG_CONFIG_ALLOW_CROSS=1 \
    PKG_CONFIG_LIBDIR_i686_unknown_linux_gnu=/usr/lib/i386-linux-gnu/pkgconfig:/usr/share/pkgconfig \
    PKG_CONFIG_LIBDIR_aarch64_unknown_linux_gnu=/usr/lib/aarch64-linux-gnu/pkgconfig:/usr/share/pkgconfig \
    PKG_CONFIG_LIBDIR_armv7_unknown_linux_gnueabihf=/usr/lib/arm-linux-gnueabihf/pkgconfig:/usr/share/pkgconfig \
    PKG_CONFIG_LIBDIR_powerpc64le_unknown_linux_gnu=/usr/lib/powerpc64le-linux-gnu/pkgconfig:/usr/share/pkgconfig \
    PKG_CONFIG_LIBDIR_riscv64gc_unknown_linux_gnu=/usr/lib/riscv64-linux-gnu/pkgconfig:/usr/share/pkgconfig

FROM image-${TARGETARCH}${TARGETVARIANT}
