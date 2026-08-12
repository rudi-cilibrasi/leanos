# syntax=docker/dockerfile:1.7@sha256:a57df69d0ea827fb7266491f2813635de6f17269be881f696fbfdf2d83dda33e

FROM docker.io/emscripten/emsdk:3.1.50@sha256:b6ea0e55fdc95be36427df6df7892d5e5e27f0440cfcf442a55f784aba09a4fa

SHELL ["/bin/bash", "-euo", "pipefail", "-c"]

ARG ZLIB_URL=https://github.com/madler/zlib/releases/download/v1.3.1/zlib-1.3.1.tar.xz
ARG ZLIB_SHA256=38ef96b8dfe510d42707d9c781877914792541133e1870841463bfa73f883e32
ARG LIBFFI_URL=https://github.com/libffi/libffi/archive/adbcf2b247696dde2667ab552cb93e0c79455c84.tar.gz
ARG LIBFFI_SHA256=1f5e7a1231b6cb9f747189c48b15bbf17afdda6e2f9684b386fd19e9bbe78649
ARG GLIB_URL=https://download.gnome.org/sources/glib/2.75/glib-2.75.0.tar.xz
ARG GLIB_SHA256=6dde8e55cc4a2c83d96797120b08bcffb5f645b2e212164ae22d63c40e0e6360
ARG PCRE2_URL=https://github.com/PhilipHazel/pcre2/releases/download/pcre2-10.40/pcre2-10.40.tar.bz2
ARG PCRE2_SHA256=14e4b83c4783933dc17e964318e6324f7cae1bc75d8f3c79bc6969f00c159d68
ARG PCRE2_PATCH_URL=https://wrapdb.mesonbuild.com/v2/pcre2_10.40-3/get_patch
ARG PCRE2_PATCH_SHA256=95391923529b4c1647a2cf88cd3b59cceb4f92393775e011f530e7865de0c7fb
ARG PIXMAN_URL=https://gitlab.freedesktop.org/pixman/pixman/-/archive/pixman-0.42.2/pixman-pixman-0.42.2.tar.gz
ARG PIXMAN_SHA256=4191a5084bae000a61e3513b06027b6f8f559d17d61769ed9de27dfb0cec8699
ARG MESON_URL=https://files.pythonhosted.org/packages/d6/97/852cc27c460d5fae07c6d7e4a2744f5684760358de3456b5ee9f130b8f57/meson-1.5.0.tar.gz
ARG MESON_SHA256=45d7b8653c1e5139df35b33be2dd5b2d040c5b2c6129f9a7c890d507e33312b8
ARG XTERM_PTY_URL=https://registry.npmjs.org/xterm-pty/-/xterm-pty-0.10.1.tgz
ARG XTERM_PTY_SHA256=ca1c31fd4c9ab1506c0e6619ee358d4260775b7045f10a5631b36f0ba9a8434a
ARG UBUNTU_SNAPSHOT_URL=https://snapshot.ubuntu.com/ubuntu
ARG UBUNTU_SNAPSHOT=20260206T000000Z

ENV TARGET=/build/target
ENV CHOST=wasm32-unknown-linux
ENV CFLAGS="-O2 -matomics -mbulk-memory -DNDEBUG -sWASM_BIGINT -DWASM_BIGINT -pthread -sMALLOC=mimalloc -sASYNCIFY=1"
ENV CXXFLAGS="${CFLAGS}"
ENV LDFLAGS="-L/build/target/lib -O2"
ENV CPATH=/build/target/include
ENV PKG_CONFIG_PATH=/build/target/lib/pkgconfig
ENV EM_PKG_CONFIG_PATH=/build/target/lib/pkgconfig

RUN rm -f /etc/apt/sources.list.d/*.list /etc/apt/sources.list.d/*.sources \
 && printf '%s\n' \
      "deb ${UBUNTU_SNAPSHOT_URL}/${UBUNTU_SNAPSHOT}/ jammy main universe" \
      "deb ${UBUNTU_SNAPSHOT_URL}/${UBUNTU_SNAPSHOT}/ jammy-updates main universe" \
      "deb ${UBUNTU_SNAPSHOT_URL}/${UBUNTU_SNAPSHOT}/ jammy-security main universe" \
      > /etc/apt/sources.list \
 && apt-get -o Acquire::Check-Valid-Until=false update \
 && apt-get install -y --no-install-recommends \
      autoconf=2.71-2 \
      automake=1:1.16.5-1.3 \
      libglib2.0-dev=2.72.4-0ubuntu2.9 \
      libltdl-dev=2.4.6-15build2 \
      libtool=2.4.6-15build2 \
      ninja-build=1.10.1-1 \
      pkgconf=1.8.0-1 \
 && rm -rf /var/lib/apt/lists/*

RUN mkdir -p /build/downloads "$TARGET" \
 && curl --fail --location --proto '=https' "$MESON_URL" -o /build/downloads/meson.tar.gz \
 && printf '%s  %s\n' "$MESON_SHA256" /build/downloads/meson.tar.gz | sha256sum --check --strict \
 && python3 -m pip install --no-deps --no-build-isolation /build/downloads/meson.tar.gz

RUN curl --fail --location --proto '=https' "$ZLIB_URL" -o /build/downloads/zlib.tar.xz \
 && printf '%s  %s\n' "$ZLIB_SHA256" /build/downloads/zlib.tar.xz | sha256sum --check --strict \
 && mkdir /build/zlib \
 && tar -xJf /build/downloads/zlib.tar.xz -C /build/zlib --strip-components=1 \
 && cd /build/zlib \
 && emconfigure ./configure --prefix="$TARGET" --static \
 && emmake make -j1 install

RUN curl --fail --location --proto '=https' "$LIBFFI_URL" -o /build/downloads/libffi.tar.gz \
 && printf '%s  %s\n' "$LIBFFI_SHA256" /build/downloads/libffi.tar.gz | sha256sum --check --strict \
 && mkdir /build/libffi \
 && tar -xzf /build/downloads/libffi.tar.gz -C /build/libffi --strip-components=1 \
 && cd /build/libffi \
 && autoreconf -fiv \
 && export LDFLAGS="$LDFLAGS -sEXPORTED_RUNTIME_METHODS=getTempRet0,setTempRet0" \
 && emconfigure ./configure --host="$CHOST" --prefix="$TARGET" \
      --enable-static --disable-shared --disable-dependency-tracking \
      --disable-builddir --disable-multi-os-directory --disable-raw-api \
      --disable-structs --disable-docs \
 && emmake make -j1 install SUBDIRS=include

RUN mkdir /build/resolv \
 && printf '%s\n' \
      '#include <netdb.h>' \
      'int res_query(const char *name, int class, int type, unsigned char *dest, int len)' \
      '{ h_errno = HOST_NOT_FOUND; return -1; }' \
      > /build/resolv/res_query.c \
 && emcc ${CFLAGS} -c /build/resolv/res_query.c -fPIC -o /build/resolv/libresolv.o \
 && emar rcs "$TARGET/lib/libresolv.a" /build/resolv/libresolv.o

RUN curl --fail --location --proto '=https' "$GLIB_URL" -o /build/downloads/glib.tar.xz \
 && printf '%s  %s\n' "$GLIB_SHA256" /build/downloads/glib.tar.xz | sha256sum --check --strict \
 && mkdir /build/glib \
 && tar -xJf /build/downloads/glib.tar.xz -C /build/glib --strip-components=1 \
 && mkdir -p /build/glib/subprojects/packagecache \
 && curl --fail --location --proto '=https' "$PCRE2_URL" -o /build/glib/subprojects/packagecache/pcre2-10.40.tar.bz2 \
 && printf '%s  %s\n' "$PCRE2_SHA256" /build/glib/subprojects/packagecache/pcre2-10.40.tar.bz2 | sha256sum --check --strict \
 && curl --fail --location --proto '=https' "$PCRE2_PATCH_URL" -o /build/glib/subprojects/packagecache/pcre2_10.40-3_patch.zip \
 && printf '%s  %s\n' "$PCRE2_PATCH_SHA256" /build/glib/subprojects/packagecache/pcre2_10.40-3_patch.zip | sha256sum --check --strict

RUN printf '%s\n' \
      '#!/bin/bash' \
      'set -euo pipefail' \
      'old="-Werror=unused-command-line-argument"' \
      'new="-Wno-error=unused-command-line-argument"' \
      'cmd="$1"; shift' \
      'args=()' \
      'for arg in "$@"; do args+=("${arg//$old/$new}"); done' \
      '"$cmd" "${args[@]}"' \
      > /build/emcc-meson-wrap.sh \
 && chmod +x /build/emcc-meson-wrap.sh \
 && printf '%s\n' \
      '[host_machine]' \
      "system = 'emscripten'" \
      "cpu_family = 'wasm32'" \
      "cpu = 'wasm32'" \
      "endian = 'little'" \
      '' \
      '[binaries]' \
      "c = ['bash', '/build/emcc-meson-wrap.sh', 'emcc']" \
      "cpp = ['bash', '/build/emcc-meson-wrap.sh', 'em++']" \
      "ar = 'emar'" \
      "ranlib = 'emranlib'" \
      "pkgconfig = ['pkg-config', '--static']" \
      > /build/cross.meson

RUN cd /build/glib \
 && export CFLAGS="-Wno-error=incompatible-function-pointer-types -Wincompatible-function-pointer-types -O2 -matomics -mbulk-memory -DNDEBUG -pthread -sWASM_BIGINT -sMALLOC=mimalloc -sASYNCIFY=1" \
 && export CXXFLAGS="$CFLAGS" \
 && meson setup _build --prefix="$TARGET" --cross-file=/build/cross.meson \
      --default-library=static --buildtype=release \
      --force-fallback-for=pcre2,gvdb -Dselinux=disabled -Dxattr=false \
      -Dlibmount=disabled -Dnls=disabled -Dtests=false -Dglib_assert=false \
      -Dglib_checks=false --wrap-mode=nodownload \
 && sed -i -E '/#define (HAVE_CLOSE_RANGE|HAVE_EPOLL_CREATE|HAVE_KQUEUE|HAVE_POSIX_SPAWN|HAVE_FALLOCATE) 1/d' _build/config.h \
 && meson install -C _build

RUN curl --fail --location --proto '=https' "$PIXMAN_URL" -o /build/downloads/pixman.tar.gz \
 && printf '%s  %s\n' "$PIXMAN_SHA256" /build/downloads/pixman.tar.gz | sha256sum --check --strict \
 && mkdir /build/pixman \
 && tar -xzf /build/downloads/pixman.tar.gz -C /build/pixman --strip-components=1 \
 && cd /build/pixman \
 && NOCONFIGURE=y ./autogen.sh \
 && emconfigure ./configure --prefix="$TARGET" \
 && emmake make -j1 \
 && emmake make install \
 && rm -f "$TARGET"/lib/libpixman-1.so*

RUN curl --fail --location --proto '=https' "$XTERM_PTY_URL" -o /build/downloads/xterm-pty.tgz \
 && printf '%s  %s\n' "$XTERM_PTY_SHA256" /build/downloads/xterm-pty.tgz | sha256sum --check --strict \
 && mkdir /build/xterm-pty \
 && tar -xzf /build/downloads/xterm-pty.tgz -C /build/xterm-pty --strip-components=1 \
 && test -f /build/xterm-pty/emscripten-pty.js

WORKDIR /build/qemu
