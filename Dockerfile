FROM ubuntu:22.04 as environment

ENV DEBIAN_FRONTEND noninteractive
ENV CARGO_REGISTRIES_CRATES_IO_PROTOCOL sparse

RUN apt-get update && apt-get install -y software-properties-common curl build-essential git

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"

RUN curl -fsSL https://deb.nodesource.com/setup_lts.x | bash -
RUN apt-get install -y nodejs

RUN cargo install tree-sitter-cli

WORKDIR /alumina/deps
RUN curl -fsSL https://github.com/tree-sitter/tree-sitter/archive/refs/tags/v0.20.8.tar.gz | tar -xz
RUN cd tree-sitter-* && make -j8 && make install && ldconfig
RUN curl -fsSL https://github.com/ianlancetaylor/libbacktrace/archive/master.tar.gz | tar -xz
RUN cd libbacktrace-* && ./configure && make -j8 && make install

FROM environment as builder

WORKDIR /alumina
ADD . .

ENV RELEASE=1
RUN make -j8

FROM ubuntu:22.04 as alumina-boot

COPY --from=builder /alumina/build/release/alumina-boot /usr/bin/alumina-boot
COPY ./sysroot /usr/include/alumina

WORKDIR /workspace
ENV ALUMINA_SYSROOT=/usr/include/alumina

ENTRYPOINT [ "/usr/bin/alumina-boot" ]

FROM ubuntu:22.04 as aluminac

COPY --from=builder \
    /usr/local/lib/libtree-sitter.a \
    /usr/local/lib/libtree-sitter.so.0.0 \
    /usr/local/lib/

RUN ln -s /usr/local/lib/libtree-sitter.so.0.0 \
    /usr/local/lib/libtree-sitter.so && \
    ln -s /usr/local/lib/libtree-sitter.so.0.0 \
    /usr/local/lib/libtree-sitter.so.0 && \
    ldconfig

COPY --from=builder /alumina/build/release/aluminac .

