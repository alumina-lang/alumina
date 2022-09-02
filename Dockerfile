FROM ubuntu:22.04 as environment

ENV DEBIAN_FRONTEND noninteractive

RUN apt-get update && apt-get install -y software-properties-common curl gnupg build-essential git
RUN curl --proto '=https' --tlsv1.2 -sSf https://apt.llvm.org/llvm-snapshot.gpg.key | apt-key add -
RUN add-apt-repository -y 'deb http://apt.llvm.org/jammy/ llvm-toolchain-jammy-13 main'

RUN apt-get update && apt-get install -y llvm-13-dev
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"

RUN curl -fsSL https://deb.nodesource.com/setup_lts.x | bash -
RUN apt-get install -y nodejs

# libgit2 seems to use an extrordinary amout of memory when building on arm64
RUN /bin/echo -e "[net]\ngit-fetch-with-cli = true\n" >> $HOME/.cargo/config.toml

RUN cargo install tree-sitter-cli

WORKDIR /alumina/deps
RUN curl -fsSL https://github.com/tree-sitter/tree-sitter/archive/refs/tags/v0.20.7.tar.gz | tar -xz
RUN cd tree-sitter-* && make -j8 && make install && ldconfig

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

RUN apt-get update && apt-get install -y curl gnupg
RUN curl --proto '=https' --tlsv1.2 -sSf https://apt.llvm.org/llvm-snapshot.gpg.key | apt-key add -
RUN echo 'deb http://apt.llvm.org/jammy/ llvm-toolchain-jammy-13 main' > /etc/apt/sources.list.d/llvm.list
RUN apt-get update && apt-get install -y libllvm13 && rm -rf /var/lib/apt/lists/*

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

