FROM ubuntu:21.04 as builder

ENV DEBIAN_FRONTEND noninteractive

# deb http://apt.llvm.org/hirsute/ llvm-toolchain-hirsute-13 main
# deb-src http://apt.llvm.org/hirsute/ llvm-toolchain-hirsute-13 main

RUN apt-get update && apt-get install -y software-properties-common curl gnupg build-essential
RUN curl --proto '=https' --tlsv1.2 -sSf https://apt.llvm.org/llvm-snapshot.gpg.key | apt-key add -
RUN add-apt-repository -y 'deb http://apt.llvm.org/hirsute/ llvm-toolchain-hirsute-13 main'

RUN apt-get update && apt-get install -y llvm-13-dev
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"

RUN curl -fsSL https://deb.nodesource.com/setup_lts.x | bash -
RUN apt-get install -y nodejs

RUN npm install -g tree-sitter-cli

WORKDIR /deps
RUN curl -fsSL https://github.com/tree-sitter/tree-sitter/archive/refs/tags/v0.20.2.tar.gz | tar -xz
RUN cd tree-sitter-* && make -j8 && make install && ldconfig

WORKDIR /build
ADD . .

RUN make
# foo
FROM ubuntu:21.04

RUN apt-get update && apt-get install -y software-properties-common curl gnupg
RUN curl --proto '=https' --tlsv1.2 -sSf https://apt.llvm.org/llvm-snapshot.gpg.key | apt-key add -
RUN add-apt-repository -y 'deb http://apt.llvm.org/hirsute/ llvm-toolchain-hirsute-13 main'
RUN apt-get update && apt-get install -y libllvm13 && rm -rf /var/lib/apt/lists/*

COPY --from=builder \
    /usr/local/lib/libtree-sitter.a \
    /usr/local/lib/libtree-sitter.so.0.0 \
    /usr/local/lib/
RUN ln -s /usr/local/lib/libtree-sitter.so.0.0 \
    /usr/local/lib/libtree-sitter.so
RUN ln -s /usr/local/lib/libtree-sitter.so.0.0 \
    /usr/local/lib/libtree-sitter.so.0

COPY --from=builder /build/build/debug/aluminac .
COPY --from=builder /build/build/debug/alumina-boot .


