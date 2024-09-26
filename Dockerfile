FROM ubuntu:24.04 as environment

ENV DEBIAN_FRONTEND noninteractive
ENV CARGO_REGISTRIES_CRATES_IO_PROTOCOL sparse

RUN apt-get update && apt-get install -y software-properties-common curl build-essential git ca-certificates gnupg

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"

RUN mkdir -p /etc/apt/keyrings && \
    (curl -fsSL https://deb.nodesource.com/gpgkey/nodesource-repo.gpg.key | gpg --dearmor -o /etc/apt/keyrings/nodesource.gpg) && \
    (echo "deb [signed-by=/etc/apt/keyrings/nodesource.gpg] https://deb.nodesource.com/node_18.x nodistro main" | tee /etc/apt/sources.list.d/nodesource.list) && \
    apt-get update && \
    apt-get install -y nodejs

RUN cargo install tree-sitter-cli

WORKDIR /alumina/deps
RUN curl -fsSL https://github.com/tree-sitter/tree-sitter/archive/refs/tags/v0.23.0.tar.gz | tar -xz
RUN cd tree-sitter-* && make -j8 && make install && ldconfig
RUN curl -fsSL https://github.com/ianlancetaylor/libbacktrace/archive/master.tar.gz | tar -xz
RUN cd libbacktrace-* && ./configure && make -j8 && make install

FROM environment as builder

WORKDIR /alumina
ADD . .

ENV RELEASE=1
RUN make -j8

FROM ubuntu:24.04 as alumina-boot

COPY --from=builder /alumina/build/release/alumina-boot /usr/bin/alumina-boot
COPY ./sysroot /usr/include/alumina

WORKDIR /workspace
ENV ALUMINA_SYSROOT=/usr/include/alumina

ENTRYPOINT [ "/usr/bin/alumina-boot" ]
