# The server (server/, a running-sum service) built against this checkout of
# etcd-io/raft with Antithesis instrumentation. Build context: the repository root.

FROM rust:1-bookworm AS log-forward
RUN rustup target add x86_64-unknown-linux-musl
COPY antithesis-fm/driver/log-forward/ /src/
RUN cd /src && cargo build --release --target x86_64-unknown-linux-musl

FROM golang:1.26-bookworm AS build
RUN go install github.com/antithesishq/antithesis-sdk-go/tools/antithesis-go-toolexec@v0.8.0
WORKDIR /src
COPY go.mod go.sum ./
COPY antithesis-fm/go.mod antithesis-fm/go.sum antithesis-fm/
COPY antithesis-fm/tracekit/go antithesis-fm/tracekit/go
RUN cd antithesis-fm && go mod download
COPY . .
WORKDIR /src/antithesis-fm
ENV CGO_ENABLED=1 \
    ANTITHESIS_INSTRUMENT=go.etcd.io/raft/v3,etcd-raft-formalized \
    ANTITHESIS_SYMBOLS_DIR=/symbols
RUN mkdir -p /symbols && go build -toolexec=antithesis-go-toolexec -o /raft-sum ./server && ls -la /symbols

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends bash curl jq ca-certificates procps \
    && rm -rf /var/lib/apt/lists/*
COPY --from=build /raft-sum /usr/local/bin/raft-sum
COPY --from=build /symbols /symbols
COPY --from=log-forward /src/target/x86_64-unknown-linux-musl/release/log-forward /usr/local/bin/
COPY antithesis-fm/driver/forward-logs /usr/local/bin/
RUN mkdir -p /data
ENTRYPOINT ["forward-logs", "raft-sum"]
