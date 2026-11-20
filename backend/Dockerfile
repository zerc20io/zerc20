# Every node that runs on a host, from the repository root:
#   docker build -f backend/Dockerfile -t zerc20-host .
# The merge prover's host runs from it too, on the prover's own instance. The enclaves' images are
# backend/attester/Dockerfile and backend/merge-prover/Dockerfile. The attester's host asks KMS for its enclave's key
# through the AWS CLI, so it is in here too.
FROM rust:1.97.1-bookworm@sha256:0e2bcaef56d041a486784e54104a81aebe0da44bd03019bd70bc0401e42e4a97 AS build
WORKDIR /src
# not rust-toolchain.toml: the image's toolchain is the same, and the file's wasm target is for storage/
COPY Cargo.toml Cargo.lock ./
COPY zkp zkp
COPY backend backend
RUN cargo build --release --locked -p zerc20-indexer -p zerc20-root-prover -p zerc20-asp -p zerc20-attester \
  -p zerc20-transact-relayer -p zerc20-deposit-relayer -p zerc20-merge-prover -p zerc20-watcher -p zerc20-treasurer

FROM debian:bookworm-slim@sha256:7c7b2c966bc9ee8cedfeef67e0e279108992c77681fa595db4a9d65c06ccc587
# AWS CLI v2 with `kms decrypt --recipient`. Pinned like the images: the zips whose AWS CLI Team signature (key
# FB5DB77FD5C118B80511ADA8A6310ACC4672475C) checked out when they were pinned.
ARG AWSCLI=2.17.0
ARG AWSCLI_SHA256_x86_64=229bdc40a4b072c99570e2d07cbc1e1bd6ea67ca10f018b54271189a61f9b067
ARG AWSCLI_SHA256_aarch64=d382fcf9b7113e17936b0b8389dd719d9fad4342f3c07dd7b36f1f8f4175f80d
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl unzip \
  && arch=$(uname -m) \
  && curl -fsSL "https://awscli.amazonaws.com/awscli-exe-linux-$arch-$AWSCLI.zip" -o /tmp/awscli.zip \
  && sha=$AWSCLI_SHA256_x86_64 && if [ "$arch" = aarch64 ]; then sha=$AWSCLI_SHA256_aarch64; fi \
  && echo "$sha  /tmp/awscli.zip" | sha256sum -c - \
  && unzip -q /tmp/awscli.zip -d /tmp && /tmp/aws/install \
  && apt-get purge -y curl unzip && apt-get autoremove -y && rm -rf /tmp/aws* /var/lib/apt/lists/*
COPY --from=build /src/target/release/zerc20-indexer /src/target/release/zerc20-root-prover \
  /src/target/release/zerc20-asp /src/target/release/zerc20-attester /src/target/release/zerc20-transact-relayer \
  /src/target/release/zerc20-deposit-relayer /src/target/release/zerc20-merge-prover /src/target/release/zerc20-watcher \
  /src/target/release/zerc20-treasurer /usr/local/bin/
