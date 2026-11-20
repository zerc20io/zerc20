# The merge prover's Nitro Enclave image. From the repository root:
#   backend/eif.sh merge-prover merge-prover.eif zkp/artifacts/merge/setup.json   # prints PCR0
# The build arguments, which eif.sh reads from the merge setup, are compiled into the binary, so PCR0 measures them:
# the merge keys it accepts. A commit and a setup build the same PCR0 on any machine: base images are pinned by digest,
# the build is --locked, and the binary's time is set, as PCR0 measures each file's time with its bytes. Publish the
# PCR0 of every release: wallets check it before sealing a witness to the enclave.
FROM rust:1.97.1-bookworm@sha256:0e2bcaef56d041a486784e54104a81aebe0da44bd03019bd70bc0401e42e4a97 AS build
ARG MERGE_PK_SHA256
ARG MERGE_VK_SHA256
WORKDIR /src
# not rust-toolchain.toml: the image's toolchain is the same, and the file's wasm target is for storage/
COPY Cargo.toml Cargo.lock ./
COPY zkp zkp
COPY backend backend
RUN test -n "$MERGE_PK_SHA256" && test -n "$MERGE_VK_SHA256" \
  && cargo build --release --locked -p zerc20-merge-prover --features enclave --bin enclave \
  && touch -d @0 target/release/enclave

FROM debian:bookworm-slim@sha256:7c7b2c966bc9ee8cedfeef67e0e279108992c77681fa595db4a9d65c06ccc587
COPY --from=build /src/target/release/enclave /enclave
CMD ["/enclave"]
