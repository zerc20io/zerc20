# What backend/eif.sh packs an enclave's image into an EIF in, from stdin with no context:
#   docker build -t zerc20-nitro-cli - <backend/nitro-cli.Dockerfile
# nitro-cli puts its own kernel, init and NSM driver into the EIF, and PCR0 measures them. So its version is pinned
# here, with the image whose package repository serves it, rather than left to what each machine has installed.
FROM amazonlinux:2023@sha256:9cf762f5099b606bcd851391317af7cd75b11363c4816ebcb5e91292dd5736a7
RUN dnf install -y aws-nitro-enclaves-cli-1.5.0-0.amzn2023 aws-nitro-enclaves-cli-devel-1.5.0-0.amzn2023 \
  && dnf clean all
