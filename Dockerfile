# Images are named by digest so the same file always builds from the same layers.
# Move the tags and digests together when taking a newer base.
FROM rust:1.100.0-slim-bookworm@sha256:7c7d4eb4d05b7781187a327809466cfddf29753f6defdc3d19a0e291951b7a37 AS build
WORKDIR /src
COPY . .
RUN cargo build --release --locked -p evmdec-cli -p evmdec-server

FROM python:3.12-slim-bookworm@sha256:935c3c5b12357a7e10caa9c1e6ca5692344d97cf229832ef584be2cec9fc03df AS sigs
ARG SIGS=1
WORKDIR /sigs
COPY corpus/build_sigs.py .
RUN if [ "$SIGS" = "1" ]; then pip install --no-cache-dir pyarrow==26.0.1 numpy==2.5.4 \
    && python3 build_sigs.py --out sigs.idx && rm -rf .sigs-cache; else touch sigs.idx; fi

FROM debian:bookworm-slim@sha256:734a72b3d6142a71993b4bc580ca01d8ca687f77a2c422d96a961d3376b179bc
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates && rm -rf /var/lib/apt/lists/* \
    && useradd --system --no-create-home --shell /usr/sbin/nologin evmdec
COPY --from=build /src/target/release/evmdec /usr/local/bin/evmdec
COPY --from=build /src/target/release/evmdec-server /usr/local/bin/evmdec-server
COPY --from=sigs /sigs/sigs.idx /var/lib/evmdec/sigs.idx
ENV PORT=8080
EXPOSE 8080
USER evmdec
CMD ["evmdec-server"]
