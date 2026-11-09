FROM rust:1-slim AS build
WORKDIR /src
COPY . .
RUN cargo build --release -p evmdec-cli -p evmdec-server

FROM python:3.12-slim AS sigs
ARG SIGS=1
WORKDIR /sigs
COPY corpus/build_sigs.py .
RUN if [ "$SIGS" = "1" ]; then pip install --no-cache-dir pyarrow numpy \
    && python3 build_sigs.py --out sigs.idx && rm -rf .sigs-cache; else touch sigs.idx; fi

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates && rm -rf /var/lib/apt/lists/*
COPY --from=build /src/target/release/evmdec /usr/local/bin/evmdec
COPY --from=build /src/target/release/evmdec-server /usr/local/bin/evmdec-server
COPY --from=sigs /sigs/sigs.idx /var/lib/evmdec/sigs.idx
ENV PORT=8080
EXPOSE 8080
CMD ["evmdec-server"]
