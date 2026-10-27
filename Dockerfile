FROM rust:1-slim AS build
WORKDIR /src
COPY . .
RUN cargo build --release -p evmdec-cli -p evmdec-server

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates && rm -rf /var/lib/apt/lists/*
COPY --from=build /src/target/release/evmdec /usr/local/bin/evmdec
COPY --from=build /src/target/release/evmdec-server /usr/local/bin/evmdec-server
ENV PORT=8080
EXPOSE 8080
CMD ["evmdec-server"]
