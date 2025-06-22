FROM rust:1.87

WORKDIR /bsti
COPY . .

RUN cargo install --path .

CMD ["bash"]
