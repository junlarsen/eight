lit:
    @echo "Running lit tests..."
    cargo build --all
    poetry run lit tests -v
