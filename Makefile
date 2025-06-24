.PHONY: test

test:
	cargo test
	cargo verus verify
