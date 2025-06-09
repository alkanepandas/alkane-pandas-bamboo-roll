# Alkane Panda Roll

Roll the Pandas.

## Building

```bash
cargo build --target wasm32-unknown-unknown --release
```

The compiled WASM binary will be available in `target/wasm32-unknown-unknown/release/alkane_pandas_roll.wasm`. 

## Deployment

```bash
oyl alkane new-contract -c ./target/alkanes/wasm32-unknown-unknown/release/alkane_pandas_bamboo_roll.wasm -data 1,0 -p oylnet
```

## Tracing

```bash
oyl provider alkanes --method trace -params '{"txid":"a1ccb55a8a66b9ddcd4340c6f03bd25c44159a7fe59e663e123c35f2028f7ecc", "vout":3}' -p oylnet
``` 