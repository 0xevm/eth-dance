# ETH-Dance
ETH-Dance is a DSL for contract interact, and with several features:
* Strong typing, for both variable and contract
* Built-in variable, for easily change state like `$account`, `$gas` or even `$endpoint`
* Powerful expression, `1.2e9u`, `1.2f64` and `1.2uq64` means `1200000000u`, `hex"3ff3333333333333"` and `0x13333333333333333u` correspondingly

## examples
a full examples could be like:
```shell
account1 = key"0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80"
account2 = key"0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"
# set confirmation check interval (in seconds)
$confirm_interval = 1
# set endpoint
$endpoint = "http://localhost:8545"
# set account
$account = account1
# foundry cheatcode, could invoke function in this
vm = address"0x7109709ECfa91a80626fF3989D68f67F5b1DD12D"
# deploy a contract to facotry
counter_factory = :deploy(CounterFactory)
# send a transaction calling `CounterFactory.create`
# note that `:` means send_transaction while `.` means call
counter_factory:create(1.2q64: U256, 1eth)
# annotate returning value is a contract `Counter`
counter: "Counter" = counter_factory.get_counter()
counter:set_admin($account)
#counter = :deploy(Counter)

# switch account, following transaction would be called from this `$account`
$account = account2

# send a transaction calling `counter.add`
counter:add(1)
counter:add(2)
# view result in `counter.sum`
sum = counter.sum()
# like assert_eq!(sum, 3) in rust
@assert.eq(sum, 3)
```

## How to use this
first you should compile `.sol` file in repo via
```shell
forge build
```
an evm would be necessary as well
```shell
anvil
```
and then run
```shell
cargo test
```

TODO
=====
- [ ] `StringPrefix` should not accept `$`
- [ ] `: built-in` to indicates built-in type
- [x] arguments should accept type annotation
- [ ] function dispatch should check conflict
- [x] switch endpoint in runtime
- [ ] include files
