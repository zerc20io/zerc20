# @zerc20/cli

A zERC20 account in a terminal: `zerc20` watches an account by its view key, pays from one by its recovery phrase, and
runs a merge prover on your own machine.

```sh
npm install -g @zerc20/cli

export ZERC20_KEY='zerc20view1…'     # a view key to look, or the 24-word recovery phrase to pay
zerc20 balance
zerc20 history --csv
zerc20 send 10 USDC zerc20id1…
zerc20 prover start                  # then: zerc20 merge USDC --prover local
zerc20 install-skill                 # teaches the coding agents on this machine to use it
```

`zerc20 --help` lists every command; [docs.zerc20.io](https://docs.zerc20.io/developers/cli) says more.

## License

[AGPL-3.0](LICENSE). The merge prover's packages are under the nodes' Business Source License.
