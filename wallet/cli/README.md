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

## Why it looks like this

- **One key, never an argument.** A view key and a recovery phrase look nothing alike, so a command takes either and
  does what that key can. It comes from a file, the environment, standard input or a prompt that shows nothing: a
  shell's history and the process list keep arguments.
- **Nothing secret stays.** The key is never written. What is kept is the account's synced state, which the SDK seals
  under a key of the key's, so that the next command reads only what is new.
- **A command is a process.** State on disk is all two commands share, and a lock file keeps a second one off an
  account the first has open.
- **Nothing is paid unasked.** A payment shows its fee and waits for a yes; with no terminal to ask on, only `--yes`
  pays. An operation an earlier command left under way is named before a sync moves it on.
- **The skill ships with the release.** What an agent must not get wrong (the key, the yes, a payment under way) is
  written beside the code it describes, and installed from it, so the two do not drift apart.
- **An old release says so.** Once a day a command asks npm for the newest release and names it, or says that this
  one is withdrawn. The answer is only shown: nothing is installed unasked, and no command trusts it.
- **The networks ship with the release.** Their settings pin the enclaves a wallet seals its witnesses to, so they
  come from the reviewed source, not from a server at run time.
- **The merge prover is the node's own binary,** a package per machine that npm picks. Run here, it serves this
  machine only: the SDK takes a prover without an enclave at a loopback address alone.

## License

[AGPL-3.0](LICENSE). The merge prover's packages are under the nodes' Business Source License.
