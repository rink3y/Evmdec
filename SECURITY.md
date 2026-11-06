# Security

evmdec is an analysis tool. It makes no transactions and holds no keys.

## A missed or wrong finding

Open an issue with the chain, the address or the bytecode, and what the analyzer said. A
contract that was exploited through something the analyzer did not report is the most useful
kind of issue: the TENDRIL case in the README came from one.

## A problem in the server

The web server fetches code and storage from public RPC endpoints and runs the decompiler on
whatever is pasted. If you find a way to make it hang, crash or reach something it should not,
open an issue marked security, or email the address in the repository's commit history.
