# Security

evmdec is a decompiler. It makes no transactions and holds no keys.

## Wrong output

Open an issue with the chain, the address or the bytecode, and the lines that are wrong.
Code that reads differently from what the bytecode does is the most useful kind of issue.

## A problem in the server

The web server fetches code and storage from public RPC endpoints and runs the decompiler on
whatever is pasted. If you find a way to make it hang, crash or reach something it should not,
open an issue marked security, or email the address in the repository's commit history.
