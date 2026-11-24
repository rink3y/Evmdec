#!/bin/sh
BIN=${BIN:-target/release/evmdec}
DIR=${DIR:-testdata/mainnet}
failed=0; total=0; named=0; plain=0
for f in "$DIR"/*.hex; do
  name=$(basename "$f" .hex)
  total=$((total+1))
  said=$("$BIN" decompile "$f" --sol 2>&1 >/dev/null); rc=$?
  line=$(printf "%s\n" "$said" | grep "equal, branch" | head -1)
  counts=$(printf "%s\n" "$said" | sed -n 's/.* \([0-9]*\) functions by name, \([0-9]*\) as plain.*/\1 \2/p' | head -1)
  set -- ${counts:-0 0}
  named=$((named+$1)); plain=$((plain+$2))
  if [ $rc -ne 0 ]; then failed=$((failed+1)); line="FAILED: $(printf "%s\n" "$said" | tail -1 | cut -c1-200)"; fi
  printf "%-26s %3s plain of %3s named | %s\n" "$name" "$2" "$1" "$line"
done
echo "contracts whose Solidity file compiles and compares equal: $((total-failed)) of $total"
echo "functions written out as plain Solidity: $plain of $named named"
[ $failed -eq 0 ]
