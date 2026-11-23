#!/bin/sh
BIN=${BIN:-target/release/evmdec}
DIR=${DIR:-testdata/mainnet}
failed=0; total=0
for f in "$DIR"/*.hex; do
  name=$(basename "$f" .hex)
  total=$((total+1))
  said=$("$BIN" decompile "$f" --sol 2>&1 >/dev/null); rc=$?
  line=$(printf "%s\n" "$said" | grep "equal, branch" | head -1)
  if [ $rc -ne 0 ]; then failed=$((failed+1)); line="FAILED: $(printf "%s\n" "$said" | tail -1 | cut -c1-200)"; fi
  printf "%-26s %s\n" "$name" "$line"
done
echo "contracts whose Solidity file compiles and compares equal: $((total-failed)) of $total"
[ $failed -eq 0 ]
