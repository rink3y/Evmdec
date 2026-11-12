#!/bin/sh
BIN=${BIN:-target/release/evmdec}
DIR=${DIR:-sample}
RUNS=${RUNS:-3}
ok=0; fail=0; timeouts=0; tb=0; tcov=0; tunres=0; tv=0; tvt=0; tmis=0
printf "%-44s %6s %6s %5s %7s %6s %9s %5s\n" contract bytes blocks cov unres funcs instr_ver mism
for f in "$DIR"/*.hex; do
  name=$(basename "$f" .hex)
  bytes=$(( ($(wc -c < "$f") - 3) / 2 ))
  out=$(timeout 120 "$BIN" decompile --json "$f" 2>/dev/null); rc=$?
  if [ $rc -eq 124 ]; then timeouts=$((timeouts+1)); printf "%-44s %6s TIMEOUT\n" "$name" "$bytes"; continue; fi
  if [ $rc -ne 0 ]; then fail=$((fail+1)); printf "%-44s %6s FAILED rc=%s\n" "$name" "$bytes" "$rc"; continue; fi
  ok=$((ok+1))
  st=$(printf "%s" "$out" | python3 -c "import json,sys; s=json.load(sys.stdin)['stats']; print(s['code_blocks'], s['covered_blocks'], s['unresolved_jumps'], s['external_functions']+s['internal_functions'])")
  set -- $st; blocks=$1; cov=$2; unres=$3; funcs=$4
  v=$(timeout 300 "$BIN" verify "$f" --runs "$RUNS" --json 2>/dev/null)
  if [ -n "$v" ]; then
    vs=$(printf "%s" "$v" | python3 -c "import json,sys; s=json.load(sys.stdin); print(s['instructions_verified'], s['instructions_total'], s['mismatch'])")
    set -- $vs; iv=$1; it=$2; mis=$3
  else iv=0; it=0; mis="?"; fi
  printf "%-44s %6s %6s %5s %7s %6s %9s %5s\n" "$name" "$bytes" "$blocks" "$cov" "$unres" "$funcs" "$iv/$it" "$mis"
  tb=$((tb+blocks)); tcov=$((tcov+cov)); tunres=$((tunres+unres)); tv=$((tv+iv)); tvt=$((tvt+it)); [ "$mis" != "?" ] && tmis=$((tmis+mis))
done
echo "contracts ok=$ok failed=$fail timeouts=$timeouts ; blocks covered $tcov/$tb ; unresolved jumps $tunres ; oracle instructions verified $tv/$tvt ; mismatches $tmis"
