#!/bin/sh
BIN=${BIN:-target/release/evmdec}
DIR=${DIR:-testdata/mainnet}
RUNS=${RUNS:-8}
printf "%-22s %7s %7s %6s %6s %6s %9s %9s %8s\n" contract blocks runs agree mism incon blk_ver instr_ver pct
tb=0; tr=0; ta=0; tm=0; ti=0; tbv=0; tiv=0; tit=0
for f in "$DIR"/*.hex; do
  name=$(basename "$f" .hex)
  out=$("$BIN" verify "$f" --runs "$RUNS" --json)
  g() { printf "%s" "$out" | python3 -c "import json,sys; print(json.load(sys.stdin)['$1'])"; }
  b=$(g blocks); r=$(g runs); a=$(g agree); m=$(g mismatch); i=$(g inconclusive); bv=$(g blocks_verified); iv=$(g instructions_verified); it=$(g instructions_total)
  pct=$(python3 -c "print(f'{100*$iv/max(1,$it):.2f}')")
  printf "%-22s %7s %7s %6s %6s %6s %9s %9s %8s\n" "$name" "$b" "$r" "$a" "$m" "$i" "$bv/$b" "$iv/$it" "$pct"
  tb=$((tb+b)); tr=$((tr+r)); ta=$((ta+a)); tm=$((tm+m)); ti=$((ti+i)); tbv=$((tbv+bv)); tiv=$((tiv+iv)); tit=$((tit+it))
done
pct=$(python3 -c "print(f'{100*$tiv/max(1,$tit):.3f}')")
printf "%-22s %7s %7s %6s %6s %6s %9s %9s %8s\n" TOTAL "$tb" "$tr" "$ta" "$tm" "$ti" "$tbv/$tb" "$tiv/$tit" "$pct"
if [ "$tb" -eq 0 ] || [ "$tm" -ne 0 ] || [ $((tiv * 1000)) -lt $((tit * ${MIN_PERMILLE:-985})) ]; then
  echo "FAIL no blocks checked, a mismatch, or under ${MIN_PERMILLE:-985} per mille of instructions verified"
  exit 1
fi
