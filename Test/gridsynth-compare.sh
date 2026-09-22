#!/bin/bash
# Compare the Agda port of gridsynth (Programs/Gridsynth.agda) with the
# Haskell reference binary, byte for byte, on a list of argument sets.
#
# usage (in WSL, from anywhere):
#   bash Test/gridsynth-compare.sh [AGDA_BINARY [HASKELL_BINARY]]
#
# Defaults: AGDA_BINARY = ~/agdabuild/Gridsynth (built by
# agda --compile --compile-dir=$HOME/agdabuild Programs/Gridsynth.agda,
# e.g. via the agda-run.sh helper), HASKELL_BINARY = ~/nsref/gridsynth.
#
# For every argument set, stdout, stderr and the exit code of both
# programs are compared. Lines with measured run times (Runtime,
# Time/candidate, and the averaged timing lines of the -t table) are
# masked before comparing, since they naturally differ. The wall-clock
# times of both programs are printed for each case. The exit status of
# the script is the number of mismatches (0 = all identical).

AGDA=${1:-$HOME/agdabuild/Gridsynth}
HASK=${2:-$HOME/nsref/gridsynth}
TMO=${TMO:-600}
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

# One argument set per line, in shell syntax (evaluated with eval).
CASES=$(cat <<'EOF'
pi/128 -d 10 -r 1
pi/8 -d 20 -r 1
pi/8 -d 20 -r 1 -s
0.3 -e 1e-5 -r 42 -s
pi/128 -b 30 -r 7 -x
pi/4 -d 10 -r 1
pi/8 -d 20 -r 1 -p
pi/8 -d 20 -r 1 -p -s
pi/8 -d 20 -r 3 -p -x
pi/7 -d 12 -r 11 -p -l -s
pi/128 -d 10 -r 1 -l
pi/128 -d 10 -r 1 -l -s
pi/3 -d 15 -r '100 200' -s -l
-d 10 -r 1 -s -- -pi/4
' -pi/4' -d 3 -r 1
'(-pi/16)' -d 12 -r 5 -s
-3*pi/5 -d 10 -r 2 -s
0 -d 10 -r 1 -s
0 -d 10 -r 1 -p -s
0 -d 10 -r 1 -x
pi -d 10 -r 1 -s
pi -d 10 -r 1 -p -s
2*pi -d 10 -r 1 -s
pi/2 -d 10 -r 4 -s
pi/64 -d 30 -r 1 -s
pi/128 -d 50 -r 1 -s
pi/128 -d 50 -r 1 -p -s
1 -d 100 -r 9 -s
pi/128 -b 100 -r 3 -s -x
0.1 -e 0.5 -r 1 -s
0.1 -d 0 -r 1 -s
0.1 -b 0 -r 1 -s
0.1 -d 1.5 -r 1 -s
pi/9 -d 20 -r 1 -f 1 -s
pi/9 -d 20 -r 1 -f 3 -s -p
--digits=12 --rseed=9 --stats pi/5
--dig 12 --rs 9 --st --lat pi/5
-sx -d15 -r1 pi/6
-r 'abc' pi/4
-r ' 5 7' pi/4 -s -d 3
'sqrt(2)+sin(1)/3' -d 10 -r 1 -s
'exp(-2)' -d 10 -r 1 -l -s
'2^(1/3)' -d 10 -r 1 -s
pi/4 -d '(5)' -r 1
pi/4 -d '- 5' -r 1
pi/4 -d 0x5 -r 1
pi/4 -d 1e1 -r 1 -s
pi/4 -f 0x10 -r 1 -d 3
-t -c 1 -d 10 -r 1
-t -c 2 -d 20 -r 5 -p
-t -c 1 -d 10 -r '3 4' pi/3
--help
-h
-z -h

-z
--e 1
--h
-d
--digits
--help=3
-d x
-d -1
-b -3
-e 2
-e 0
-e 0.5 -r '12 34 ' pi
pi/4 -r 1234567
pi/4 -f 0
pi/4 -f -3
pi/4 -f x
pi/4 -f 1e1
pi/4 -c 3
-t -c 0
-t -c x
a b
a b c
pi/4+
-pi/4
-- -pi/4 -d 3 -r 1
pi/4 -d '5 '
pi/4 -d NaN -r 1
pi/4 -b x
pi/4 -e x
-x -q --foo --bits
EOF
)

fail=0
n=0
printf '%-45s %10s %10s  %s\n' "arguments" "haskell" "agda" "result"
while IFS= read -r line; do
  n=$((n+1))
  eval "args=($line)"
  mask() { sed -E -e 's/^(Runtime|Time\/candidate): .*/\1: <masked>/' \
                  -e 's/^% (Runtime|Time\/candidate): .*/% \1: <masked>/' \
                  -e 's/^.*(% Runtime, averaged|% Time per candidate, averaged)/<masked> \1/' "$1"; }
  t0=$(date +%s.%N)
  timeout "$TMO" "$HASK" "${args[@]}" > "$TMP/h.out" 2> "$TMP/h.err"; hrc=$?
  t1=$(date +%s.%N)
  timeout "$TMO" "$AGDA" "${args[@]}" > "$TMP/a.out" 2> "$TMP/a.err"; arc=$?
  t2=$(date +%s.%N)
  ht=$(echo "$t1 - $t0" | bc); at=$(echo "$t2 - $t1" | bc)
  if [ "$hrc" = "$arc" ] && cmp -s <(mask "$TMP/h.out") <(mask "$TMP/a.out") && cmp -s "$TMP/h.err" "$TMP/a.err"; then
    res="same (exit $hrc)"
  else
    res="DIFFERENT (exit $hrc / $arc)"
    fail=$((fail+1))
    { echo "---- $line"; diff <(mask "$TMP/h.out") <(mask "$TMP/a.out"); diff "$TMP/h.err" "$TMP/a.err"; } | head -20
  fi
  printf '%-45s %9.3fs %9.3fs  %s\n' "${line:0:45}" "$ht" "$at" "$res"
done <<< "$CASES"
echo "$n cases, $fail different"
exit $fail
