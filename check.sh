#!/bin/sh
# check.sh - build lalr_gen and verify every expectation of the assignment.
# usage:  sh check.sh
# Exits 0 only if every check passes.

cd "$(dirname "$0")" || exit 1
pass=0
fail=0

ok()  { pass=$((pass + 1)); printf '  \033[32mPASS\033[0m  %s\n' "$1"; }
bad() { fail=$((fail + 1)); printf '  \033[31mFAIL\033[0m  %s\n' "$1"; }

# run the generator and squeeze runs of blanks, so patterns below need not
# count the spaces used for column alignment
run() { ./lalr_gen "$@" 2>/dev/null | tr -s ' '; }

# want <label> <fixed-string> <args to lalr_gen...>
want() {
    label=$1
    pat=$2
    shift 2
    if run "$@" | grep -qF -- "$pat"; then ok "$label"; else
        bad "$label"
        printf '        expected to find: %s\n' "$pat"
    fi
}

echo
echo "=== 1. build ==================================================="
out=$(gcc -Wall -Wextra -std=c99 -pedantic -o lalr_gen lalr_gen.c 2>&1)
if [ $? -ne 0 ]; then
    echo "  build FAILED:"
    echo "$out"
    exit 1
fi
if [ -z "$out" ]; then
    ok "gcc -Wall -Wextra -std=c99 -pedantic: zero warnings"
else
    bad "compiler produced output:"
    echo "$out"
fi

echo
echo "=== 2. grammar.txt: counts ====================================="
want "4 productions"        "productions (augmented) : 4"  grammar.txt
want "10 canonical LR(1) states" "canonical LR(1) states : 10" grammar.txt
want "7 LR(0) cores"        "distinct LR(0) cores : 7"      grammar.txt
want "no conflicts"         "table conflicts : 0"           grammar.txt

echo
echo "=== 3. grammar.txt: accepted strings ==========================="
for s in ccdd dd ccdccd; do
    want "$s accepted" "ACCEPTED" grammar.txt "$s"
done

echo
echo "=== 4. grammar.txt: rejected strings =========================="
want "cdc    -> invalid string"  "REJECTED - invalid string" grammar.txt cdc
want "cdc    -> names column 4"  "column 4:"                 grammar.txt cdc
want "cdc    -> expects c, d"    "expected one of: c, d"      grammar.txt cdc
want "cddccd -> invalid string"  "REJECTED - invalid string" grammar.txt cddccd
want "cxd    -> illegal symbol"  "REJECTED - illegal symbol" grammar.txt cxd
want "cxd    -> names column 2"  "column 2: 'x'"              grammar.txt cxd

echo
echo "=== 5. expr.txt on the SAME binary, no recompilation ==========="
want "7 productions"             "productions (augmented) : 7"  expr.txt
want "22 canonical LR(1) states" "canonical LR(1) states : 22"  expr.txt
want "12 LR(0) cores"            "distinct LR(0) cores : 12"    expr.txt
want "no conflicts"              "table conflicts : 0"          expr.txt
want "multi-char terminal id"    " id"                          expr.txt

echo
echo "=== 6. expr.txt: parses ========================================"
want "id + id * id accepted"  "ACCEPTED"              expr.txt "id + id * id"
want "id+id*id (no spaces)"   "ACCEPTED"              expr.txt "id+id*id"
want "( id + id ) * id"       "ACCEPTED"              expr.txt "( id + id ) * id"
want "id + * id rejected"     "REJECTED - invalid string" expr.txt "id + * id"
want "  -> at column 6"       "column 6:"             expr.txt "id + * id"
want "  -> expects (, id"     "expected one of: (, id" expr.txt "id + * id"
want "id @ id illegal"        "REJECTED - illegal symbol" expr.txt "id @ id"

echo
echo "=== 7. trace flag =============================================="
want "-t traces a shift"   "shift" -t grammar.txt ccdd
want "-t traces a reduce"  "reduce by" -t grammar.txt ccdd

echo
echo "=== 8. exit codes =============================================="
./lalr_gen grammar.txt ccdd >/dev/null 2>&1
[ $? -eq 0 ] && ok "accepted string exits 0" || bad "accepted string exits 0"
./lalr_gen grammar.txt cdc >/dev/null 2>&1
[ $? -eq 1 ] && ok "rejected string exits 1" || bad "rejected string exits 1"

echo
echo "==============================================================="
printf ' %d passed, %d failed\n' "$pass" "$fail"
echo "==============================================================="
echo
[ "$fail" -eq 0 ] || exit 1
