#!/usr/bin/env bash
# compiles programs to real x86-64 binaries, runs them, and checks that each one prints the same
# thing and exits with the same code as the interpreter. needs nasm and a C compiler.
#
#   tests/run.sh               every program in tests/
#   tests/run.sh FILE...       just these
#   tests/run.sh --random N    N random programs from `vc gen`
set -uo pipefail
cd "$(dirname "$0")/.."

lake build vc > /dev/null || exit 1
vc=.lake/build/bin/vc
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
cc -O2 -c runtime/runtime.c -o "$out/runtime.o" || exit 1

failed=0
passed=0

# check FILE: build it, run it, and compare with the interpreter
check() {
  local file=$1 name expected actual
  name=$(basename "$file" .lisp)
  expected=$($vc run "$file"; echo "(exit $?)")
  if ! { $vc asm "$file" > "$out/$name.asm" &&
         nasm -f elf64 "$out/$name.asm" -o "$out/$name.o" &&
         cc "$out/runtime.o" "$out/$name.o" -o "$out/$name"; }; then
    echo "FAIL $name: didn't build"
    failed=$((failed + 1))
    return
  fi
  actual=$("$out/$name"; echo "(exit $?)")
  if [[ "$expected" == "$actual" ]]; then
    [[ -n "${quiet:-}" ]] || echo "ok   $name: ${actual//$'\n'/ }"
    passed=$((passed + 1))
  else
    echo "FAIL $name: the interpreter says ${expected//$'\n'/ }, the binary says ${actual//$'\n'/ }"
    failed=$((failed + 1))
  fi
}

if [[ "${1:-}" == "--random" ]]; then
  quiet=1
  for ((seed = 1; seed <= ${2:-100}; seed++)); do
    $vc gen "$seed" > "$out/random_$seed.lisp"
    check "$out/random_$seed.lisp"
    # keep failing programs around to look at
    [[ $failed -eq 0 ]] || cp "$out/random_$seed.lisp" . 2> /dev/null
  done
elif [[ $# -gt 0 ]]; then
  for file in "$@"; do check "$file"; done
else
  for file in tests/*.lisp; do check "$file"; done
fi

echo "$passed passed, $failed failed"
[[ $failed -eq 0 ]]
