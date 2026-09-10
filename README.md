# LALR Parser Generator

A general LR(1)/LALR(1) parser generator in a single ANSI C file. The grammar is
read from a text file at run time, so **one compiled binary builds a parser for any
context-free grammar you write** — no grammar is hard-coded anywhere in the source,
and nothing needs recompiling to switch grammars.

```
$ ./lalr_gen grammar.txt ccdd
ACCEPTED - the string is in the language

$ ./lalr_gen expr.txt "id + * id"          # same binary, different grammar
REJECTED - invalid string
  column 6: symbol '*' is legal but state 6 has no action for it
  expected one of: (, id
```

## Build

Requires only a C compiler and libc — no external libraries, no `malloc`.

```sh
gcc -Wall -o lalr_gen lalr_gen.c
```

Compiles with zero warnings under `gcc -Wall -Wextra -std=c99 -pedantic`.

## Usage

```
lalr_gen [-t] <grammar-file> [input string]
```

| Invocation | What it does |
|---|---|
| `./lalr_gen grammar.txt` | print the full report: grammar, symbol classification, FIRST sets, every LR(1) state, every transition, the ACTION/GOTO table, the LALR merge and a summary |
| `./lalr_gen grammar.txt ccdd` | parse one string against the grammar |
| `./lalr_gen -t grammar.txt ccdd` | the same, tracing every shift and reduce |
| `./lalr_gen --help` | usage summary |

`-t` must precede the grammar file; everything *after* the grammar file is treated as
input text. Arguments after the grammar file are joined with single blanks, so both
`./lalr_gen grammar.txt "c c d d"` and `./lalr_gen grammar.txt c c d d` work.

Exit status is `0` when the string is accepted, `1` when it is rejected or a fatal
error occurred. Grammar conflicts are written to **stderr**, so `2>conflicts.txt`
separates them from the report.

## Grammar file format

The reader defines the whole format; nothing else in the program knows about it.

```
# ...          comment, to the end of the line
%start X       optional; if absent, the LHS of the first rule is the start symbol
A -> x y z     symbols are separated by whitespace, so names may be any length
A -> x | y     '|' separates alternatives; each becomes its own production
A -> %empty    an epsilon production
```

Everything else is **derived**:

- a symbol appearing on any left-hand side is a **non-terminal**;
- every other symbol is a **terminal** — you never declare the alphabet;
- `S' -> S` is added as **production 0**;
- `$` is registered as the end marker.

`grammar.txt`:

```
%start S

S -> C C
C -> c C | d
```

`expr.txt` — note `id`, a terminal more than one character long:

```
%start E

E -> E + T | T
T -> T * F | F
F -> ( E ) | id
```

## Error reporting

Two distinct rejections, both naming the column.

**Illegal symbol** — the tokeniser finds text matching no terminal of this grammar:

```
$ ./lalr_gen grammar.txt cxd
REJECTED - illegal symbol
  column 2: 'x' begins no terminal of this grammar, so it cannot be tokenised
  the terminals of this grammar are: c, d
```

**Invalid string** — every symbol is legal, but `ACTION[state][lookahead]` is empty.
The expected set is read straight out of that state's ACTION row: every terminal
whose cell is not `A_ERROR`.

```
$ ./lalr_gen grammar.txt cdc
REJECTED - invalid string
  column 4: symbol '$' is legal but state 6 has no action for it
  expected one of: c, d
```

The tokeniser uses **longest match** over the terminal set, so `ccdd`, `c c d d` and
`id + id * id` all tokenise with no special cases — and with terminals `i` and `if`
present, `ifix` tokenises as `if i x`.

## Design

Symbols are stored as symbol-table indices, never as characters, so names may be any
length.

```c
Production { int lhs; int rhs[MAX_RHS]; int len; }   /* index in G = its number */
Item       { int prod; int dot; int look; }          /* ONE lookahead, not a set */
State      { Item items[MAX_ITEMS]; int n; }         /* behaves as a set */
```

Keeping exactly one lookahead per item is deliberate: dropping the `look` field then
gives the LR(0) core directly, which is precisely what the LALR merge test needs —
`sameCore()` and `countCores()` do nothing more than ignore that field.

Pipeline:

1. **`loadGrammar`** — read the file. `parseRule()` splits one line into its
   alternatives, `addProduction()` numbers each one. The line is walked with explicit
   pointers, never nested `strtok`: `strtok`'s hidden static pointer means an inner
   scan destroys the outer one, silently losing every alternative after the first.
2. **`computeFirst`** — FIRST sets and nullable flags by fixed-point iteration (sweep
   all productions until a pass changes nothing, so mutual recursion is fine).
   `firstOfString(seq, len, la, out)` computes FIRST(βa).
3. **`buildCollection`** — `closure()` applies the LR(1) closure rule using
   `firstOfString`; `gotoState()` advances the dot and closes. States are compared by
   mutual containment (`sameState`), not by position, so the driver terminates.
4. **`buildTables`** — ACTION/GOTO, every cell initialised to `A_ERROR` first, so an
   error is simply a cell nobody overwrote. Shift/reduce and reduce/reduce conflicts
   are reported on stderr with the state and symbol (resolved as shift, and as the
   lower-numbered production, respectively).
5. **`parse`** — stack-based LR driver.

All storage is static, sized by `MAX_` constants (`MAX_SYMBOLS`, `MAX_PRODS`,
`MAX_RHS`, `MAX_ITEMS`, `MAX_STATES`, …). A grammar that exceeds a limit exits with a
message naming the constant to raise, for example:

```
lalr_gen: fatal: more than 1024 LR(1) states - raise MAX_STATES
```

## Verified behaviour

`sh check.sh` rebuilds and asserts all of the following — 30 checks, exit 0 only if
every one passes.

| | `grammar.txt` | `expr.txt` |
|---|---|---|
| productions | 4 | 7 |
| canonical LR(1) states | 10 | 22 |
| distinct LR(0) cores (= LALR states) | 7 | 12 |
| conflicts | 0 | 0 |

```
grammar.txt :  ccdd, dd, ccdccd          accepted
               cdc, cddccd               invalid string
               cxd                       illegal symbol, column 2
expr.txt    :  id + id * id              accepted
               id + * id                 invalid string, column 6, expects "(, id"
```

Also exercised: `%empty` with nullable propagation through mutual recursion, an
omitted `%start`, multi-character terminals such as `:=` and `begin`, ambiguous and
dangling-else grammars, four alternatives on one line, longest-match tokenising, and
every `MAX_*` and malformed-grammar message.

## Files

| File | Purpose |
|---|---|
| `lalr_gen.c` | the entire generator |
| `grammar.txt` | `S -> C C`, `C -> c C \| d` |
| `expr.txt` | the expression grammar, with the multi-character terminal `id` |
| `check.sh` | build + 30-assertion regression harness |
| `CLAUDE.md` | working notes for this folder |
