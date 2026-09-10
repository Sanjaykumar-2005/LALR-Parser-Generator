/* ------------------------------------------------------------------------
 * lalr_gen.c - a general LR(1)/LALR(1) parser generator.
 *
 * No grammar is hard-coded anywhere in this file.  The grammar is read from
 * a text file named on the command line, so one compiled binary builds a
 * parser for any context-free grammar the user writes.
 *
 *   build : gcc -Wall -Wextra -std=c99 -o lalr_gen lalr_gen.c
 *   use   : lalr_gen [-t] <grammar-file> [input string]
 *
 * With no input string the program prints a full report of the grammar, the
 * canonical LR(1) collection and the LALR(1) merge.  With an input string it
 * runs the table-driven parser over it;  -t traces every shift and reduce.
 *
 * Grammar file format (defined only here, in the reader):
 *
 *     # ...        comment to end of line
 *     %start X     optional; if absent the LHS of the first rule is used
 *     A -> x y z   symbols are separated by whitespace, so names may be
 *                  any length
 *     A -> x | y   '|' separates alternatives, each becomes its own
 *                  production
 *     A -> %empty  an epsilon production
 *
 * Everything else is derived: a symbol that appears on some left-hand side
 * is a non-terminal, every other symbol is a terminal, S' -> S is added as
 * production 0 and '$' is registered as the end marker.  The user never
 * declares the alphabet.
 * ------------------------------------------------------------------------ */

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <ctype.h>

/* ------------------------------------------------------------------ limits
 * All storage is static;  nothing in this program calls malloc.  Exceeding
 * any limit is a clean exit with a message naming the constant to raise.
 */
#define MAX_NAME     64      /* longest symbol name, including the NUL      */
#define MAX_SYMBOLS 128      /* distinct symbols (terminals + non-terminals)*/
#define MAX_PRODS   256      /* productions, the augmented one included     */
#define MAX_RHS      32      /* symbols on one right-hand side              */
#define MAX_ITEMS   512      /* LR(1) items in one state                    */
#define MAX_STATES 1024      /* states in the canonical LR(1) collection     */
#define MAX_LINE   1024      /* longest grammar-file line / input string    */
#define MAX_TOKENS 1024      /* tokens in one input string                  */
#define MAX_STACK  1024      /* parser stack depth                          */

/* ------------------------------------------------------------- data types */

typedef struct {
    int lhs;                 /* symbol index of the left-hand side          */
    int rhs[MAX_RHS];        /* symbol indices of the right-hand side       */
    int len;                 /* 0 for an epsilon production                 */
} Production;                /* the index in G[] *is* the production number */

typedef struct {
    int prod;                /* which production                            */
    int dot;                 /* 0 .. G[prod].len                            */
    int look;                /* ONE lookahead terminal, not a set.  Dropping
                              * this field leaves the LR(0) core, which is
                              * exactly what the LALR merge test compares.  */
} Item;

typedef struct {
    Item items[MAX_ITEMS];
    int  n;                  /* items[0..n-1] behave as a set: addItem()
                              * never stores a duplicate                    */
} State;

enum { A_ERROR = 0, A_SHIFT, A_REDUCE, A_ACCEPT };

/* ----------------------------------------------------------- global tables */

static char symName[MAX_SYMBOLS][MAX_NAME];
static int  symIsNT[MAX_SYMBOLS];            /* 1 = non-terminal            */
static int  nsym = 0;

static Production G[MAX_PRODS];
static int  nprod = 0;

static int  augSym   = -1;                   /* S'                          */
static int  startSym = -1;                   /* S                           */
static int  endSym   = -1;                   /* $                           */

static char firstSet[MAX_SYMBOLS][MAX_SYMBOLS];   /* firstSet[X][t] != 0    */
static int  nullable[MAX_SYMBOLS];

static State states[MAX_STATES];
static int   nstates = 0;
static int   trans[MAX_STATES][MAX_SYMBOLS];      /* -1 = no transition     */

static int  actKind[MAX_STATES][MAX_SYMBOLS];     /* A_ERROR .. A_ACCEPT    */
static int  actVal[MAX_STATES][MAX_SYMBOLS];      /* target state / prod no */
static int  gotoTab[MAX_STATES][MAX_SYMBOLS];     /* -1 = error             */
static int  nconflict = 0;

/* raw rules, as text, before the symbol table exists ---------------------- */
static char rawLhs[MAX_PRODS][MAX_NAME];
static char rawRhs[MAX_PRODS][MAX_RHS][MAX_NAME];
static int  rawLen[MAX_PRODS];
static int  nraw = 0;

/* tokenised input -------------------------------------------------------- */
static int tok[MAX_TOKENS];                  /* symbol index of each token  */
static int tcol[MAX_TOKENS];                 /* 1-based column of each one  */
static int ntok = 0;

/* ------------------------------------------------------------- utilities */

static void fatal(const char *fmt, ...)
{
    va_list ap;
    fputs("lalr_gen: fatal: ", stderr);
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fputc('\n', stderr);
    exit(EXIT_FAILURE);
}

static char *trim(char *s)
{
    char *e;
    while (*s && isspace((unsigned char)*s)) s++;
    e = s + strlen(s);
    while (e > s && isspace((unsigned char)e[-1])) *--e = '\0';
    return s;
}

static int lookupSym(const char *s)
{
    int i;
    for (i = 0; i < nsym; i++)
        if (strcmp(symName[i], s) == 0) return i;
    return -1;
}

/* intern a name: return its index, creating the entry on first sight.  New
 * symbols start out classified as terminals;  loadGrammar() promotes every
 * name it has seen on a left-hand side. */
static int intern(const char *s)
{
    int i = lookupSym(s);
    if (i >= 0) return i;
    if ((int)strlen(s) >= MAX_NAME)
        fatal("symbol \"%s\" is longer than %d characters - raise MAX_NAME",
              s, MAX_NAME - 1);
    if (nsym >= MAX_SYMBOLS)
        fatal("grammar uses more than %d distinct symbols - raise MAX_SYMBOLS",
              MAX_SYMBOLS);
    strcpy(symName[nsym], s);
    symIsNT[nsym] = 0;
    return nsym++;
}

static int addProduction(int lhs, const int *rhs, int len)
{
    int i;
    if (nprod >= MAX_PRODS)
        fatal("grammar has more than %d productions - raise MAX_PRODS",
              MAX_PRODS);
    if (len > MAX_RHS)
        fatal("a right-hand side of %s has more than %d symbols - raise MAX_RHS",
              symName[lhs], MAX_RHS);
    G[nprod].lhs = lhs;
    G[nprod].len = len;
    for (i = 0; i < len; i++) G[nprod].rhs[i] = rhs[i];
    return nprod++;
}

static void printProduction(FILE *f, int p)
{
    int i;
    fprintf(f, "%s ->", symName[G[p].lhs]);
    if (G[p].len == 0) fprintf(f, " %%empty");
    for (i = 0; i < G[p].len; i++) fprintf(f, " %s", symName[G[p].rhs[i]]);
}

static void printItem(FILE *f, const Item *x)
{
    const Production *P = &G[x->prod];
    int i;
    fprintf(f, "[%s ->", symName[P->lhs]);
    for (i = 0; i < P->len; i++) {
        if (i == x->dot) fprintf(f, " .");
        fprintf(f, " %s", symName[P->rhs[i]]);
    }
    if (x->dot == P->len) fprintf(f, " .");
    fprintf(f, " , %s]", symName[x->look]);
}

/* ===================================================================== 1.
 * loadGrammar - read the grammar file.
 * ===================================================================== */

/* record one alternative while the symbol table does not exist yet */
static void addRaw(const char *lhs, char toks[][MAX_NAME], int n)
{
    int i;
    if (nraw >= MAX_PRODS - 1)
        fatal("grammar file holds more than %d productions - raise MAX_PRODS",
              MAX_PRODS - 1);
    if ((int)strlen(lhs) >= MAX_NAME)
        fatal("symbol \"%s\" is longer than %d characters - raise MAX_NAME",
              lhs, MAX_NAME - 1);
    strcpy(rawLhs[nraw], lhs);
    for (i = 0; i < n; i++) strcpy(rawRhs[nraw][i], toks[i]);
    rawLen[nraw] = n;
    nraw++;
}

/* Split one rule line into its alternatives.
 *
 * This walks the line with explicit pointers on purpose.  strtok() keeps a
 * single hidden static pointer, so a nested strtok() - an inner scan for the
 * symbols of one alternative inside an outer scan for the alternatives -
 * destroys the outer scan's position and every alternative after the first is
 * silently lost.  Nothing here is allowed to rely on that hidden state.
 */
static void parseRule(char *line, int lineno)
{
    char *arrow, *p, *q;
    char  lhs[MAX_NAME];
    char  toks[MAX_RHS][MAX_NAME];
    int   i, n, ln;

    arrow = strstr(line, "->");
    if (arrow == NULL)
        fatal("line %d: not a rule and not a directive, no \"->\" found: %s",
              lineno, line);

    *arrow = '\0';
    q  = trim(line);
    ln = (int)strlen(q);
    if (ln == 0)
        fatal("line %d: nothing stands to the left of \"->\"", lineno);
    if (ln >= MAX_NAME)
        fatal("line %d: symbol \"%s\" is longer than %d characters"
              " - raise MAX_NAME", lineno, q, MAX_NAME - 1);
    for (i = 0; i < ln; i++)
        if (isspace((unsigned char)q[i]))
            fatal("line %d: \"%s\" - exactly one symbol may stand left of"
                  " \"->\"", lineno, q);
    strcpy(lhs, q);

    p = arrow + 2;
    for (;;) {                       /* one turn of this loop per alternative */
        n = 0;
        for (;;) {                   /* collect the symbols of one alternative */
            int m = 0;
            while (*p && isspace((unsigned char)*p)) p++;
            if (*p == '\0' || *p == '|') break;
            if (n >= MAX_RHS)
                fatal("line %d: more than %d symbols on one right-hand side"
                      " - raise MAX_RHS", lineno, MAX_RHS);
            while (*p && !isspace((unsigned char)*p) && *p != '|') {
                if (m >= MAX_NAME - 1)
                    fatal("line %d: symbol is longer than %d characters"
                          " - raise MAX_NAME", lineno, MAX_NAME - 1);
                toks[n][m++] = *p++;
            }
            toks[n][m] = '\0';
            n++;
        }

        if (n == 0)
            fatal("line %d: empty alternative - write \"%%empty\" for an"
                  " epsilon production", lineno);
        if (n == 1 && strcmp(toks[0], "%empty") == 0) {
            n = 0;                                   /* epsilon production */
        } else {
            for (i = 0; i < n; i++) {
                if (strcmp(toks[i], "%empty") == 0)
                    fatal("line %d: %%empty must be the whole right-hand side",
                          lineno);
                if (toks[i][0] == '%')
                    fatal("line %d: unknown directive word \"%s\"",
                          lineno, toks[i]);
            }
        }
        addRaw(lhs, toks, n);

        if (*p == '|') { p++; continue; }
        break;
    }
}

static void parseDirective(char *line, int lineno, char *startName)
{
    char *p = line + 1;                       /* just past the '%'          */
    char  word[MAX_NAME];
    int   n = 0;

    while (*p && !isspace((unsigned char)*p)) {
        if (n < MAX_NAME - 1) word[n++] = *p;
        p++;
    }
    word[n] = '\0';
    if (strcmp(word, "start") != 0)
        fatal("line %d: unknown directive \"%%%s\" (only %%start exists)",
              lineno, word);

    while (*p && isspace((unsigned char)*p)) p++;
    n = 0;
    while (*p && !isspace((unsigned char)*p)) {
        if (n >= MAX_NAME - 1)
            fatal("line %d: symbol is longer than %d characters - raise"
                  " MAX_NAME", lineno, MAX_NAME - 1);
        word[n++] = *p++;
    }
    word[n] = '\0';
    if (n == 0)
        fatal("line %d: %%start needs a symbol name", lineno);
    while (*p && isspace((unsigned char)*p)) p++;
    if (*p != '\0')
        fatal("line %d: %%start takes exactly one symbol", lineno);
    if (startName[0] != '\0')
        fatal("line %d: a second %%start directive (already \"%s\")",
              lineno, startName);
    strcpy(startName, word);
}

static void loadGrammar(const char *path)
{
    char  buf[MAX_LINE];
    char  startName[MAX_NAME];
    char  augName[MAX_NAME];
    FILE *f;
    int   lineno = 0, r, i, rhs[MAX_RHS];

    startName[0] = '\0';

    f = fopen(path, "r");
    if (f == NULL) fatal("cannot open grammar file \"%s\"", path);

    while (fgets(buf, (int)sizeof buf, f) != NULL) {
        char *hash, *s;
        lineno++;
        if (strchr(buf, '\n') == NULL && !feof(f))
            fatal("line %d of \"%s\" is longer than %d characters - raise"
                  " MAX_LINE", lineno, path, MAX_LINE - 1);
        hash = strchr(buf, '#');
        if (hash != NULL) *hash = '\0';              /* comment to line end */
        s = trim(buf);
        if (*s == '\0') continue;
        if (*s == '%' && strncmp(s, "%empty", 6) != 0)
            parseDirective(s, lineno, startName);
        else
            parseRule(s, lineno);
    }
    fclose(f);

    if (nraw == 0) fatal("grammar file \"%s\" holds no productions", path);
    if (startName[0] == '\0') strcpy(startName, rawLhs[0]);

    /* Build the symbol table.  S' first, then '$', then every left-hand side
     * (these are the non-terminals), then the remaining right-hand-side names
     * - whatever is left over is a terminal. */
    strcpy(augName, startName);
    for (;;) {                   /* S', then S'' ... until the name is fresh */
        int clash = 0, j;
        if ((int)strlen(augName) >= MAX_NAME - 1)
            fatal("no room to build an augmented start symbol from \"%s\""
                  " - raise MAX_NAME", startName);
        strcat(augName, "'");
        for (r = 0; r < nraw && !clash; r++) {
            if (strcmp(rawLhs[r], augName) == 0) clash = 1;
            for (j = 0; j < rawLen[r] && !clash; j++)
                if (strcmp(rawRhs[r][j], augName) == 0) clash = 1;
        }
        if (!clash) break;
    }
    augSym = intern(augName);
    symIsNT[augSym] = 1;
    endSym = intern("$");                            /* the end marker      */

    for (r = 0; r < nraw; r++) symIsNT[intern(rawLhs[r])] = 1;

    startSym = lookupSym(startName);
    if (startSym < 0 || !symIsNT[startSym])
        fatal("start symbol \"%s\" never appears on a left-hand side",
              startName);

    rhs[0] = startSym;
    addProduction(augSym, rhs, 1);                   /* production 0        */

    for (r = 0; r < nraw; r++) {
        int lhs = lookupSym(rawLhs[r]);
        for (i = 0; i < rawLen[r]; i++) rhs[i] = intern(rawRhs[r][i]);
        addProduction(lhs, rhs, rawLen[r]);
    }
}

/* ===================================================================== 2.
 * computeFirst - nullable flags and FIRST sets by fixed-point iteration.
 * One sweep over every production is repeated until a pass changes nothing,
 * so mutual recursion between rules needs no special treatment.
 * ===================================================================== */

static void computeFirst(void)
{
    int changed, p, i, j, t;

    memset(firstSet, 0, sizeof firstSet);
    memset(nullable, 0, sizeof nullable);
    for (i = 0; i < nsym; i++)
        if (!symIsNT[i]) firstSet[i][i] = 1;         /* FIRST(a) = { a }    */

    do {
        changed = 0;
        for (p = 0; p < nprod; p++) {
            int A = G[p].lhs, allNullable = 1;
            for (j = 0; j < G[p].len; j++) {
                int X = G[p].rhs[j];
                for (t = 0; t < nsym; t++)
                    if (firstSet[X][t] && !firstSet[A][t]) {
                        firstSet[A][t] = 1;
                        changed = 1;
                    }
                if (!nullable[X]) { allNullable = 0; break; }
            }
            if (allNullable && !nullable[A]) { nullable[A] = 1; changed = 1; }
        }
    } while (changed);
}

/* FIRST(beta a): the terminals that may open the string seq[0..len-1], plus
 * the lookahead la when every symbol of seq is nullable. */
static void firstOfString(const int *seq, int len, int la, char *out)
{
    int i, t, allNullable = 1;
    memset(out, 0, (size_t)nsym);
    for (i = 0; i < len; i++) {
        int X = seq[i];
        for (t = 0; t < nsym; t++)
            if (firstSet[X][t]) out[t] = 1;
        if (!nullable[X]) { allNullable = 0; break; }
    }
    if (allNullable && la >= 0) out[la] = 1;
}

/* ===================================================================== 3.
 * buildCollection - the canonical LR(1) collection.
 * ===================================================================== */

static int addItem(State *s, int prod, int dot, int look)
{
    int i;
    for (i = 0; i < s->n; i++)
        if (s->items[i].prod == prod &&
            s->items[i].dot  == dot  &&
            s->items[i].look == look) return 0;      /* already in the set  */
    if (s->n >= MAX_ITEMS)
        fatal("a state needs more than %d LR(1) items - raise MAX_ITEMS",
              MAX_ITEMS);
    s->items[s->n].prod = prod;
    s->items[s->n].dot  = dot;
    s->items[s->n].look = look;
    s->n++;
    return 1;
}

/* LR(1) closure: for [A -> alpha . B beta , a] and every B -> gamma, add
 * [B -> . gamma , b] for every b in FIRST(beta a). */
static void closure(State *s)
{
    char fs[MAX_SYMBOLS];
    int  changed = 1;

    while (changed) {
        int i;
        changed = 0;
        for (i = 0; i < s->n; i++) {               /* s->n grows as we go   */
            const Production *P = &G[s->items[i].prod];
            int dot = s->items[i].dot, B, p, t;
            if (dot >= P->len) continue;
            B = P->rhs[dot];
            if (!symIsNT[B]) continue;
            firstOfString(P->rhs + dot + 1, P->len - dot - 1,
                          s->items[i].look, fs);
            for (p = 0; p < nprod; p++) {
                if (G[p].lhs != B) continue;
                for (t = 0; t < nsym; t++)
                    if (fs[t] && addItem(s, p, 0, t)) changed = 1;
            }
        }
    }
}

/* GOTO(s, sym): advance the dot over sym in every item that can, then close */
static void gotoState(const State *s, int sym, State *out)
{
    int i;
    out->n = 0;
    for (i = 0; i < s->n; i++) {
        const Production *P = &G[s->items[i].prod];
        if (s->items[i].dot < P->len && P->rhs[s->items[i].dot] == sym)
            addItem(out, s->items[i].prod, s->items[i].dot + 1,
                    s->items[i].look);
    }
    if (out->n > 0) closure(out);
}

static int subsetOf(const State *a, const State *b)
{
    int i, j;
    for (i = 0; i < a->n; i++) {
        for (j = 0; j < b->n; j++)
            if (a->items[i].prod == b->items[j].prod &&
                a->items[i].dot  == b->items[j].dot  &&
                a->items[i].look == b->items[j].look) break;
        if (j == b->n) return 0;
    }
    return 1;
}

/* States are compared as sets, by mutual containment - never by the order in
 * which the items happen to sit in the array.  That is what lets the driver
 * below recognise a state it has already built, and so terminate. */
static int sameState(const State *a, const State *b)
{
    return subsetOf(a, b) && subsetOf(b, a);
}

/* the same comparison with the lookaheads dropped: the LR(0) core */
static int coreSubsetOf(const State *a, const State *b)
{
    int i, j;
    for (i = 0; i < a->n; i++) {
        for (j = 0; j < b->n; j++)
            if (a->items[i].prod == b->items[j].prod &&
                a->items[i].dot  == b->items[j].dot) break;
        if (j == b->n) return 0;
    }
    return 1;
}

static int sameCore(const State *a, const State *b)
{
    return coreSubsetOf(a, b) && coreSubsetOf(b, a);
}

/* number of distinct LR(0) cores = number of LALR(1) states after merging */
static int countCores(void)
{
    int i, j, c = 0;
    for (i = 0; i < nstates; i++) {
        for (j = 0; j < i; j++)
            if (sameCore(&states[i], &states[j])) break;
        if (j == i) c++;
    }
    return c;
}

static State scratch;                 /* kept static: a State is sizeable  */

static void buildCollection(void)
{
    int i, a;

    states[0].n = 0;
    addItem(&states[0], 0, 0, endSym);               /* [S' -> . S , $]     */
    closure(&states[0]);
    nstates = 1;

    for (i = 0; i < nstates; i++) {
        for (a = 0; a < nsym; a++) trans[i][a] = -1;
        for (a = 0; a < nsym; a++) {
            int j;
            gotoState(&states[i], a, &scratch);
            if (scratch.n == 0) continue;
            for (j = 0; j < nstates; j++)
                if (sameState(&scratch, &states[j])) break;
            if (j == nstates) {
                if (nstates >= MAX_STATES)
                    fatal("more than %d LR(1) states - raise MAX_STATES",
                          MAX_STATES);
                states[nstates] = scratch;
                nstates++;
            }
            trans[i][a] = j;
        }
    }
}

/* ===================================================================== 4.
 * buildTables - ACTION and GOTO.
 * ===================================================================== */

static void buildTables(void)
{
    int i, a, k;

    /* Every cell starts as A_ERROR, so a parse error is simply a cell that
     * nobody overwrote - there is no separate error table to keep in step. */
    for (i = 0; i < nstates; i++)
        for (a = 0; a < nsym; a++) {
            actKind[i][a] = A_ERROR;
            actVal[i][a]  = 0;
            gotoTab[i][a] = -1;
        }

    for (i = 0; i < nstates; i++) {
        /* shifts and gotos come straight out of the transitions */
        for (a = 0; a < nsym; a++) {
            int j = trans[i][a];
            if (j < 0) continue;
            if (symIsNT[a]) {
                gotoTab[i][a] = j;
            } else {
                actKind[i][a] = A_SHIFT;
                actVal[i][a]  = j;
            }
        }
        /* reductions come from the items whose dot has reached the end */
        for (k = 0; k < states[i].n; k++) {
            const Item *x = &states[i].items[k];
            int la = x->look;
            if (x->dot != G[x->prod].len) continue;
            if (x->prod == 0) {                      /* [S' -> S . , $]     */
                if (la == endSym) {
                    actKind[i][la] = A_ACCEPT;
                    actVal[i][la]  = 0;
                }
                continue;
            }
            if (actKind[i][la] == A_SHIFT) {
                nconflict++;
                fprintf(stderr, "lalr_gen: conflict: shift/reduce in state %d"
                        " on '%s' - shift to state %d vs reduce by (%d) ",
                        i, symName[la], actVal[i][la], x->prod);
                printProduction(stderr, x->prod);
                fprintf(stderr, "  [resolved as shift]\n");
            } else if (actKind[i][la] == A_REDUCE && actVal[i][la] != x->prod) {
                int keep = actVal[i][la] < x->prod ? actVal[i][la] : x->prod;
                nconflict++;
                fprintf(stderr, "lalr_gen: conflict: reduce/reduce in state %d"
                        " on '%s' - production %d vs production %d"
                        "  [resolved as production %d]\n",
                        i, symName[la], actVal[i][la], x->prod, keep);
                actVal[i][la] = keep;
            } else if (actKind[i][la] == A_ERROR) {
                actKind[i][la] = A_REDUCE;
                actVal[i][la]  = x->prod;
            }
        }
    }
}

/* ===================================================================== 5.
 * parse - the stack-based LR driver, with the two rejections.
 * ===================================================================== */

/* every terminal whose ACTION cell in this state is not A_ERROR, read
 * straight out of the table row */
static void printExpected(FILE *f, int st)
{
    int a, first = 1;
    for (a = 0; a < nsym; a++) {
        if (symIsNT[a]) continue;
        if (actKind[st][a] == A_ERROR) continue;
        fprintf(f, "%s%s", first ? "" : ", ", symName[a]);
        first = 0;
    }
    if (first) fprintf(f, "(nothing - this state accepts no terminal)");
}

static void printTerminals(FILE *f)
{
    int a, first = 1;
    for (a = 0; a < nsym; a++) {
        if (symIsNT[a] || a == endSym) continue;
        fprintf(f, "%s%s", first ? "" : ", ", symName[a]);
        first = 0;
    }
}

/* Longest match over the terminal set.  Because the longest terminal that
 * fits at the cursor always wins, "ccdd", "c c d d" and "id + id * id" all
 * tokenise with no special cases.  Returns 0 after reporting an illegal
 * symbol. */
static int tokenize(const char *text)
{
    int p = 0;

    ntok = 0;
    while (text[p] != '\0') {
        int best = -1, bestLen = 0, a;
        if (isspace((unsigned char)text[p])) { p++; continue; }
        for (a = 0; a < nsym; a++) {
            int L;
            if (symIsNT[a] || a == endSym) continue;
            L = (int)strlen(symName[a]);
            if (L > bestLen && strncmp(text + p, symName[a], (size_t)L) == 0) {
                best    = a;
                bestLen = L;
            }
        }
        if (best < 0) {
            printf("REJECTED - illegal symbol\n");
            printf("  column %d: '%c' begins no terminal of this grammar,"
                   " so it cannot be tokenised\n", p + 1, text[p]);
            printf("  the terminals of this grammar are: ");
            printTerminals(stdout);
            printf("\n");
            return 0;
        }
        if (ntok >= MAX_TOKENS - 1)
            fatal("input holds more than %d tokens - raise MAX_TOKENS",
                  MAX_TOKENS - 1);
        tok[ntok]  = best;
        tcol[ntok] = p + 1;
        ntok++;
        p += bestLen;
    }
    tok[ntok]  = endSym;                             /* the end marker      */
    tcol[ntok] = p + 1;
    ntok++;
    return 1;
}

static int parse(const char *text, int trace)
{
    int stack[MAX_STACK];
    int top = 0, i = 0, step = 0, k;

    printf("input : \"%s\"\n", text);
    if (!tokenize(text)) return 0;

    printf("tokens: ");
    for (k = 0; k < ntok; k++)
        printf("%s%s", k ? " " : "", symName[tok[k]]);
    printf("\n");
    if (trace) printf("trace :\n");

    stack[0] = 0;
    for (;;) {
        int s = stack[top], a = tok[i];
        switch (actKind[s][a]) {
        case A_SHIFT:
            if (trace)
                printf("  %3d. state %-3d  shift  '%s' (column %d)"
                       "  -> state %d\n",
                       ++step, s, symName[a], tcol[i], actVal[s][a]);
            if (top + 1 >= MAX_STACK)
                fatal("parser stack deeper than %d - raise MAX_STACK",
                      MAX_STACK);
            stack[++top] = actVal[s][a];
            i++;
            break;

        case A_REDUCE: {
            int p = actVal[s][a], g;
            if (trace) {
                printf("  %3d. state %-3d  reduce by (%d) ", ++step, s, p);
                printProduction(stdout, p);
                printf("   [lookahead '%s']\n", symName[a]);
            }
            if (top < G[p].len) fatal("parser stack underflow");
            top -= G[p].len;
            g = gotoTab[stack[top]][G[p].lhs];
            if (g < 0)
                fatal("no GOTO for %s in state %d - table is inconsistent",
                      symName[G[p].lhs], stack[top]);
            stack[++top] = g;
            break;
        }

        case A_ACCEPT:
            if (trace) printf("  %3d. state %-3d  accept\n", ++step, s);
            printf("ACCEPTED - the string is in the language\n");
            return 1;

        default:
            printf("REJECTED - invalid string\n");
            printf("  column %d: symbol '%s' is legal but state %d has no"
                   " action for it\n", tcol[i], symName[a], s);
            printf("  expected one of: ");
            printExpected(stdout, s);
            printf("\n");
            return 0;
        }
    }
}

/* ========================================================================
 * report - everything the generator knows, for a grammar with no input.
 * ======================================================================== */

static void printTable(void)
{
    int i, a;

    printf("  %-6s|", "state");
    for (a = 0; a < nsym; a++) if (!symIsNT[a]) printf(" %-6s", symName[a]);
    printf(" |");
    for (a = 0; a < nsym; a++)
        if (symIsNT[a] && a != augSym) printf(" %-6s", symName[a]);
    printf("\n");

    for (i = 0; i < nstates; i++) {
        printf("  %-6d|", i);
        for (a = 0; a < nsym; a++) {
            char cell[16];
            if (symIsNT[a]) continue;
            switch (actKind[i][a]) {
            case A_SHIFT:  sprintf(cell, "s%d", actVal[i][a]); break;
            case A_REDUCE: sprintf(cell, "r%d", actVal[i][a]); break;
            case A_ACCEPT: strcpy(cell, "acc");                break;
            default:       strcpy(cell, ".");                  break;
            }
            printf(" %-6s", cell);
        }
        printf(" |");
        for (a = 0; a < nsym; a++) {
            char cell[16];
            if (!symIsNT[a] || a == augSym) continue;
            if (gotoTab[i][a] < 0) strcpy(cell, ".");
            else sprintf(cell, "%d", gotoTab[i][a]);
            printf(" %-6s", cell);
        }
        printf("\n");
    }
}

static void report(void)
{
    int i, a, p, k, nt, cores, shown[MAX_STATES];

    printf("================================================================\n");
    printf(" AUGMENTED GRAMMAR  -  %d productions\n", nprod);
    printf("================================================================\n");
    for (p = 0; p < nprod; p++) {
        printf("  (%d)  ", p);
        printProduction(stdout, p);
        printf("\n");
    }

    printf("\n================================================================\n");
    printf(" SYMBOL CLASSIFICATION  -  derived, nothing was declared\n");
    printf("================================================================\n");
    printf("  start symbol          : %s\n", symName[startSym]);
    printf("  augmented start symbol: %s\n", symName[augSym]);
    printf("  end marker            : %s\n", symName[endSym]);
    printf("  non-terminals (appear on some left-hand side):\n   ");
    for (a = 0; a < nsym; a++) if (symIsNT[a]) printf(" %s", symName[a]);
    printf("\n  terminals (everything else):\n   ");
    for (a = 0; a < nsym; a++) if (!symIsNT[a]) printf(" %s", symName[a]);
    printf("\n");

    printf("\n================================================================\n");
    printf(" NULLABLE FLAGS AND FIRST SETS\n");
    printf("================================================================\n");
    for (a = 0; a < nsym; a++) {
        int t, first = 1;
        if (!symIsNT[a]) continue;
        printf("  %-10s nullable=%-3s FIRST = {",
               symName[a], nullable[a] ? "yes" : "no");
        for (t = 0; t < nsym; t++) {
            if (!firstSet[a][t]) continue;
            printf("%s %s", first ? "" : ",", symName[t]);
            first = 0;
        }
        printf(" }\n");
    }
    printf("  (for a terminal a, FIRST(a) = { a })\n");

    printf("\n================================================================\n");
    printf(" CANONICAL LR(1) ITEM SETS  -  %d states\n", nstates);
    printf("================================================================\n");
    for (i = 0; i < nstates; i++) {
        int m;
        printf("  State %d:\n", i);
        for (m = 0; m < states[i].n; m++) {
            printf("    ");
            printItem(stdout, &states[i].items[m]);
            printf("\n");
        }
    }

    printf("\n================================================================\n");
    printf(" TRANSITIONS  (GOTO on a non-terminal, shift on a terminal)\n");
    printf("================================================================\n");
    for (i = 0; i < nstates; i++)
        for (a = 0; a < nsym; a++)
            if (trans[i][a] >= 0)
                printf("  I%-4d -- %-10s --> I%-4d   (%s)\n",
                       i, symName[a], trans[i][a],
                       symIsNT[a] ? "goto" : "shift");

    printf("\n================================================================\n");
    printf(" ACTION / GOTO TABLE   (sN shift, rN reduce by production N,\n");
    printf("                        acc accept, '.' error)\n");
    printf("================================================================\n");
    printTable();

    cores = countCores();
    printf("\n================================================================\n");
    printf(" LALR(1) MERGE  -  LR(1) states that share an LR(0) core\n");
    printf("================================================================\n");
    for (i = 0; i < nstates; i++) shown[i] = 0;
    k = 0;
    for (i = 0; i < nstates; i++) {
        int j, n = 0;
        if (shown[i]) continue;
        printf("  core %-3d <- states", k++);
        for (j = i; j < nstates; j++)
            if (!shown[j] && sameCore(&states[i], &states[j])) {
                shown[j] = 1;
                printf(" %d", j);
                n++;
            }
        printf("%s\n", n > 1 ? "   (merged)" : "");
    }

    nt = 0;
    for (a = 0; a < nsym; a++) if (symIsNT[a]) nt++;

    printf("\n================================================================\n");
    printf(" SUMMARY\n");
    printf("================================================================\n");
    printf("  productions (augmented) : %d\n", nprod);
    printf("  non-terminals           : %d\n", nt);
    printf("  terminals               : %d\n", nsym - nt);
    printf("  canonical LR(1) states  : %d\n", nstates);
    printf("  distinct LR(0) cores    : %d"
           "   = LALR(1) states after merging\n", cores);
    printf("  table conflicts         : %d\n", nconflict);
}

/* ======================================================================== */

static void usage(const char *me)
{
    fprintf(stderr,
        "usage: %s [-t] <grammar-file> [input string]\n"
        "  with no input string : print the grammar, the FIRST sets, the\n"
        "                         LR(1) collection, the tables and the\n"
        "                         LR(1)-vs-LALR(1) state count\n"
        "  -t                   : trace every shift and reduce while parsing\n",
        me);
}

int main(int argc, char **argv)
{
    const char *path = NULL;
    char input[MAX_LINE];
    int  trace = 0, haveInput = 0, used = 0, i;

    input[0] = '\0';
    for (i = 1; i < argc; i++) {
        if (path == NULL) {                 /* flags may precede the grammar */
            if (strcmp(argv[i], "-t") == 0) { trace = 1; continue; }
            if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
                usage(argv[0]);
                return EXIT_SUCCESS;
            }
            if (argv[i][0] == '-' && argv[i][1] != '\0') {
                fprintf(stderr, "lalr_gen: unknown option \"%s\"\n", argv[i]);
                usage(argv[0]);
                return EXIT_FAILURE;
            }
            path = argv[i];
            continue;
        }
        /* everything after the grammar file is the input string, joined with
         * single blanks so both "c c d d" and  c c d d  work */
        {
            int need = (int)strlen(argv[i]) + (used ? 1 : 0);
            if (used + need >= MAX_LINE)
                fatal("input string is longer than %d characters - raise"
                      " MAX_LINE", MAX_LINE - 1);
            if (used) input[used++] = ' ';
            strcpy(input + used, argv[i]);
            used += (int)strlen(argv[i]);
        }
        haveInput = 1;
    }

    if (path == NULL) { usage(argv[0]); return EXIT_FAILURE; }

    loadGrammar(path);
    computeFirst();
    buildCollection();
    buildTables();

    if (!haveInput) {
        report();
        return EXIT_SUCCESS;
    }

    printf("grammar: %s   (%d productions, %d LR(1) states, %d LR(0) cores)\n",
           path, nprod, nstates, countCores());
    return parse(input, trace) ? EXIT_SUCCESS : EXIT_FAILURE;
}
