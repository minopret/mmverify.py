#!/usr/bin/env python3
# mmverify.py -- Proof verifier for the Metamath language
# Copyright (C) 2002 Raph Levien raph (at) acm (dot) org
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License

# To run the program, type
#   $ python3 mmverify.py set.mm --logfile set.log
# and set.log will have the verification results.  One can also use bash
# redirections and type '$ python3 mmverify.py < set.mm 2> set.log' but this
# would fail in case 'set.mm' contains (directly or not) a recursive inclusion
# statement $[ set.mm $] .
#
# To get help on the program usage, type
#   $ python3 mmverify.py -h

# (nm 27-Jun-2005) mmverify.py requires that a $f hypothesis must not occur
# after a $e hypothesis in the same scope, even though this is allowed by
# the Metamath spec.  This is not a serious limitation since it can be
# met by rearranging the hypothesis order.
# (rl 2-Oct-2006) removed extraneous line found by Jason Orendorff
# (sf 27-Jan-2013) ported to Python 3, added support for compressed proofs
# and file inclusion
# (bj 3-Apr-2022) streamline code and significant speedup (4x) by verifying
# compressed proofs without converting them to normal format

import sys
import itertools
import pathlib
import argparse
import typing
import io

Label = str
Var = str
Const = str
Steptyp = str  # can actually be one of '$e', '$f', '$a', '$p'
StringOption = typing.Optional[str]
Symbol = typing.Union[Var, Const]
Stmt = list[Symbol]
Ehyp = Stmt
Fhyp = tuple[Var, Const]
Dv = tuple[Var, Var]
Assertion = tuple[set[Dv], list[Fhyp], list[Ehyp], Stmt]
FullStmt = tuple[Steptyp, typing.Union[Stmt, Assertion]]
# Actually, the second component of a FullStmt is a Stmt when its first
# component is '$e' or '$f' and an Assertion if its first component is '$a' or
# '$p', but this is a bit cumbersome to build it into the typing system.
# This explains the errors when static type checking (e.g., mypy).


class MMError(Exception):
    """Class of Metamath errors."""
    pass


class MMKeyError(MMError, KeyError):
    """Class of Metamath key errors."""
    pass


def vprint(vlevel: int, *args) -> None:
    """Print log message if verbosity level is higher than the argument."""
    if verbosity >= vlevel:
        print(*args, file=logfile)


class toks:
    """Class of sets of tokens from which functions read as in an input
    stream.
    """

    def __init__(self, file: io.TextIOWrapper) -> None:
        """Construct a 'toks' from the given file: initialize a line buffer
        containing the lines of the file, and initialize a set of imported
        files to a singleton containing that file, so as to avoid multiple
        imports.
        """
        self.lines_buf = [file]
        self.tokbuf: list[str] = []
        self.imported_files = set({pathlib.Path(file.name).resolve()})

    def read(self) -> StringOption:
        """Read the next token in the token buffer, or if it is empty, split
        the next line into tokens and read from it."""
        while not self.tokbuf:
            line = self.lines_buf[-1].readline()
            if not line:
                self.lines_buf.pop().close()
                if not self.lines_buf:
                    return None
            else:
                self.tokbuf = line.split()
                self.tokbuf.reverse()
        return self.tokbuf.pop()

    def readf(self) -> StringOption:
        """Read the next token once included files have been expanded.  In the
        latter case, the path/name of the expanded file is added to the set of
        imported files so as to avoid multiple imports.
        """
        tok = self.read()
        while tok == '$[':
            filename = self.read()
            if not filename:
                raise MMError('Inclusion command not terminated')
            endbracket = self.read()
            if endbracket != '$]':
                raise MMError('Inclusion command not terminated')
            file = pathlib.Path(filename).resolve()
            if file not in self.imported_files:
                self.lines_buf.append(open(file, mode='r', encoding='ascii'))
                self.imported_files.add(file)
                vprint(5, 'Importing file:', filename)
            tok = self.read()
        return tok

    def readc(self) -> StringOption:
        """Read the next token once included files have been expanded and
        ignoring comments.
        """
        while 1:
            tok = self.readf()
            if tok == '$(':
                while tok != '$)':
                    tok = self.read()
            else:
                return tok

    def readstmt(self) -> Stmt:
        """Read tokens from the input (assumed to be at the beginning of a
        statement) and return the list of tokens until the next end-statement
        token '$.'.
        """
        stmt = []
        tok = self.readc()
        while tok != '$.':
            if tok is None:
                raise MMError('EOF before $.')
            stmt.append(tok)
            tok = self.readc()
        return stmt


class Frame:
    """Class of frames, keeping track of the environment."""

    def __init__(self) -> None:
        """Construct an empty frame."""
        self.c: set[Const] = set()
        self.v: set[Var] = set()
        self.d: set[Dv] = set()
        self.f: list[Fhyp] = []
        self.f_labels: dict[Var, Label] = {}
        self.e: list[Ehyp] = []
        self.e_labels: dict[tuple[Symbol], Label] = {}


class FrameStack(list):
    """Class of frame stacks, which extends lists (considered and used as
    stacks).
    """

    def push(self) -> None:
        """Push an empty frame to the stack."""
        self.append(Frame())

    def add_c(self, tok: Const) -> None:
        """Add a constant to the frame stack top.  Allow local definitions."""
        if self.lookup_c(tok):
            raise MMError('const already defined and active')
        if self.lookup_v(tok):
            raise MMError('const already defined as var and active')
        self[-1].c.add(tok)

    def add_v(self, tok: Var) -> None:
        """Add a variable to the frame stack top.  Allow local definitions."""
        if self.lookup_v(tok):
            raise MMError('var already defined and active')
        if self.lookup_c(tok):
            raise MMError('var already defined as const and active')
        self[-1].v.add(tok)

    def add_f(self, var: Var, kind: Const, label: Label) -> None:
        """Add a floating hypothesis (ordered pair (variable, kind)) to the
        frame stack top.
        """
        if not self.lookup_v(var):
            raise MMError('var in $f not defined: {0}'.format(var))
        if not self.lookup_c(kind):
            raise MMError('const in $f not defined {0}'.format(kind))
        frame = self[-1]
        # The following line forbids multiple $f-statements for a given var.
        # If that restriction is removed, then 'make_assertion' should be
        # changed accordingly with the comment there.
        if any(var in fr.f_labels.keys() for fr in self):
            raise MMError('var in $f already typed by an active $f-statement')
        frame.f.append((var, kind))
        frame.f_labels[var] = label

    def add_e(self, stmt: Stmt, label: Label) -> None:
        """Add an essential hypothesis (token tuple) to the frame stack
        top.
        """
        frame = self[-1]
        frame.e.append(stmt)
        frame.e_labels[tuple(stmt)] = label
        # conversion to tuple since dictionary keys must be hashable

    def add_d(self, stmt: Stmt) -> None:
        """Add a disjoint variable condition (ordered pair of variables) to
        the frame stack top.
        """
        varlist = self.find_vars(stmt)
        self[-1].d.update((min(x, y), max(x, y))
                          for x, y in itertools.product(varlist, varlist) if x != y)

    def lookup_c(self, tok: Const) -> bool:
        """Return whether the given token is an active constant."""
        return any(tok in fr.c for fr in self)

    def lookup_v(self, tok: Var) -> bool:
        """Return whether the given token is an active variable."""
        return any(tok in fr.v for fr in self)

    def lookup_d(self, x: Var, y: Var) -> bool:
        """Return whether the given ordered pair of tokens belongs to an
        active disjoint variable statement.
        """
        return any((min(x, y), max(x, y)) in fr.d for fr in self)

    def lookup_f(self, var: Var) -> Label:
        """Return the label of the active floating hypothesis which types the
        given variable.
        """
        for frame in self:
            try:
                return frame.f_labels[var]
            except KeyError:
                pass
        raise MMKeyError(var)

    def lookup_e(self, stmt: Stmt) -> Label:
        """Return the label of the (earliest) active essential hypothesis with
        the given statement.
        """
        stmt_t = tuple(stmt)
        for frame in self:
            try:
                return frame.e_labels[stmt_t]
            except KeyError:
                pass
        raise MMKeyError(stmt_t)

    def find_vars(self, stmt: Stmt) -> list[Var]:
        """Return the list of variables in the given statement."""
        vars = []
        for x in stmt:
            if x not in vars and self.lookup_v(x):
                vars.append(x)
        return vars

    def make_assertion(self, stmt: Stmt) -> Assertion:
        """Return a quadruple (disjoint variable conditions, floating
        hypotheses, essential hypotheses, conclusion) describing the given
        assertion.
        """
        e_hyps = [eh for fr in self for eh in fr.e]
        mand_vars = {tok for hyp in itertools.chain(e_hyps, [stmt])
                     for tok in hyp if self.lookup_v(tok)}
        dvs = {(x, y) for fr in self for (x, y) in
               fr.d.intersection(itertools.product(mand_vars, mand_vars))}
        f_hyps = []
        # If one allows Metamath databases with multiple $f-statements for a
        # given var, then one should use "reversed" in the next two lines and
        # use 'appendleft' from 'collections.deque' to get the latest f_hyp
        # corresponding to the given var.
        # The current version of 'add_f' forbids such multiple $f-statements.
        for fr in self:
            for v, k in fr.f:
                if v in mand_vars:
                    f_hyps.append((k, v))
                    mand_vars.remove(v)
        vprint(18, 'make_assertion:', dvs, f_hyps, e_hyps, stmt)
        return (dvs, f_hyps, e_hyps, stmt)


def apply_subst(stmt: Stmt, subst: dict[Var, Stmt]) -> Stmt:
    """Return the token list resulting from the given substitution
    (dictionary) applied to the given statement (token list).
    """
    result = []
    for tok in stmt:
        if tok in subst:
            result += subst[tok]
        else:
            result.append(tok)
    vprint(20, 'apply_subst:', stmt, subst, '=', result)
    return result


class MM:
    """Class of ("abstract syntax trees" describing) Metamath databases."""

    def __init__(self, begin_label: Label, stop_label: Label) -> None:
        """Construct an empty Metamath database."""
        self.fs = FrameStack()
        self.labels: dict[Label, FullStmt] = {}
        self.begin_label = begin_label
        self.stop_label = stop_label

    def read(self, toks: toks) -> None:
        """Read the given token list to update the database and verify its
        proofs.
        """
        self.fs.push()
        label = None
        tok = toks.readc()
        while tok and tok != '$}':
            if tok == '$c':
                for tok in toks.readstmt():
                    self.fs.add_c(tok)
            elif tok == '$v':
                for tok in toks.readstmt():
                    self.fs.add_v(tok)
            elif tok == '$f':
                stmt = toks.readstmt()
                if not label:
                    raise MMError('$f must have label')
                if len(stmt) != 2:
                    raise MMError('$f must have length 2')
                vprint(15, label, '$f', stmt[0], stmt[1], '$.')
                self.fs.add_f(stmt[1], stmt[0], label)
                self.labels[label] = ('$f', [stmt[0], stmt[1]])
                label = None
            elif tok == '$e':
                if not label:
                    raise MMError('$e must have label')
                stmt = toks.readstmt()
                self.fs.add_e(stmt, label)
                self.labels[label] = ('$e', stmt)
                label = None
            elif tok == '$a':
                if not label:
                    raise MMError('$a must have label')
                if label == self.stop_label:
                    sys.exit(0)
                if label == self.begin_label:
                    self.begin_label = None
                self.labels[label] = ('$a',
                                      self.fs.make_assertion(toks.readstmt()))
                label = None
            elif tok == '$p':
                if not label:
                    raise MMError('$p must have label')
                if label == self.stop_label:
                    sys.exit(0)
                if label == self.begin_label:
                    self.begin_label = None
                stmt = toks.readstmt()
                proof = None
                try:
                    i = stmt.index('$=')
                    proof = stmt[i + 1:]
                    stmt = stmt[:i]
                except ValueError:
                    raise MMError('$p must contain a proof after $=')
                dvs, f_hyps, e_hyps, conclusion = self.fs.make_assertion(stmt)
                if not self.begin_label:
                    vprint(2, 'verifying:', label)
                    self.verify(f_hyps, e_hyps, conclusion, proof)
                self.labels[label] = ('$p', (dvs, f_hyps, e_hyps, conclusion))
                label = None
            elif tok == '$d':
                self.fs.add_d(toks.readstmt())
            elif tok == '${':
                self.read(toks)
            elif tok[0] != '$':
                label = tok
            else:
                print('Unknown token:', tok)
            tok = toks.readc()
        self.fs.pop()

    def treat_step(self,
                   step: FullStmt,
                   stack: list[Stmt]) -> None:
        """Carry out the given proof step (given the label to treat and the
        current proof stack).  This modifies the given stack in place.
        """
        steptyp, stepdat = step
        vprint(10, 'step', steptyp, stepdat)
        if steptyp in ('$e', '$f'):
            stack.append(stepdat)
        elif steptyp in ('$a', '$p'):
            dvs0, f_hyps0, e_hyps0, conclusion0 = stepdat
            vprint(12, stepdat)
            npop = len(f_hyps0) + len(e_hyps0)
            sp = len(stack) - npop
            if sp < 0:
                raise MMError('stack underflow')
            subst: dict[Var, Stmt] = {}
            for k, v in f_hyps0:
                entry = stack[sp]
                if entry[0] != k:
                    raise MMError(
                        ("stack entry {2!s} does not match floating " +
                         "hypothesis ({0}, {1})").format(entry, k, v))
                subst[v] = entry[1:]
                sp += 1
            vprint(15, 'subst:', subst)
            for h in e_hyps0:
                entry = stack[sp]
                subst_h = apply_subst(h, subst)
                if entry != subst_h:
                    raise MMError(("stack entry {0!s} does not match " +
                                   "essential hypothesis {1!s}")
                                  .format(entry, subst_h))
                sp += 1
            for x, y in dvs0:
                vprint(16, 'dist', x, y, subst[x], subst[y])
                x_vars = self.fs.find_vars(subst[x])
                y_vars = self.fs.find_vars(subst[y])
                vprint(16, 'V(x) =', x_vars)
                vprint(16, 'V(y) =', y_vars)
                for x, y in itertools.product(x_vars, y_vars):
                    if x == y or not self.fs.lookup_d(x, y):
                        raise MMError("Disjoint variable violation: " +
                                      "{0} , {1}".format(x, y))
            del stack[len(stack) - npop:]
            stack.append(apply_subst(conclusion0, subst))
        vprint(12, 'stack:', stack)

    def treat_normal_proof(self, proof) -> list[Stmt]:
        """Return the proof stack once the given normal proof has been
        processed.
        """
        stack: list[Stmt] = []
        for label in proof:
            self.treat_step(self.labels[label], stack)
        return stack

    def treat_compressed_proof(
            self,
            f_hyps: list[Fhyp],
            e_hyps: list[Ehyp],
            proof) -> list[Stmt]:
        """Return the proof stack once the given compressed proof for an
        assertion with the given $f and $e-hypotheses has been processed.
        """
        # Preprocessing and building the lists of proof_ints and labels
        f_labels = [self.fs.lookup_f(v) for _, v in f_hyps]
        e_labels = [self.fs.lookup_e(s) for s in e_hyps]
        labels = f_labels + e_labels  # labels of implicit hypotheses
        idx_bloc = proof.index(')')  # index of end of label bloc
        labels += proof[1:idx_bloc]  # labels which will be referenced later
        compressed_proof = ''.join(proof[idx_bloc + 1:])
        vprint(5, 'labels:', labels)
        vprint(5, 'proof:', compressed_proof)
        proof_ints = []  # integers referencing the labels in 'labels'
        cur_int = 0  # counter for radix conversion
        for ch in compressed_proof:
            if ch == 'Z':
                proof_ints.append(-1)
            elif 'A' <= ch and ch <= 'T':
                proof_ints.append(20 * cur_int + ord(ch) - 65)  # ord('A') = 65
                cur_int = 0
            else:  # 'U' <= ch and ch <= 'Y'
                cur_int = 5 * cur_int + ord(ch) - 84  # ord('U') = 85
        vprint(5, 'proof_ints:', proof_ints)
        label_end = len(labels)
        # Processing of the proof
        stack: list[Stmt] = []  # proof stack
        # statements saved for later reuse (marked with a 'Z')
        saved_stmts = []
        for proof_int in proof_ints:
            vprint(10, 'stack:', stack)
            if proof_int == -1:  # save the current step for later
                saved_stmts.append(stack[-1])
            elif 0 <= proof_int and proof_int < label_end:
                # pf_int denotes an implicit hypothesis or a label in the label
                # bloc
                self.treat_step(self.labels[labels[proof_int]], stack)
            elif label_end <= proof_int:
                # pf_int denotes an earlier proof step marked with a 'Z'
                # A proof step that has already been proved can be treated as
                # a dv-free and hypothesis-free axiom.
                self.treat_step(
                    ('$a', (set(), [], [], saved_stmts[proof_int - label_end])), stack)
        return stack

    def verify(
            self,
            f_hyps: list[Fhyp],
            e_hyps: list[Ehyp],
            conclusion: Stmt,
            proof) -> None:
        """Verify that the given proof (in normal or compressed format) is a
        correct proof of the given assertion.
        """
        # It would not be useful to also pass the list of dv conditions of the
        # assertion as an argument since other dv conditions corresponding to
        # dummy variables should be 'lookup_d'ed anyway.
        if proof[0] == '(':  # compressed format
            stack = self.treat_compressed_proof(f_hyps, e_hyps, proof)
        else:  # normal format
            stack = self.treat_normal_proof(proof)
        vprint(10, 'stack at end of proof:', stack)
        if len(stack) != 1:
            raise MMError(
                "Stack has more than one entry at end of proof (top " +
                "entry: {0!s} ; proved assertion: {1!s}).".format(
                    stack[0],
                    conclusion))
        if stack[0] != conclusion:
            raise MMError(("Stack entry {0!s} does not match proved " +
                          " assertion {1!s}").format(stack[0], conclusion))

    def dump(self) -> None:
        """Print the labels of the database."""
        print(self.labels)


if __name__ == '__main__':
    """Parse the arguments and verify the given Metamath database."""
    parser = argparse.ArgumentParser(description="""Verify a Metamath database.
      The grammar of the whole file is verified.  Proofs are verified between
      the statements with labels BEGIN_LABEL (included) and STOP_LABEL (not
      included).

      One can also use bash redirections:
         '$ python3 mmverify.py < file.mm 2> file.log'
      in place of
         '$ python3 mmverify.py file.mm --logfile file.log'
      but this fails in case 'file.mm' contains (directly or not) a recursive
      inclusion statement '$[ file.mm $]'.""")
    parser.add_argument(
        'database',
        nargs='?',
        type=argparse.FileType(
            mode='r',
            encoding='ascii'),
        default=sys.stdin,
        help="""database (Metamath file) to verify, expressed using relative
          path (defaults to <stdin>)""")
    parser.add_argument(
        '-l',
        '--logfile',
        dest='logfile',
        type=argparse.FileType(
            mode='w',
            encoding='ascii'),
        default=sys.stderr,
        help="""file to output logs, expressed using relative path (defaults to
          <stderr>)""")
    parser.add_argument(
        '-v',
        '--verbosity',
        dest='verbosity',
        default=0,
        type=int,
        help='verbosity level (default=0 is mute; higher is more verbose)')
    parser.add_argument(
        '-b',
        '--begin-label',
        dest='begin_label',
        type=str,
        help="""assertion label where to begin verifying proofs (included,
          provided it is a provable statement)""")
    parser.add_argument(
        '-s',
        '--stop-label',
        dest='stop_label',
        type=str,
        help='assertion label where to stop verifying proofs (not included)')
    args = parser.parse_args()
    verbosity = args.verbosity
    db_file = args.database
    logfile = args.logfile
    vprint(1, 'mmverify.py -- Proof verifier for the Metamath language')
    mm = MM(args.begin_label, args.stop_label)
    vprint(1, 'Reading source file "{0}"...'.format(db_file.name))
    mm.read(toks(db_file))
    vprint(1, 'No errors were found.')
    # mm.dump()
