#!/usr/bin/env python3
"""mmverify.py -- Proof verifier for the Metamath language
Copyright (C) 2002 Raph Levien raph (at) acm (dot) org
Copyright (C) David A. Wheeler and mmverify.py contributors

This program is free software distributed under the MIT license;
see the file LICENSE for full license information.
SPDX-License-Identifier: MIT

To run the program, type
  $ python3 mmverify.py set.mm --logfile set.log
and set.log will have the verification results.  One can also use bash
redirections and type '$ python3 mmverify.py < set.mm 2> set.log' but this
would fail in case 'set.mm' contains (directly or not) a recursive inclusion
statement $[ set.mm $] .

To get help on the program usage, type
  $ python3 mmverify.py -h

(nm 27-Jun-2005) mmverify.py requires that a $f hypothesis must not occur
after a $e hypothesis in the same scope, even though this is allowed by
the Metamath spec.  This is not a serious limitation since it can be
met by rearranging the hypothesis order.
(rl 2-Oct-2006) removed extraneous line found by Jason Orendorff
(sf 27-Jan-2013) ported to Python 3, added support for compressed proofs
and file inclusion
(bj 3-Apr-2022) streamlined code; obtained significant speedup (4x on set.mm)
by verifying compressed proofs without converting them to normal proof format;
added type hints
(am 29-May-2023) added typeguards
(am 23-Dec-2023) made code pass pylint and types pass mypy
"""

import sys
import itertools
import pathlib
import argparse
import typing
import io

Label = str
Var = str
Const = str
Stmttype = typing.Literal["$c", "$v", "$f", "$e", "$a", "$p", "$d", "$="]
StringOption = typing.Optional[str]
Symbol = typing.Union[Var, Const]
Stmt = list[Symbol]
Ehyp = Stmt
Fhyp = tuple[Var, Const]
Dv = tuple[Var, Var]
class Assertion(typing.NamedTuple):
    """A quadruple (disjoint variable conditions, floating
    hypotheses, essential hypotheses, conclusion) describing the given
    assertion.
    """
    dvs: set[Dv]
    f_hyps: list[Fhyp]
    e_hyps: list[Ehyp]
    stmt: Stmt
FullStmt = tuple[Stmttype, typing.Union[Stmt, Assertion]]

def is_hypothesis(stmt: FullStmt) -> typing.TypeGuard[tuple[Stmttype, Stmt]]:
    """The second component of a FullStmt is a Stmt when its first
    component is '$e' or '$f'."""
    return stmt[0] in ('$e', '$f')

def is_assertion(stmt: FullStmt) -> typing.TypeGuard[tuple[Stmttype, Assertion]]:
    """The second component of a FullStmt is an Assertion if its first
    component is '$a' or '$p'."""
    return stmt[0] in ('$a', '$p')

# Note: a script at github.com/metamath/set.mm removes from the following code
# the lines beginning with (spaces followed by) 'vprint(' using the command
#   $ sed -E '/^ *vprint\(/d' mmverify.py > mmverify.faster.py
# In order that mmverify.faster.py be valid, one must therefore not break
# 'vprint' commands over multiple lines, nor have indented blocs containing
# only vprint lines (this would create ill-indented files).


class MMError(Exception):
    """Class of Metamath errors."""


class MMKeyError(MMError, KeyError):
    """Class of Metamath key errors."""


def vprint(vlevel: int, *arguments: typing.Any) -> None:
    """Print log message if verbosity level is higher than the argument."""
    if verbosity >= vlevel:
        print(*arguments, file=logfile)


class Toks:
    """Class of sets of tokens from which functions read as in an input
    stream.
    """

    def __init__(self, file: io.TextIOWrapper) -> None:
        """Construct a 'Toks' from the given file: initialize a line buffer
        containing the lines of the file, and initialize a set of imported
        files to a singleton containing that file, so as to avoid multiple
        imports.
        """
        self.files_buf = [file]
        self.tokbuf: list[str] = []
        self.imported_files = set({pathlib.Path(file.name).resolve()})

    def read(self) -> StringOption:
        """Read the next token in the token buffer, or if it is empty, split
        the next line into tokens and read from it."""
        while not self.tokbuf:
            if self.files_buf:
                line = self.files_buf[-1].readline()
            else:
                # There is no file to read from: this can only happen if end
                # of file is reached while within a ${ ... $} block.
                raise MMError("Unclosed ${ ... $} block at end of file.")
            if line:  # split the line into a list of tokens
                self.tokbuf = line.split()
                self.tokbuf.reverse()
            else:  # no line: end of current file
                self.files_buf.pop().close()
                if not self.files_buf:
                    return None  # End of database
        tok = self.tokbuf.pop()
        vprint(90, "Token:", tok)
        return tok

    def readf(self) -> StringOption:
        """Read the next token once included files have been expanded.  In the
        latter case, the path/name of the expanded file is added to the set of
        imported files so as to avoid multiple imports.
        """
        tok = self.read()
        while tok == '$[':
            filename = self.read()
            if not filename:
                raise MMError(
                    "Unclosed inclusion statement at end of file.")
            endbracket = self.read()
            if endbracket != '$]':
                raise MMError(
                    f"Inclusion statement for file {filename} not " +
                    "closed with a '$]'.")
            file = pathlib.Path(filename).resolve()
            if file not in self.imported_files:
                # wrap the rest of the line after the inclusion command in a
                # file object
                self.files_buf.append(
                    io.StringIO(
                        " ".join(
                            reversed(
                                self.tokbuf))))
                self.tokbuf = []
                with open(file, mode='r', encoding='ascii') as cursor:
                    self.files_buf.append(cursor)
                self.imported_files.add(file)
                vprint(5, 'Importing file:', filename)
            tok = self.read()
        vprint(80, "Token once included files expanded:", tok)
        return tok

    def readc(self) -> StringOption:
        """Read the next token once included files have been expanded and
        comments have been skipped.
        """
        tok = self.readf()
        while tok == '$(':
            # Note that we use 'read' in this while-loop, and not 'readf',
            # since inclusion statements within a comment are still comments
            # so should be skipped.
            # The following line is not necessary but makes things clearer;
            # note the similarity with the first three lines of 'readf'.
            tok = self.read()
            while tok and tok != '$)':
                if '$(' in tok or '$)' in tok:
                    raise MMError(
                        f"Encountered token '{tok}' while reading a comment. " +
                        "Comment contents should not contain '$(' nor " +
                        "'$)' as a substring.  In particular, comments " +
                        "should not nest.")
                tok = self.read()
            if not tok:
                raise MMError("Unclosed comment at end of file.")
            assert tok == '$)'
            # 'readf' since an inclusion may follow a comment immediately
            tok = self.readf()
        vprint(70, "Token once comments skipped:", tok)
        return tok


class Frame:
    """Class of frames, keeping track of the environment."""

    def __init__(self) -> None:
        """Construct an empty frame."""
        self.var: set[Var] = set()
        self.disjoint: set[Dv] = set()
        self.floating: list[Fhyp] = []
        self.f_labels: dict[Var, Label] = {}
        self.essential: list[Ehyp] = []
        self.e_labels: dict[tuple[Symbol, ...], Label] = {}
        # Note: both self.essential and self.e_labels are needed since the keys of
        # self.e_labels form a set, but the order and repetitions of self.essential
        # are needed.

    def add_e(self, stmt: Stmt, label: Label) -> None:
        """Add an essential hypothesis (token tuple)."""
        self.essential.append(stmt)
        self.e_labels[tuple(stmt)] = label
        # conversion to tuple since dictionary keys must be hashable

    def add_d(self, varlist: list[Var]) -> None:
        """Add a disjoint variable condition (ordered pair of variables)."""
        self.disjoint.update((min(x, y), max(x, y))
                          for x, y in itertools.product(varlist, varlist)
                          if x != y)

class FrameStack(list[Frame]):
    """Class of frame stacks, which extends lists (considered and used as
    stacks).
    """

    def push(self) -> None:
        """Push an empty frame to the stack."""
        self.append(Frame())

    def add_e(self, stmt: Stmt, label: Label) -> None:
        """Add an essential hypothesis (token tuple) to the frame stack
        top.
        """
        self[-1].add_e(stmt, label)

    def add_d(self, varlist: list[Var]) -> None:
        """Add a disjoint variable condition (ordered pair of variables) to
        the frame stack top.
        """
        self[-1].add_d(varlist)

    def lookup_v(self, tok: Var) -> bool:
        """Return whether the given token is an active variable."""
        return any(tok in fr.var for fr in self)

    def lookup_d(self, x_var: Var, y_var: Var) -> bool:
        """Return whether the given ordered pair of tokens belongs to an
        active disjoint variable statement.
        """
        return any((min(x_var, y_var), max(x_var, y_var)) in fr.disjoint for fr in self)

    def lookup_f(self, var: Var) -> typing.Optional[Label]:
        """Return the label of the active floating hypothesis which types the
        given variable.
        """
        for frame in self:
            try:
                return frame.f_labels[var]
            except KeyError:
                pass
        return None  # Variable is not actively typed

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

    def find_vars(self, stmt: Stmt) -> set[Var]:
        """Return the set of variables in the given statement."""
        return {x for x in stmt if self.lookup_v(x)}

    def make_assertion(self, stmt: Stmt) -> Assertion:
        """Return a quadruple (disjoint variable conditions, floating
        hypotheses, essential hypotheses, conclusion) describing the given
        assertion.
        """
        e_hyps = [eh for fr in self for eh in fr.essential]
        mand_vars = {tok for hyp in itertools.chain(e_hyps, [stmt])
                     for tok in hyp if self.lookup_v(tok)}
        dvs = {(x, y) for fr in self for (x, y)
               in fr.disjoint if x in mand_vars and y in mand_vars}
        f_hyps = []
        for frame in self:
            for typecode, var in frame.floating:
                if var in mand_vars:
                    f_hyps.append((typecode, var))
                    mand_vars.remove(var)
        assertion = Assertion(dvs, f_hyps, e_hyps, stmt)
        vprint(18, 'Make assertion:', assertion)
        return assertion


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
    vprint(20, 'Applying subst', subst, 'to stmt', stmt, ':', result)
    return result


class MM:
    """Class of ("abstract syntax trees" describing) Metamath databases."""

    def __init__(self, begin_label: Label, stop_label: Label) -> None:
        """Construct an empty Metamath database."""
        self.constants: set[Const] = set()
        self.framestack = FrameStack()
        self.labels: dict[Label, FullStmt] = {}
        self.begin_label = begin_label
        self.stop_label = stop_label
        self.verify_proofs = not self.begin_label

    def add_c(self, tok: Const) -> None:
        """Add a constant to the database."""
        if tok in self.constants:
            raise MMError(
                f'Constant already declared: {tok}')
        if self.framestack.lookup_v(tok):
            raise MMError(
                f'Trying to declare as a constant an active variable: {tok}')
        self.constants.add(tok)

    def add_v(self, tok: Var) -> None:
        """Add a variable to the frame stack top (that is, the current frame)
        of the database.  Allow local variable declarations.
        """
        if self.framestack.lookup_v(tok):
            raise MMError(f'var already declared and active: {tok}')
        if tok in self.constants:
            raise MMError(
                f'var already declared as constant: {tok}')
        self.framestack[-1].var.add(tok)

    def add_f(self, typecode: Const, var: Var, label: Label) -> None:
        """Add a floating hypothesis (ordered pair (variable, typecode)) to
        the frame stack top (that is, the current frame) of the database.
        """
        if not self.framestack.lookup_v(var):
            raise MMError(f'var in $f not declared: {var}')
        if typecode not in self.constants:
            raise MMError(f'typecode in $f not declared: {typecode}')
        if any(var in fr.f_labels for fr in self.framestack):
            raise MMError(
                "var in $f already typed by an active " +
                f"$f-statement: {var}")
        frame = self.framestack[-1]
        frame.floating.append((typecode, var))
        frame.f_labels[var] = label

    def readstmt_aux(
            self,
            stmttype: Stmttype,
            toks: Toks,
            end_token: str) -> Stmt:
        """Read tokens from the input (assumed to be at the beginning of a
        statement) and return the list of tokens until the end_token
        (typically "$=" or "$.").
        """
        stmt = []
        tok = toks.readc()
        while tok and tok != end_token:
            is_active_var = self.framestack.lookup_v(tok)
            if stmttype in {'$d', '$e', '$a', '$p'} and not (
                    tok in self.constants or is_active_var):
                raise MMError(
                    f"Token {tok} is not an active symbol")
            if stmttype in {
                '$e',
                '$a',
                    '$p'} and is_active_var and not self.framestack.lookup_f(tok):
                raise MMError(f"Variable {tok} in {stmttype}-statement is not typed " +
                              "by an active $f-statement).")
            stmt.append(tok)
            tok = toks.readc()
        if not tok:
            raise MMError(
                f"Unclosed {stmttype}-statement at end of file.")
        assert tok == end_token
        vprint(20, 'Statement:', stmt)
        return stmt

    def read_non_p_stmt(self, stmttype: Stmttype, toks: Toks) -> Stmt:
        """Read tokens from the input (assumed to be at the beginning of a
        non-$p-statement) and return the list of tokens until the next
        end-statement token '$.'.
        """
        return self.readstmt_aux(stmttype, toks, end_token="$.")

    def read_p_stmt(self, toks: Toks) -> tuple[Stmt, Stmt]:
        """Read tokens from the input (assumed to be at the beginning of a
        p-statement) and return the couple of lists of tokens (stmt, proof)
        appearing in "$p stmt $= proof $.".
        """
        stmt = self.readstmt_aux("$p", toks, end_token="$=")
        proof = self.readstmt_aux("$=", toks, end_token="$.")
        return stmt, proof

    def read_cvfe(self, tok: str, toks: Toks, label):
        """Read constant, variable, floating hypothesis, or essential
        hypothesis from the given token list to update the database and
        verify its proofs.
        """
        match tok:
            case '$c':
                for tok_c in self.read_non_p_stmt('$c', toks):
                    self.add_c(tok_c)
            case '$v':
                for tok_v in self.read_non_p_stmt('$v', toks):
                    self.add_v(tok_v)
            case '$f':
                stmt = self.read_non_p_stmt('$f', toks)
                if not label:
                    raise MMError(
                        f'$f must have label (statement: {stmt})')
                if len(stmt) != 2:
                    raise MMError(
                        f'$f must have length two but is {stmt}')
                self.add_f(stmt[0], stmt[1], label)
                self.labels[label] = ('$f', [stmt[0], stmt[1]])
                label = None
            case '$e':
                if not label:
                    raise MMError('$e must have label')
                stmt = self.read_non_p_stmt('$e', toks)
                self.framestack.add_e(stmt, label)
                self.labels[label] = ('$e', stmt)
                label = None

    def read_stmt_or_proof(self, tok: str, toks: Toks, label):
        """Read constant, variable, floating hypothesis, essential
        hypothesis, assertion, or disjoint variable condition from the
        given token list to update the database and verify its proofs.
        """
        match tok:
            case '$c' | '$v' | '$f' | '$e':
                self.read_cvfe(tok, toks, label)
            case '$a':
                if not label:
                    raise MMError('$a must have label')
                self.labels[label] = (
                    '$a', self.framestack.make_assertion(
                        self.read_non_p_stmt('$a', toks)))
                label = None
            case '$p':
                if not label:
                    raise MMError('$p must have label')
                stmt, proof = self.read_p_stmt(toks)
                assertion = self.framestack.make_assertion(stmt)
                if self.verify_proofs:
                    vprint(2, 'Verify:', label)
                    self.verify(assertion.f_hyps, assertion.e_hyps, assertion.stmt, proof)
                self.labels[label] = ('$p', assertion)
                label = None
            case '$d':
                self.framestack.add_d(self.read_non_p_stmt('$d', toks))

    def read(self, toks: Toks) -> None:
        """Read the given token list to update the database and verify its
        proofs.
        """
        self.framestack.push()
        label = None
        tok = toks.readc()
        try:
            while tok and tok != '$}':
                match tok:
                    case '$c' | '$v' | '$f' | '$e' | '$a' | '$p' | '$d':
                        self.read_stmt_or_proof(tok, toks, label)
                    case '${':
                        self.read(toks)
                    case '$)':
                        raise MMError("Unexpected '$)' while not within a comment")
                    case _:
                        if tok[0] != '$':
                            if tok in self.labels:
                                raise MMError(f'Label {tok} multiply defined.')
                            label = tok
                            vprint(20, 'Label:', label)
                            if label == self.stop_label:
                                # exit gracefully the nested calls to self.read()
                                sys.exit(0)
                            if label == self.begin_label:
                                self.verify_proofs = True
                        else:
                            raise MMError(f"Unknown token: '{tok}'.")
                tok = toks.readc()
        except SystemExit as exit_err:
            raise exit_err
        finally:
            self.framestack.pop()

    def treat_step(self,
                   step: FullStmt,
                   stack: list[Stmt]) -> None:
        """Carry out the given proof step (given the label to treat and the
        current proof stack).  This modifies the given stack in place.
        """
        vprint(10, 'Proof step:', step)
        if is_hypothesis(step):
            stmt = step[1]
            stack.append(stmt)
        elif is_assertion(step):
            assertion = step[1]
            npop = len(assertion.f_hyps) + len(assertion.e_hyps)
            stackpointer = len(stack) - npop
            if stackpointer < 0:
                raise MMError(
                    f"Stack underflow: proof step {step} requires too many " +
                    f"({npop}) hypotheses.")
            subst: dict[Var, Stmt] = {}
            for typecode, var in assertion.f_hyps:
                entry = stack[stackpointer]
                if entry[0] != typecode:
                    raise MMError(
                        f"Proof stack entry {entry} does not match floating " +
                        f"hypothesis ({typecode}, {var}).")
                subst[var] = entry[1:]
                stackpointer += 1
            vprint(15, 'Substitution to apply:', subst)
            for hyp in assertion.e_hyps:
                entry = stack[stackpointer]
                subst_h = apply_subst(hyp, subst)
                if entry != subst_h:
                    raise MMError(f"Proof stack entry {entry} does not match " +
                                  f"essential hypothesis {subst_h}.")
                stackpointer += 1
            self.treat_disjoint_conditions(assertion.dvs, subst)
            del stack[len(stack) - npop:]
            stack.append(apply_subst(assertion.stmt, subst))
        vprint(12, 'Proof stack:', stack)

    def treat_disjoint_conditions(self, dvs, subst) -> None:
        """Carry out the given disjoint variable conditions (given the
        substitution to apply).
        """
        for x_var, y_var in dvs:
            vprint(16, 'dist', x_var, y_var, subst[x_var], subst[y_var])
            x_vars = self.framestack.find_vars(subst[x_var])
            y_vars = self.framestack.find_vars(subst[y_var])
            vprint(16, 'V(x_var) =', x_vars)
            vprint(16, 'V(y_var) =', y_vars)
            for x_var0, y_var0 in itertools.product(x_vars, y_vars):
                if x_var0 == y_var0 or not self.framestack.lookup_d(x_var0, y_var0):
                    raise MMError("Disjoint variable violation: " +
                                  f"{x_var0} , {y_var0}")

    def treat_normal_proof(self, proof: list[str]) -> list[Stmt]:
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
            proof: list[str]) -> list[Stmt]:
        """Return the proof stack once the given compressed proof for an
        assertion with the given $f and $e-hypotheses has been processed.
        """
        # Preprocessing and building the lists of proof_ints and labels
        flabels = [self.framestack.lookup_f(v) for _, v in f_hyps]
        elabels = [self.framestack.lookup_e(s) for s in e_hyps]
        plabels = flabels + elabels  # labels of implicit hypotheses
        idx_bloc = proof.index(')')  # index of end of label bloc
        plabels += proof[1:idx_bloc]  # labels which will be referenced later
        compressed_proof = ''.join(proof[idx_bloc + 1:])
        vprint(5, 'Referenced labels:', plabels)
        label_end = len(plabels)
        vprint(5, 'Number of referenced labels:', label_end)
        vprint(5, 'Compressed proof steps:', compressed_proof)
        vprint(5, 'Number of steps:', len(compressed_proof))
        proof_ints = []  # integers referencing the labels in 'labels'
        cur_int = 0  # counter for radix conversion
        for character in compressed_proof:
            if character == 'Z':
                proof_ints.append(-1)
            elif 'A' <= character <= 'T':
                proof_ints.append(20 * cur_int + ord(character) - 65)  # ord('A') = 65
                cur_int = 0
            else:  # 'U' <= character <= 'Y'
                cur_int = 5 * cur_int + ord(character) - 84  # ord('U') = 85
        vprint(5, 'Integer-coded steps:', proof_ints)

        return self.process_proof(proof_ints, plabels, label_end)

    def process_proof(self, proof_ints, plabels, label_end) -> list[Stmt]:
        """Processing of the proof"""
        stack: list[Stmt] = []  # proof stack
        # statements saved for later reuse (marked with a 'Z')
        saved_stmts = []
        # can be recovered as len(saved_stmts) but less efficient
        n_saved_stmts = 0
        for proof_int in proof_ints:
            if proof_int == -1:  # save the current step for later reuse
                stmt = stack[-1]
                vprint(15, 'Saving step', stmt)
                saved_stmts.append(stmt)
                n_saved_stmts += 1
            elif proof_int < label_end:
                # proof_int denotes an implicit hypothesis or a label in the
                # label bloc
                self.treat_step(self.labels[plabels[proof_int]], stack)
            elif proof_int >= label_end + n_saved_stmts:
                raise MMError(
                    f"Not enough saved proof steps ({n_saved_stmts} saved but calling " +
                    f"the {proof_int}th).")
            else:  # label_end <= proof_int < label_end + n_saved_stmts
                # proof_int denotes an earlier proof step marked with a 'Z'
                # A proof step that has already been proved can be treated as
                # a dv-free and hypothesis-free axiom.
                stmt = saved_stmts[proof_int - label_end]
                vprint(15, 'Reusing step', stmt)
                self.treat_step(
                    ('$a',
                     Assertion(set(), [], [], stmt)),
                    stack)
        return stack

    def verify(
            self,
            f_hyps: list[Fhyp],
            e_hyps: list[Ehyp],
            conclusion: Stmt,
            proof: list[str]) -> None:
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
        vprint(10, 'Stack at end of proof:', stack)
        if not stack:
            raise MMError(
                "Empty stack at end of proof.")
        if len(stack) > 1:
            raise MMError(
                "Stack has more than one entry at end of proof (top " +
                f"entry: {stack[0]} ; proved assertion: {conclusion}).")
        if stack[0] != conclusion:
            raise MMError(f"Stack entry {stack[0]} does not match proved " +
                          f" assertion {conclusion}.")
        vprint(3, 'Correct proof!')

    def dump(self) -> None:
        """Print the labels of the database."""
        print(self.labels)


def parse_args():
    """Parse the arguments."""
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
        help="""label where to begin verifying proofs (included, if it is a
          provable statement)""")
    parser.add_argument(
        '-s',
        '--stop-label',
        dest='stop_label',
        type=str,
        help='label where to stop verifying proofs (not included)')
    return parser.parse_args()

def run(db_file, begin_label, stop_label):
    """Verify the given Metamath database."""
    vprint(1, 'mmverify.py -- Proof verifier for the Metamath language')
    metamath = MM(begin_label, stop_label)
    vprint(1, f'Reading source file "{db_file.name}"...')
    metamath.read(Toks(db_file))
    vprint(1, 'No errors were found.')
    # metamath.dump()

if __name__ == '__main__':
    args = parse_args()
    verbosity = args.verbosity
    logfile = args.logfile

    run(args.database, args.begin_label, args.stop_label)
