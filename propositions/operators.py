# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    # Task 3.5

    root = formula.root

    if is_variable(root):
        return formula

    if is_constant(root):
        p = Formula('p')
        if root == 'T':
            return Formula('|', p, Formula('~', p))
        else:
            return Formula('&', p, Formula('~', p))

    if is_unary(root):
        return Formula('~', to_not_and_or(formula.first))

    left = to_not_and_or(formula.first)
    right = to_not_and_or(formula.second)

    if root == '&' or root == '|':
        return Formula(root, left, right)

    if root == '->':
        return Formula('|', Formula('~', left), right)

    if root == '+':
        return Formula('|', Formula('&', left, Formula('~', right)), Formula('&', Formula('~', left), right))

    if root == '<->':
        return Formula('|', Formula('&', left, right), Formula('&', Formula('~', left), Formula('~', right)))

    if root == '-&':
        return Formula('~', Formula('&', left, right))

    if root == '-|':
        return Formula('~', Formula('|', left, right))


def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a

    root = formula.root

    if is_variable(root):
        return formula

    if is_constant(root):
        p = Formula('p')
        if root == 'T':
            return Formula('~', Formula('&', p, Formula('~', p)))
        return Formula('&', p, Formula('~', p))

    if is_unary(root):
        return Formula('~', to_not_and(formula.first))

    left = to_not_and(formula.first)
    right = to_not_and(formula.second)

    if root == '&':
        return Formula('&', left, right)

    if root == '|':
        return Formula('~', Formula('&', Formula('~', left), Formula('~', right)))

    if root == '->':
        return to_not_and(Formula('|', Formula('~', formula.first), formula.second))

    if root == '+':
        return to_not_and(Formula('|', Formula('&', formula.first, Formula('~', formula.second)), Formula('&', Formula('~', formula.first), formula.second)))

    if root == '<->':
        return to_not_and(
            Formula('|', Formula('&', formula.first, formula.second), Formula('&', Formula('~', formula.first), Formula('~', formula.second))))

    if root == '-&':
        return Formula('~', Formula('&', left, right))

    if root == '-|':
        return to_not_and(Formula('~', Formula('|', formula.first, formula.second)))
    return formula


def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b

    root = formula.root

    if is_variable(root):
        return formula

    if is_constant(root):
        p = Formula('p')
        if root == 'T':
            return Formula('-&',
                           Formula('-&', p, p),
                           Formula('-&', p, p))
        return Formula('-&', p, Formula('-&', p, p))

    if is_unary(root):
        inner = to_nand(formula.first)
        return Formula('-&', inner, inner)

    left = to_nand(formula.first)
    right = to_nand(formula.second)

    if root == '&':
        nand = Formula('-&', left, right)
        return Formula('-&', nand, nand)

    if root == '|':
        left_not = Formula('-&', left, left)
        right_not = Formula('-&', right, right)
        return Formula('-&', left_not, right_not)

    if root == '->':
        not_left = Formula('-&', left, left)
        return Formula('-&', not_left, right)

    if root == '+':
        a_or_b = to_nand(Formula('|', formula.first, formula.second))
        a_and_b = to_nand(Formula('&', formula.first, formula.second))
        not_and = Formula('-&', a_and_b, a_and_b)
        return to_nand(Formula('&', a_or_b, not_and))

    if root == '<->':
        xor = to_nand(Formula('+', formula.first, formula.second))
        return Formula('-&', xor, xor)

    if root == '-&':
        return Formula('-&', left, right)

    if root == '-|':
        or_formula = to_nand(Formula('|', formula.first, formula.second))
        return Formula('-&', or_formula, or_formula)

    return formula


def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c

    root = formula.root

    if is_variable(root):
        return formula

    if is_constant(root):
        p = Formula('p')
        if root == 'T':
            return Formula('->', p, p)
        return Formula('~', Formula('->', p, p))

    if is_unary(root):
        return Formula('~', to_implies_not(formula.first))

    left = to_implies_not(formula.first)
    right = to_implies_not(formula.second)

    if root == '->':
        return Formula('->', left, right)

    if root == '&':
        return Formula('~', Formula('->', left, Formula('~', right)))

    if root == '|':
        return Formula('->', Formula('~', left), right)

    if root == '+':
        return to_implies_not(
            Formula('|', Formula('&', formula.first, Formula('~', formula.second)), Formula('&', Formula('~', formula.first), formula.second)))

    if root == '<->':
        return to_implies_not(Formula('|', Formula('&', formula.first, formula.second), Formula('&', Formula('~', formula.first), Formula('~', formula.second))))

    if root == '-&':
        return to_implies_not(Formula('~', Formula('&', formula.first, formula.second)))

    if root == '-|':
        return to_implies_not(Formula('~', Formula('|', formula.first, formula.second)))

    return formula


def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d

    root = formula.root

    if is_variable(root):
        return formula

    if is_constant(root):
        if root == 'F':
            return Formula('F')
        return Formula('->', Formula('F'), Formula('F'))

    if is_unary(root):
        inner = to_implies_false(formula.first)
        return Formula('->', inner, Formula('F'))

    left = to_implies_false(formula.first)
    right = to_implies_false(formula.second)

    if root == '->':
        return Formula('->', left, right)

    if root == '&':
        return Formula('->', Formula('->', left, Formula('->', right, Formula('F'))), Formula('F'))

    if root == '|':
        return Formula('->', Formula('->', left, Formula('F')), right)

    if root == '+':
        return to_implies_false(Formula('|', Formula('&', formula.first, Formula('~', formula.second)),
                                        Formula('&', Formula('~', formula.first), formula.second)))

    if root == '<->':
        return to_implies_false(Formula('|', Formula('&', formula.first, formula.second),
                                        Formula('&', Formula('~', formula.first), Formula('~', formula.second))))

    if root == '-&':
        return to_implies_false(Formula('~', Formula('&', formula.first, formula.second)))

    if root == '-|':
        return to_implies_false(Formula('~', Formula('|', formula.first, formula.second)))

    return formula
