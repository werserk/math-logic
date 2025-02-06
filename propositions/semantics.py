# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""

from itertools import product
from typing import Iterable

from propositions.proofs import *

#: A model for propositional-logic formulas, a mapping from variable names to
#: truth values.
Model = Mapping[str, bool]


def is_model(model: Model) -> bool:
    """Checks if the given dictionary is a model over some set of variable
    names.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variable
        names, ``False`` otherwise.
    """
    for key in model:
        if not is_variable(key):
            return False
    return True


def variables(model: Model) -> AbstractSet[str]:
    """Finds all variable names over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variable names over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()


def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variable names of the
            given formula, to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.

    Examples:
        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': False})
        True

        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': True})
        False
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    if is_variable(formula.root):
        return model[formula.root]
    elif is_constant(formula.root):
        return True if formula.root == "T" else False
    elif is_unary(formula.root):
        return not evaluate(formula.first, model)
    else:
        left_val = evaluate(formula.first, model)
        right_val = evaluate(formula.second, model)
        if formula.root == "&":
            return left_val and right_val
        elif formula.root == "|":
            return left_val or right_val
        elif formula.root == "->":
            return (not left_val) or right_val
        elif formula.root == "+":
            return (left_val and not right_val) or (not left_val and right_val)
        elif formula.root == "<->":
            return left_val == right_val
        elif formula.root == "-&":
            return not (left_val and right_val)
        elif formula.root == "-|":
            return not (left_val or right_val)
        else:
            raise Exception("Неизвестный оператор: " + formula.root)


def all_models(variables: Sequence[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variable names.

    Task 2.2: Перебирает все комбинации значений (False < True) по заданным переменным.
    """
    for v in variables:
        assert is_variable(v)
    for values in product([False, True], repeat=len(variables)):
        yield {v: val for v, val in zip(variables, values)}


def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    models.

    Parameters:
        formula: formula to calculate the truth value of.
        models: iterable over models to calculate the truth value in.

    Task 2.3.
    """
    return (evaluate(formula, model) for model in models)


def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula with variable‐name columns sorted alphabetically.

    Task 2.4.
    """
    vars_sorted = sorted(formula.variables())
    headers = list(vars_sorted) + [str(formula)]
    widths = [max(len(h), 1) for h in headers]

    def format_cell(text, width):
        return f" {text:^{width}} "

    header_line = "|" + "|".join(format_cell(h, w) for h, w in zip(headers, widths)) + "|"
    separator_line = "|" + "|".join("-" * (w + 2) for w in widths) + "|"
    print(header_line)
    print(separator_line)
    models_list = list(all_models(vars_sorted))
    for model in models_list:
        row_cells = [format_cell("T" if model[v] else "F", w) for v, w in zip(vars_sorted, widths[:-1])]
        formula_val = "T" if evaluate(formula, model) else "F"
        row_cells.append(format_cell(formula_val, widths[-1]))
        row_line = "|" + "|".join(row_cells) + "|"
        print(row_line)


def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Task 2.5a.
    """
    vars_list = sorted(formula.variables())
    return all(evaluate(formula, model) for model in all_models(vars_list))


def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Task 2.5b.
    """
    vars_list = sorted(formula.variables())
    return all(not evaluate(formula, model) for model in all_models(vars_list))


def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Task 2.5c.
    """
    vars_list = sorted(formula.variables())
    return any(evaluate(formula, model) for model in all_models(vars_list))


def _synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single conjunctive
    clause that evaluates to ``True`` in the given model, and to ``False`` in
    any other model over the same variable names.

    Task 2.6.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    literals = []
    for v in sorted(model.keys()):
        if model[v]:
            literals.append(Formula(v))
        else:
            literals.append(Formula("~", Formula(v)))
    if len(literals) == 1:
        return literals[0]
    conj = Formula("&", literals[0], literals[1])
    for lit in literals[2:]:
        conj = Formula("&", conj, lit)
    return conj


def synthesize(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variable names,
    that has the specified truth table.

    Task 2.7.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    models_list = list(all_models(variables))
    dnf_clauses = []
    for model, truth in zip(models_list, values):
        if truth:
            dnf_clauses.append(_synthesize_for_model(model))
    if not dnf_clauses:
        p = variables[0]
        return Formula("&", Formula("~", Formula(p)), Formula(p))
    if len(dnf_clauses) == 1:
        return dnf_clauses[0]
    disj = Formula("|", dnf_clauses[0], dnf_clauses[1])
    for clause in dnf_clauses[2:]:
        disj = Formula("|", disj, clause)
    return disj


def _synthesize_for_all_except_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single disjunctive
    clause that evaluates to ``False`` in the given model, and to ``True`` in
    any other model over the same variable names.

    Parameters:
        model: model over a nonempty set of variable names, in which the
            synthesized formula is to not hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    # Optional Task 2.8


def synthesize_cnf(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in CNF over the given variable names,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variable names for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variable names, in the order returned
            by `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize_cnf(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Optional Task 2.9


def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.

    Examples:
        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': True, 'q': False})
        False

        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': False, 'q': False})
        True
    """
    assert is_model(model)
    # Task 4.2


def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3
