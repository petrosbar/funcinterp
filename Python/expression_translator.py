import ast
import operator
from numbers import Number
from typing import Callable, Type

BIN_OP_SYMBOL: dict[Type[ast.AST], str] = {
    ast.Add: " + ",
    ast.Sub: " - ",
    ast.Mult: " * ",
    ast.Div: " / ",
    ast.Pow: " ** ",
    ast.Mod: " % ",
    ast.FloorDiv: " // ",
    ast.BitAnd: " & ",
    ast.BitOr: " | ",
}

UNARY_OP_SYMBOL: dict[Type[ast.AST], str] = {
    ast.UAdd: "+",
    ast.USub: "-",
    ast.Not: "~",
}

AST_2_PYTHON_OP: dict[Type[ast.AST], Callable[[Number, Number], Number]] = {
    ast.Add: operator.add,
    ast.Sub: operator.sub,
    ast.Mult: operator.mul,
    ast.Div: operator.truediv,
    ast.Pow: operator.pow,
    ast.Mod: operator.mod,
    ast.FloorDiv: operator.floordiv,
    ast.BitAnd: operator.and_,
    ast.BitOr: operator.or_,
}

BOOL_OP_SYMBOL: dict[Type[ast.AST], str] = {
    ast.And: " & ",
    ast.Or: " | ",
}

COMPARE_OP_SYMBOL: dict[Type[ast.AST], str] = {
    ast.Lt: " < ",
    ast.Gt: " > ",
    ast.Eq: " == ",
    ast.LtE: " <= ",
    ast.GtE: " >= ",
    ast.NotEq: " != ",
    ast.Is: " is ",
    ast.IsNot: " is not ",
}

PYTHON_CASTS_MAP: dict[str, str] = {
    "float": "Float64",
    "int": "Int64",
    "str": "Utf8",
}

PYTHON_METHODS_MAP: dict[str, str] = {
    "lower": "str.to_lowercase",
    "title": "str.to_titlecase",
    "upper": "str.to_uppercase",
}

PYTHON_BUILTINS: dict[str, str] = {
    "abs": "abs",
}


def traverse(expression_tree: list) -> str:
    expression = "("
    for expr in expression_tree:
        if isinstance(expr, list):
            expression += traverse(expr)
        else:
            expression += str(expr)
    return expression + ")"


def pull_out_not(expression: list) -> None:
    """Pull out '~' from every subexpression to avoid redundant parentheses.
    
    This function recursively goes through all sublists (subexpressions)
    and if finds an expression of which the first symbol is "~", it pulls it out
    and makes it a symbol of the outer list.
    """
    if isinstance(expression, list):
        for i, j in enumerate(expression):
            if isinstance(j, list):
                if j[0] == "~":
                    expression.insert(i, j.pop(0))
                else:
                    pull_out_not(j)


def parenthesise(nested_expressions: list) -> str:
    pull_not(nested_expressions)
    return traverse(nested_expressions)[1:-1]


def parse_expression(node):

    if isinstance(node, ast.Name):
        return f'pl.col("{node.id}")'

    if isinstance(node, ast.Constant):
        return str(node.value)

    if isinstance(node, ast.Tuple):
        return f'({", ".join([parse_expression(element) for element in node.elts])})'

    if isinstance(node, ast.UnaryOp):
        un_expr = parse_expression(node.operand)
        if isinstance(node.op, (ast.UAdd, ast.USub)):
            return UNARY_OP_SYMBOL[node.op.__class__] + un_expr
        if isinstance(node.op, ast.Not):
            if isinstance(un_expr, list):
                return [UNARY_OP_SYMBOL[node.op.__class__]] + un_expr
            if isinstance(un_expr, str):
                return UNARY_OP_SYMBOL[node.op.__class__] + un_expr
        return None

    if isinstance(node, ast.Call):
        if isinstance(node.func, ast.Name):
            func = node.func.id
            if func in PYTHON_CASTS_MAP:
                return f'pl.col("{node.args[0].id}").cast(pl.{PYTHON_CASTS_MAP[func]})'
            if func in PYTHON_BUILTINS:
                return f'pl.col("{node.args[0].id}").{PYTHON_BUILTINS[func]}()'
            return None
        if isinstance(node.func, ast.Attribute):
            attr = node.func.attr
            if attr in PYTHON_METHODS_MAP:
                return f'{parse_expression(node.func.value)}.{PYTHON_METHODS_MAP[attr]}()'
            return None
        return f'pl.col("{node.args[0].id}").{func}()'

    if isinstance(node, ast.Compare):
        if len(node.ops + node.comparators) > 2:
            return None
        if isinstance(node.ops[0], ast.In):
            return f"{parse_expression(node.left)}.is_in({parse_expression(node.comparators[0])})"
        if isinstance(node.ops[0], ast.NotIn):
            return f"~{parse_expression(node.left)}.is_in({parse_expression(node.comparators[0])})"
        return [
            parse_expression(node.left),
            COMPARE_OP_SYMBOL.get(node.ops[0].__class__),
            parse_expression(node.comparators[0]),
        ]

    if isinstance(node, ast.BinOp):
        if isinstance(node.left, ast.Constant) and isinstance(node.right, ast.Constant):
            return str(
                AST_2_PYTHON_OP[node.op.__class__](node.left.value, node.right.value)
            )
        return [
            parse_expression(node.left),
            BIN_OP_SYMBOL[node.op.__class__],
            parse_expression(node.right),
        ]

    if isinstance(node, ast.BoolOp):
        parse_operands = [parse_expression(i) for i in node.values]
        for index in range(1, len(parse_operands) * 2 - 1, 2):
            parse_operands.insert(index, BOOL_OP_SYMBOL[node.op.__class__])
        return parse_operands
    # after this function returns, flatten the list and check for
    # None. If there's any, expression cannot be native.
    return None
