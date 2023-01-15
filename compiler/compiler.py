# A verification key generator for a simple zk language, reverse-engineered
# to match https://zkrepl.dev/ output

from utils import *
from .assembly import *
from .utils import *
from setup import Setup
from verifier import VerificationKey
from typing import Optional, Set

def make_s_polynomials(group_order: int, gates: list[GateWires]) -> dict[Column, list[Optional[f_inner]]]:
    if len(gates) > group_order:
        raise Exception("Group order too small")

    # For each variable, extract the list of (column, row) positions
    # where that variable is used
    variable_uses: dict[Optional[str], Set[Cell]] = {None: set()}
    for row, wires in enumerate(gates):
        for column, value in zip(Column.variants(), wires.as_list()):
            if value not in variable_uses:
                variable_uses[value] = set()
            variable_uses[value].add(Cell(column, row))

    # Mark unused cells
    for row in range(len(gates), group_order):
        for column in (Column.variants()):
            variable_uses[None].add(Cell(column, row))

    # For each list of positions, rotate by one.
    # 
    # For example, if some variable is used in positions
    # (LEFT, 4), (LEFT, 7) and (OUTPUT, 2), then we store:
    #
    # at S[LEFT][7] the field element representing (LEFT, 4)
    # at S[OUTPUT][2] the field element representing (LEFT, 7)
    # at S[LEFT][4] the field element representing (OUTPUT, 2)

    S = {
        Column.LEFT: [None] * group_order,
        Column.RIGHT: [None] * group_order,
        Column.OUTPUT: [None] * group_order,
    }

    for _, uses in variable_uses.items():
        sorted_uses = sorted(uses)
        for i, cell in enumerate(sorted_uses):
            next_i = (i+1) % len(sorted_uses)
            next_column = sorted_uses[next_i].column
            next_row = sorted_uses[next_i].row
            S[next_column][next_row] = cell.label(group_order)

    return S

# Generate the gate polynomials: L, R, M, O, C,
# each a list of length `group_order` 
def make_gate_polynomials(group_order: int, eqs: list[AssemblyEqn]) -> tuple[list[f_inner], list[f_inner], list[f_inner], list[f_inner], list[f_inner]]:
    L = [f_inner(0) for _ in range(group_order)]
    R = [f_inner(0) for _ in range(group_order)]
    M = [f_inner(0) for _ in range(group_order)]
    O = [f_inner(0) for _ in range(group_order)]
    C = [f_inner(0) for _ in range(group_order)]
    for i, eq in enumerate(eqs):
        gate = eq.gate()
        L[i] = gate.L
        R[i] = gate.R
        M[i] = gate.M
        O[i] = gate.O
        C[i] = gate.C
    return L, R, M, O, C

# Get the list of public variable assignments, in order
def get_public_assignments(coeffs: list[dict[Optional[str], int]]) -> list[Optional[str]]:
    o = []
    no_more_allowed = False
    for coeff in coeffs:
        if coeff.get('$public', False) is True:
            if no_more_allowed:
                raise Exception("Public var declarations must be at the top")
            var_name = [x for x in list(coeff.keys()) if '$' not in x][0]
            if coeff != {'$public': True, '$output_coeff': 0, var_name: -1}:
                raise Exception("Malformatted coeffs: {}",format(coeffs))
            o.append(var_name)
        else:
            no_more_allowed = True
    return o

# Generate the verification key with the given setup, group order and equations
def make_verification_key(setup: Setup, group_order: int, code: list[str]):
    eqs = to_assembly(code)
    if len(eqs) > group_order:
        raise Exception("Group order too small")
    L, R, M, O, C = make_gate_polynomials(group_order, eqs)
    S = make_s_polynomials(group_order, [eq.wires for eq in eqs])
    return VerificationKey(
        setup.evaluations_to_point(M),
        setup.evaluations_to_point(L),
        setup.evaluations_to_point(R),
        setup.evaluations_to_point(O),
        setup.evaluations_to_point(C),
        setup.evaluations_to_point(S[Column.LEFT]),
        setup.evaluations_to_point(S[Column.RIGHT]),
        setup.evaluations_to_point(S[Column.OUTPUT]),
        setup.X2,
        get_root_of_unity(group_order)
    )
