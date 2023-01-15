import compiler.compiler as c
from compiler.assembly import to_assembly
from compiler.utils import get_product_key
import prover as p
import json
from test.mini_poseidon import rc, mds, poseidon_hash
from utils import *
from typing import Optional

# Attempts to "run" the program to fill in any intermediate variable
# assignments, starting from the given assignments. Eg. if
# `starting_assignments` contains {'a': 3, 'b': 5}, and the first line
# says `c <== a * b`, then it fills in `c: 15`.
def fill_variable_assignments(code: list[str], starting_assignments: dict[Optional[str], int]) -> dict[Optional[str], int]:
    out = {k: f_inner(v) for k,v in starting_assignments.items()}
    out[None] = f_inner(0)
    eqs = to_assembly(code)
    for eq in eqs:
        wires = eq.wires
        coeffs = eq.coeffs
        in_L = wires.L
        in_R = wires.R
        output = wires.O
        out_coeff = coeffs.get('$output_coeff', 1)
        product_key = get_product_key(in_L, in_R)
        if output is not None and out_coeff in (-1, 1):
            new_value = f_inner(
                coeffs.get('', 0) +
                out[in_L] * coeffs.get(in_L, 0) +
                out[in_R] * coeffs.get(in_R, 0) * (1 if in_R != in_L else 0) +
                out[in_L] * out[in_R] * coeffs.get(product_key, 0)
            ) * out_coeff # should be / but equivalent for (1, -1)
            if output in out:
                if out[output] != new_value:
                    raise Exception("Failed assertion: {} = {}"
                                    .format(out[output], new_value))
            else:
                out[output] = new_value
                # print('filled in:', output, out[output])
    return {k: v.n for k,v in out.items()}


def basic_test():
    # Extract 2^28 powers of tau
    setup = c.Setup.from_file('test/powersOfTau28_hez_final_11.ptau')
    print("Extracted setup")
    vk = c.make_verification_key(setup, 8, ['c <== a * b'])
    print("Generated verification key")
    their_output = json.load(open('test/main.plonk.vkey.json'))
    for key in ('Qm', 'Ql', 'Qr', 'Qo', 'Qc', 'S1', 'S2', 'S3', 'X_2'):
        if c.interpret_json_point(their_output[key]) != getattr(vk, key):
            raise Exception("Mismatch {}: ours {} theirs {}"
                            .format(key, getattr(vk, key), their_output[key]))
    assert getattr(vk, 'w') == int(their_output['w'])
    print("Basic test success")
    return setup

# Equivalent to this zkrepl code:
#
# template Example () {
#    signal input a;
#    signal input b;
#    signal c;
#    c <== a * b + a;
# }
def ab_plus_a_test(setup):
    vk = c.make_verification_key(setup, 8, ['ab === a - c', '-ab === a * b'])
    print("Generated verification key")
    their_output = json.load(open('test/main.plonk.vkey-58.json'))
    for key in ('Qm', 'Ql', 'Qr', 'Qo', 'Qc', 'S1', 'S2', 'S3', 'X_2'):
        if c.interpret_json_point(their_output[key]) != getattr(vk, key):
            raise Exception("Mismatch {}: ours {} theirs {}"
                            .format(key, getattr(vk, key), their_output[key]))
    assert getattr(vk, 'w') == int(their_output['w'])
    print("ab+a test success")

def one_public_input_test(setup):
    vk = c.make_verification_key(setup, 8, ['c public', 'c === a * b'])
    print("Generated verification key")
    their_output = json.load(open('test/main.plonk.vkey-59.json'))
    for key in ('Qm', 'Ql', 'Qr', 'Qo', 'Qc', 'S1', 'S2', 'S3', 'X_2'):
        if c.interpret_json_point(their_output[key]) != getattr(vk, key):
            raise Exception("Mismatch {}: ours {} theirs {}"
                            .format(key, getattr(vk, key), their_output[key]))
    assert getattr(vk, 'w') == int(their_output['w'])
    print("One public input test success")

def prover_test(setup):
    print("Beginning prover test")
    eqs = ['e public', 'c <== a * b', 'e <== c * d']
    assignments = {'a': 3, 'b': 4, 'c': 12, 'd': 5, 'e': 60}
    return p.prove_from_witness(setup, 8, eqs, assignments)
    print("Prover test success")

def verifier_test(setup, proof):
    print("Beginning verifier test")
    eqs = ['e public', 'c <== a * b', 'e <== c * d']
    public = [60]
    vk = c.make_verification_key(setup, 8, eqs)
    assert vk.verify_proof(8, proof, public, optimized=False)
    assert vk.verify_proof(8, proof, public, optimized=True)
    print("Verifier test success")

def factorization_test(setup):
    print("Beginning test: prove you know small integers that multiply to 91")
    eqs = """n public
        pb0 === pb0 * pb0
        pb1 === pb1 * pb1
        pb2 === pb2 * pb2
        pb3 === pb3 * pb3
        qb0 === qb0 * qb0
        qb1 === qb1 * qb1
        qb2 === qb2 * qb2
        qb3 === qb3 * qb3
        pb01 <== pb0 + 2 * pb1
        pb012 <== pb01 + 4 * pb2
        p <== pb012 + 8 * pb3
        qb01 <== qb0 + 2 * qb1
        qb012 <== qb01 + 4 * qb2
        q <== qb012 + 8 * qb3
        n <== p * q"""
    lines = [line.strip() for line in eqs.split('\n')]
    public = [91]
    vk = c.make_verification_key(setup, 16, lines)
    print("Generated verification key")
    assignments = fill_variable_assignments(lines, {
        'pb3': 1, 'pb2': 1, 'pb1': 0, 'pb0': 1,
        'qb3': 0, 'qb2': 1, 'qb1': 1, 'qb0': 1,
    })
    proof = p.prove_from_witness(setup, 16, lines, assignments)
    print("Generated proof")
    assert vk.verify_proof(16, proof, public, optimized=True)
    print("Factorization test success!")

def output_proof_lang() -> str:
    o = []
    o.append('L0 public')
    o.append('M0 public')
    o.append('M64 public')
    o.append('R0 <== 0')
    for i in range(64):
        for j, pos in enumerate(('L', 'M', 'R')):
            f = {'x': i, 'r': rc[i][j], 'p': pos}
            if i < 4 or i >= 60 or pos == 'L':
                o.append('{p}adj{x} <== {p}{x} + {r}'.format(**f))
                o.append('{p}sq{x} <== {p}adj{x} * {p}adj{x}'.format(**f))
                o.append('{p}qd{x} <== {p}sq{x} * {p}sq{x}'.format(**f))
                o.append('{p}qn{x} <== {p}qd{x} * {p}adj{x}'.format(**f))
            else:
                o.append('{p}qn{x} <== {p}{x} + {r}'.format(**f))
        for j, pos in enumerate(('L', 'M', 'R')):
            f = {'x': i, 'p': pos, 'm': mds[j]}
            o.append('{p}suma{x} <== Lqn{x} * {m}'.format(**f))
            f = {'x': i, 'p': pos, 'm': mds[j+1]}
            o.append('{p}sumb{x} <== {p}suma{x} + Mqn{x} * {m}'.format(**f))
            f = {'x': i, 'xp1': i+1, 'p': pos, 'm': mds[j+2]}
            o.append('{p}{xp1} <== {p}sumb{x} + Rqn{x} * {m}'.format(**f))
    return '\n'.join(o)

def poseidon_test(setup):
    # PLONK-prove the correctness of a Poseidon execution. Note that this is
    # a very suboptimal way to do it: an optimized implementation would use
    # a custom PLONK gate to do a round in a single gate
    expected_value = poseidon_hash(1, 2)
    # Generate code for proof
    code = output_proof_lang()
    eqs = [line.strip() for line in code.split('\n')]
    print("Generated code for Poseidon test")
    assignments = fill_variable_assignments(eqs, {'L0': 1, 'M0': 2})
    vk = c.make_verification_key(setup, 1024, eqs)
    print("Generated verification key")
    proof = p.prove_from_witness(setup, 1024, eqs, assignments)
    print("Generated proof")
    assert vk.verify_proof(1024, proof, [1, 2, expected_value])
    print("Verified proof!")
if __name__ == '__main__':
    setup = basic_test()
    ab_plus_a_test(setup)
    one_public_input_test(setup)
    proof = prover_test(setup)
    verifier_test(setup, proof)
    factorization_test(setup)
    poseidon_test(setup)
