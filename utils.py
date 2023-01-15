import py_ecc.bn128 as b
from py_ecc.fields.field_elements import FQ as Field
from functools import cache
from Crypto.Hash import keccak
from multicombs import lincomb

f = b.FQ
f2 = b.FQ2

class f_inner(Field):
    field_modulus = b.curve_order

primitive_root = 5

# Gets the first root of unity of a given group order
@cache
def get_root_of_unity(group_order) -> f_inner:
    return f_inner(5) ** ((b.curve_order - 1) // group_order)

# Gets the full list of roots of unity of a given group order
@cache
def get_roots_of_unity(group_order: int) -> list[f_inner]:
    o = [f_inner(1), get_root_of_unity(group_order)]
    while len(o) < group_order:
        o.append(o[-1] * o[1])
    return o

def keccak256(x):
    return keccak.new(digest_bits=256).update(x).digest()

def serialize_int(x):
    return x.n.to_bytes(32, 'big')

def serialize_point(pt):
    return pt[0].n.to_bytes(32, 'big') + pt[1].n.to_bytes(32, 'big')

# Converts a hash to a f_inner element
def binhash_to_f_inner(h):
    return f_inner(int.from_bytes(h, 'big'))

def ec_mul(pt, coeff):
    if hasattr(coeff, 'n'):
        coeff = coeff.n
    return b.multiply(pt, coeff % b.curve_order)

# Elliptic curve linear combination. A truly optimized implementation
# would replace this with a fast lin-comb algo, see https://ethresear.ch/t/7238
def ec_lincomb(pairs):
    return lincomb(
        [pt for (pt, _) in pairs],
        [int(n) % b.curve_order for (_, n) in pairs],
        b.add,
        b.Z1
    )
    # Equivalent to:
    # o = b.Z1
    # for pt, coeff in pairs:
    #     o = b.add(o, ec_mul(pt, coeff))
    # return o

# Extracts a point from JSON in zkrepl's format
def interpret_json_point(p):
    if len(p) == 3 and isinstance(p[0], str) and p[2] == "1":
        return (f(int(p[0])), f(int(p[1])))
    elif len(p) == 3 and p == ["0", "1", "0"]:
        return b.Z1
    elif len(p) == 3 and isinstance(p[0], list) and p[2] == ["1", "0"]:
        return (
            f2([int(p[0][0]), int(p[0][1])]),
            f2([int(p[1][0]), int(p[1][1])]),
        )
    elif len(p) == 3 and p == [["0", "0"], ["1", "0"], ["0", "0"]]:
        return b.Z2
    raise Exception("cannot interpret that point: {}".format(p))

# Fast Fourier transform, used to convert between polynomial coefficients
# and a list of evaluations at the roots of unity
# See https://vitalik.ca/general/2019/05/12/fft.html
def _fft(vals, modulus, roots_of_unity):
    if len(vals) == 1:
        return vals
    L = _fft(vals[::2], modulus, roots_of_unity[::2])
    R = _fft(vals[1::2], modulus, roots_of_unity[::2])
    o = [0 for i in vals]
    for i, (x, y) in enumerate(zip(L, R)):
        y_times_root = y*roots_of_unity[i]
        o[i] = (x+y_times_root) % modulus 
        o[i+len(L)] = (x-y_times_root) % modulus 
    return o

# Convenience method to do FFTs specifically over the subgroup over which
# all of the proofs are operating
def f_inner_fft(vals, inv=False):
    roots = [x.n for x in get_roots_of_unity(len(vals))]
    o, nvals = b.curve_order, [x.n for x in vals]
    if inv:
        # Inverse FFT
        invlen = f_inner(1) / len(vals)
        reversed_roots = [roots[0]] + roots[1:][::-1]
        return [f_inner(x) * invlen for x in _fft(nvals, o, reversed_roots)]
    else:
        # Regular FFT
        return [f_inner(x) for x in _fft(nvals, o, roots)]

# Converts a list of evaluations at [1, w, w**2... w**(n-1)] to
# a list of evaluations at
# [offset, offset * q, offset * q**2 ... offset * q**(4n-1)] where q = w**(1/4)
# This lets us work with higher-degree polynomials, and the offset lets us
# avoid the 0/0 problem when computing a division (as long as the offset is
# chosen randomly)
def fft_expand_with_offset(vals, offset):
    group_order = len(vals)
    x_powers = f_inner_fft(vals, inv=True)
    x_powers = [
        (offset**i * x) for i, x in enumerate(x_powers)
    ] + [f_inner(0)] * (group_order * 3)
    return f_inner_fft(x_powers)

# Convert from offset form into coefficients
# Note that we can't make a full inverse function of fft_expand_with_offset
# because the output of this might be a deg >= n polynomial, which cannot
# be expressed via evaluations at n roots of unity
def offset_evals_to_coeffs(evals, offset):
    shifted_coeffs = f_inner_fft(evals, inv=True)
    inv_offset = (1 / offset)
    return [v * inv_offset ** i for (i, v) in enumerate(shifted_coeffs)]

# Given a polynomial expressed as a list of evaluations at roots of unity,
# evaluate it at x directly, without using an FFT to covert to coeffs first
def barycentric_eval_at_point(values, x):
    order = len(values)
    roots_of_unity = get_roots_of_unity(order)
    return (
        (f_inner(x)**order - 1) / order *
        sum([
            value * root / (x - root)
            for value, root in zip(values, roots_of_unity)
        ])
    )
