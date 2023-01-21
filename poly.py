from enum import Enum
from curve import Scalar

class Basis(Enum):
    LAGRANGE = 1
    MONOMIAL = 2
    EXTENDED_LAGRANGE = 3
    EXTENDED_MONOMIAL = 4

class Polynomial:
    basis: Basis
    values: list[Scalar]

    def __init__(self, basis: Basis, values: list[Scalar]):
        self.basis = basis
        self.values = values

    def __add__(self, other):
        if isinstance(other, Polynomial):
            assert len(self.values) == len(other.values)
            assert self.basis == other.basis
            values = [self.values[i] + other.values[i] for i in range(len(self.values))]
            return Polynomial(self.basis, values)
        elif isinstance(other, Scalar):
            return self._add_constant(other)

    def __sub__(self, other):
        if isinstance(other, Polynomial):
            assert len(self.values) == len(other.values)
            assert self.basis == other.basis
            values = [self.values[i] - other.values[i] for i in range(len(self.values))]
            return Polynomial(self.basis, values)
        elif isinstance(other, Scalar):
            return self._add_constant(-other)
    
    def __mul__(self, other):
        if isinstance(other, Polynomial):
            assert self.basis == Basis.EXTENDED_LAGRANGE
            assert other.basis == Basis.EXTENDED_LAGRANGE
            values = [self.values[i] * other.values[i] for i in range(len(self.values))]
            return Polynomial(self.basis, values)
        elif isinstance(other, Scalar):
            return self._scale(other)

    def __truediv__(self, other):
        if isinstance(other, Polynomial):
            assert self.basis == other.basis
            assert self.basis == Basis.EXTENDED_LAGRANGE or self.basis == Basis.LAGRANGE
            values = [self.values[i] / other.values[i] for i in range(len(self.values))]
            return Polynomial(self.basis, values)
        elif isinstance(other, Scalar):
            return self._scale(1 / other)

    def _scale(self, scalar: Scalar):
        values = [scalar * self.values[i] for i in range(len(self.values))]
        return Polynomial(self.basis, values)
    
    def _add_constant(self, constant: Scalar):
        assert self.basis != Basis.MONOMIAL
        constants = Polynomial(
            self.basis,
            [constant] * len(self.values)
        )
        return self + constants

    def shift(self, shift: int):
        assert self.basis != Basis.MONOMIAL
        values = self.values[shift:] + self.values[:shift]
        return Polynomial(self.basis, values)

    # Given a polynomial expressed as a list of evaluations at roots of unity,
    # evaluate it at x directly, without using an FFT to convert to coeffs first
    def barycentric_eval(self, x) -> Scalar:
        order = len(self.values)

        return (
            (Scalar(x)**order - 1) / order *
            sum([
                value * root / (x - root)
                for value, root in zip(self.values, Scalar.roots_of_unity(len(self.values)))
            ])
        )
    
    def ifft(self):
        return self.fft(inv=True)

    # Convenience method to do FFTs specifically over the subgroup over which
    # all of the proofs are operating
    def fft(self, inv=False):
        # Fast Fourier transform, used to convert between polynomial coefficients
        # and a list of evaluations at the roots of unity
        # See https://vitalik.ca/general/2019/05/12/fft.html
        def _fft(values, roots_of_unity):
            if len(values) == 1:
                return values
            L = _fft(values[::2], roots_of_unity[::2])
            R = _fft(values[1::2], roots_of_unity[::2])
            output = [0] * len(values)
            for i, (x, y) in enumerate(zip(L, R)):
                y_times_root = y * roots_of_unity[i]
                output[i] = (x + y_times_root) % Scalar.field_modulus 
                output[i + len(L)] = (x - y_times_root) % Scalar.field_modulus 
            return output

        roots = [x.n for x in Scalar.roots_of_unity(len(self.values))]
        nvals = [x.n for x in self.values]
        if inv:
            # Inverse FFT from Lagrange basis to monomial basis
            invlen = Scalar(1) / len(self.values)
            reversed_roots = [roots[0]] + roots[1:][::-1]
            values = [Scalar(x) * invlen for x in _fft(nvals, reversed_roots)]
            if self.basis == Basis.LAGRANGE:
                return Polynomial(Basis.MONOMIAL, values)
            else:
                assert self.basis == Basis.EXTENDED_LAGRANGE
                return Polynomial(Basis.EXTENDED_MONOMIAL, values)
        else:
            # Regular FFT from monomial basis to Lagrange basis
            values = [Scalar(x) for x in _fft(nvals, roots)]
            if self.basis == Basis.MONOMIAL:
                return Polynomial(Basis.LAGRANGE, values)
            else:
                assert self.basis == Basis.EXTENDED_MONOMIAL
                return Polynomial(Basis.EXTENDED_LAGRANGE, values)

    def to_coset(self, shift: Scalar, inv=False):
        cofactor = 1 / shift if inv else shift
        if self.basis == Basis.MONOMIAL or self.basis == Basis.EXTENDED_MONOMIAL:
            return Polynomial(
                self.basis,
                [(cofactor ** i * x) for i, x in enumerate(self.values)]
            )

    # Converts a list of evaluations at the roots of unity
    #                       [1, w, w**2... w**(n-1)]
    # to a list of evaluations at the shifted quarter roots of unity
    #         [cofactor, cofactor * q, cofactor * q**2 ... cofactor * q**(4n-1)]
    # where q = w**(1/4).
    # 
    # This lets us work with higher-degree polynomials, and the cofactor lets us
    # avoid the 0/0 problem when computing a division (as long as the cofactor is
    # chosen randomly)
    def fft_expand_to_coset(self, cofactor):
        assert self.basis == Basis.LAGRANGE

        group_order = len(self.values)
        coeffs = self.ifft()
        coeffs_coset = coeffs.to_coset(cofactor)
        coeffs_coset_expanded = Polynomial(
            Basis.EXTENDED_MONOMIAL,
            coeffs_coset.values + [Scalar(0)] * (group_order * 3)
        )
        return coeffs_coset_expanded.fft()
    
    # Convert from coset expanded form into coefficients
    # Note that we can't make a full inverse function of fft_expand_to_coset
    # because the output of this might be a deg >= n polynomial, which cannot
    # be expressed via evaluations at n roots of unity
    def coset_evals_to_coeffs(self, cofactor):
        assert self.basis == Basis.EXTENDED_LAGRANGE
        unshifted_expanded_coeffs = self.ifft()
        return unshifted_expanded_coeffs.to_coset(cofactor, inv=True)
