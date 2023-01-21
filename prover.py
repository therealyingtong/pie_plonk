from compiler.program import Program
from compiler.utils import Column
from curve import Scalar
from dataclasses import dataclass
from kzg.setup import *
from poly import Basis, Polynomial
from transcript import Transcript
from typing import Optional
from transcript import *
from utils import *

@dataclass
class Prover:
    def prove(self, setup: Setup, program: Program, witness: dict[Optional[str], int]):
        self.group_order = program.group_order

        proof = {}

        # Initialise Fiat-Shamir transcript
        transcript = Transcript()

        # Collect fixed and public information
        self.init(program, witness)

        # Round 1
        # - [a(x)]₁ (commitment to left wire polynomial)
        # - [b(x)]₁ (commitment to right wire polynomial)
        # - [c(x)]₁ (commitment to output wire polynomial)
        a_1, b_1, c_1 = self.round_1(program, witness, transcript, setup)
        proof['a_1'] = a_1
        proof['b_1'] = b_1
        proof['c_1'] = c_1

        # Round 2
        # - [z(x)]₁ (commitment to permutation polynomial)
        z_1 = self.round_2(transcript, setup)
        proof['z_1'] = z_1

        # Round 3
        # - [t_lo(x)]₁ (commitment to t_lo(X), the low chunk of the quotient polynomial t(X))
        # - [t_mid(x)]₁ (commitment to t_mid(X), the middle chunk of the quotient polynomial t(X))
        # - [t_hi(x)]₁ (commitment to t_hi(X), the high chunk of the quotient polynomial t(X))
        t_lo_1, t_mid_1, t_hi_1 = self.round_3(transcript, setup)
        proof['t_lo_1'] = t_lo_1
        proof['t_mid_1'] = t_mid_1
        proof['t_hi_1'] = t_hi_1

        # Round 4
        # - Evaluation of a(X) at evaluation challenge ζ
        # - Evaluation of b(X) at evaluation challenge ζ
        # - Evaluation of c(X) at evaluation challenge ζ
        # - Evaluation of the first permutation polynomial S_σ1(X) at evaluation challenge ζ
        # - Evaluation of the second permutation polynomial S_σ2(X) at evaluation challenge ζ
        # - Evaluation of the shifted permutation polynomial z(X) at the shifted evaluation challenge ζω
        a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval = self.round_4(transcript)
        proof['a_eval'] = a_eval
        proof['b_eval'] = b_eval
        proof['c_eval'] = c_eval
        proof['s1_eval'] = s1_eval
        proof['s2_eval'] = s2_eval
        proof['z_shifted_eval'] = z_shifted_eval

        # Round 5
        # - [W_ζ(X)]₁ (commitment to the opening proof polynomial)
        # - [W_ζω(X)]₁ (commitment to the opening proof polynomial)
        W_z_1, W_zw_1 = self.round_5(transcript, setup)
        proof['W_z_1'] = W_z_1
        proof['W_zw_1'] = W_zw_1

        return proof
    
    def init(self, program: Program, witness: dict[Optional[str], int]):
        QL, QR, QM, QO, QC = program.make_gate_polynomials()

        S = program.make_s_polynomials()
        S1 = S[Column.LEFT]
        S2 = S[Column.RIGHT]
        S3 = S[Column.OUTPUT]

        # Collect information about public values
        public_vars = program.get_public_assignments()
        public_values = (
            [Scalar(-witness[v]) for v in public_vars] +
            [Scalar(0) for _ in range(self.group_order - len(public_vars))]
        )
        PI = Polynomial(Basis.LAGRANGE, public_values)

        self.QL = QL
        self.QR = QR
        self.QM = QM
        self.QO = QO
        self.QC = QC
        self.S1 = S1
        self.S2 = S2
        self.S3 = S3
        self.PI = PI

    def round_1(
        self,
        program: Program,
        witness: dict[Optional[str], int],
        transcript: Transcript, setup: Setup
    ):
        group_order = self.group_order

        if None not in witness:
            witness[None] = 0

        # Compute wire assignments
        A_values = [Scalar(0) for _ in range(group_order)]
        B_values = [Scalar(0) for _ in range(group_order)]
        C_values = [Scalar(0) for _ in range(group_order)]

        for i, gate_wires in enumerate(program.wires()):
            A_values[i] = Scalar(witness[gate_wires.L])
            B_values[i] = Scalar(witness[gate_wires.R])
            C_values[i] = Scalar(witness[gate_wires.O])

        A = Polynomial(Basis.LAGRANGE, A_values)
        a_1 = setup.commit(A)
        transcript.hash_point(a_1)

        B = Polynomial(Basis.LAGRANGE, B_values)
        b_1 = setup.commit(B)
        transcript.hash_point(b_1)

        C = Polynomial(Basis.LAGRANGE, C_values)
        c_1 = setup.commit(C)
        transcript.hash_point(c_1)

        self.A = A
        self.B = B
        self.C = C

        # Sanity check that witness fulfils gate constraints
        for i in range(group_order):
            assert (
                A.values[i] * self.QL.values[i] + B.values[i] * self.QR.values[i] + A.values[i] * B.values[i] * self.QM.values[i] +
                C.values[i] * self.QO.values[i] + self.PI.values[i] + self.QC.values[i] == 0
            )

        return a_1, b_1, c_1

    def round_2(
        self,
        transcript: Transcript,
        setup: Setup,
    ):
        group_order = self.group_order

        # The first two Fiat-Shamir challenges
        beta = transcript.squeeze()
        transcript.beta = beta
        self.beta = beta

        gamma = transcript.squeeze()
        transcript.gamma = gamma
        self.gamma = gamma

        # Compute the accumulator polynomial for the permutation arguments
        Z_values = [Scalar(1)]
        roots_of_unity = Scalar.roots_of_unity(group_order)
        for i in range(group_order):
            Z_values.append(
                Z_values[-1] *
                self.rlc(self.A.values[i], roots_of_unity[i]) *
                self.rlc(self.B.values[i], 2 * roots_of_unity[i]) *
                self.rlc(self.C.values[i], 3 * roots_of_unity[i]) /
                self.rlc(self.A.values[i], self.S1.values[i]) /
                self.rlc(self.B.values[i], self.S2.values[i]) /
                self.rlc(self.C.values[i], self.S3.values[i])
            )
        assert Z_values.pop() == 1
        Z = Polynomial(Basis.LAGRANGE, Z_values)

        # Sanity-check that Z was computed correctly
        for i in range(group_order):
            assert (
                self.rlc(self.A.values[i], roots_of_unity[i]) *
                self.rlc(self.B.values[i], 2 * roots_of_unity[i]) *
                self.rlc(self.C.values[i], 3 * roots_of_unity[i])
            ) * Z.values[i] - (
                self.rlc(self.A.values[i], self.S1.values[i]) *
                self.rlc(self.B.values[i], self.S2.values[i]) *
                self.rlc(self.C.values[i], self.S3.values[i])
            ) * Z.values[(i+1) % group_order] == 0

        z_1 = setup.commit(Z)
        transcript.hash_point(z_1)
        print("Permutation accumulator polynomial successfully generated")

        self.Z = Z
        return z_1

    def round_3(self, transcript: Transcript, setup: Setup):
        group_order = self.group_order

        # Compute the quotient polynomial
        def quotient_poly():
            A_big = self.fft_expand_to_coset(self.A)
            B_big = self.fft_expand_to_coset(self.B)
            C_big = self.fft_expand_to_coset(self.C)

            # Compute the quotient polynomial (called T(x) in the paper)
            # It is only possible to construct this polynomial if the following
            # equations are true at all roots of unity {1, w ... w^(n-1)}:
            #
            # 1. All gates are correct:
            #    A * QL + B * QR + A * B * QM + C * QO + PI + QC = 0
            def gates():
                QL_big, QR_big, QM_big, QO_big, QC_big, PI_big = (
                    self.fft_expand_to_coset(x) for x in (
                        self.QL, self.QR, self.QM, self.QO, self.QC, self.PI
                    )
                )
                return (
                    A_big * QL_big
                    + B_big * QR_big
                    + A_big * B_big * QM_big
                    + C_big * QO_big
                    + PI_big
                    + QC_big
                )
            
            # 2. The permutation accumulator is valid:
            #    Z(wx) * (rlc of A, S1) * (rlc of B, S2) * (rlc of C, S3)
            #  = Z(x) * (rlc of A, X) * (rlc of B, 2X) * (rlc of C, 3X)
            Z_big = self.fft_expand_to_coset(self.Z)

            def permutation_accumulator():
                S1_big = self.fft_expand_to_coset(self.S1)
                S2_big = self.fft_expand_to_coset(self.S2)
                S3_big = self.fft_expand_to_coset(self.S3)

                Z_shifted_big = Z_big.shift(4)
                quarter_roots_shifted = self.quarter_roots_shifted()
                LHS = (
                    self.rlc(A_big, S1_big) *
                    self.rlc(B_big, S2_big) *
                    self.rlc(C_big, S3_big)
                ) * Z_shifted_big
                RHS = (
                    self.rlc(A_big, quarter_roots_shifted) *
                    self.rlc(B_big, quarter_roots_shifted * Scalar(2)) *
                    self.rlc(C_big, quarter_roots_shifted * Scalar(3))
                ) * Z_big

                return LHS - RHS

            # 3. The permutation accumulator equals 1 at the start point
            #    (Z - 1) * L1 = 0
            #    L1 = Lagrange polynomial, equal at all roots of unity except 1
            def permutation_start():
                # Equals 1 at x=1 and 0 at other roots of unity
                L1_big = self.fft_expand_to_coset(
                    Polynomial(
                        Basis.LAGRANGE,
                        [Scalar(1)] + [Scalar(0)] * (group_order - 1)
                    )
                )
                return (Z_big - Scalar(1)) * L1_big

            numerator = (
                gates()
                    + permutation_accumulator() * transcript.alpha
                    + permutation_start() * transcript.alpha ** 2
            )

            # Sanity check that numerator is zero at all quarter roots of unity
            lagrange = self.expanded_evals_to_coeffs(numerator).fft()
            for root in Scalar.roots_of_unity(4 * group_order):
                assert lagrange.barycentric_eval(root) == Scalar(0)

            # Z_H = X^N - 1, also in evaluation form in the coset
            ZH_big_values = [
                r ** group_order - 1
                for r in self.quarter_roots_shifted().values
            ]
            ZH_big = Polynomial(Basis.EXTENDED_LAGRANGE, ZH_big_values)
            quotient_big = numerator / ZH_big

            quotient = self.expanded_evals_to_coeffs(quotient_big).values

            # Sanity check: quotient polynomial has degree < 3n
            assert quotient[-group_order:] == [0] * group_order
            print("Generated the quotient polynomial")

            return quotient, quotient_big.values[0]

        # Split up T into T1, T2 and T3 (needed because T has degree 3n, so is
        # too big for the trusted setup)
        def split_quotient_poly(quotient, quotient_big_0: Scalar):
            T1 = Polynomial(Basis.MONOMIAL, quotient[:group_order]).fft()
            T2 = Polynomial(Basis.MONOMIAL, quotient[group_order: group_order * 2]).fft()
            T3 = Polynomial(Basis.MONOMIAL, quotient[group_order * 2: group_order * 3]).fft()

            # Sanity check that we've computed T1, T2, T3 correctly
            # The quotient polynomial in the extended Lagrange basis
            # should evaluate to its first term at `fft_cofactor`.
            assert (
                T1.barycentric_eval(self.fft_cofactor) +
                T2.barycentric_eval(self.fft_cofactor) * self.fft_cofactor ** group_order +
                T3.barycentric_eval(self.fft_cofactor) * self.fft_cofactor ** (group_order * 2)
            ) == quotient_big_0

            print("Generated T1, T2, T3 polynomials")

            return T1, T2, T3

        alpha = transcript.squeeze()
        transcript.alpha = alpha

        # This value could be anything, it just needs to be unpredictable. Lets us
        # have evaluation forms at cosets to avoid zero evaluations, so we can
        # divide polys without the 0/0 issue
        fft_cofactor = transcript.squeeze()
        transcript.fft_cofactor = fft_cofactor
        self.fft_cofactor = fft_cofactor

        quotient_poly, quotient_big_0 = quotient_poly()
        T1, T2, T3 = split_quotient_poly(quotient_poly, quotient_big_0)

        t_lo_1 = setup.commit(T1)
        transcript.hash_point(t_lo_1)

        t_mid_1 = setup.commit(T2)
        transcript.hash_point(t_mid_1)

        t_hi_1 = setup.commit(T3)
        transcript.hash_point(t_hi_1)

        self.T1 = T1
        self.T2 = T2
        self.T3 = T3

        return t_lo_1, t_mid_1, t_hi_1

    def round_4(self, transcript: Transcript):
        group_order = self.group_order

        zed = transcript.squeeze()
        transcript.zed = zed
        self.zed = zed

        a_eval = self.A.barycentric_eval(zed)
        transcript.hash_scalar(a_eval)
        
        b_eval = self.B.barycentric_eval(zed)
        transcript.hash_scalar(b_eval)
        
        c_eval = self.C.barycentric_eval(zed)
        transcript.hash_scalar(c_eval)
        
        s1_eval = self.S1.barycentric_eval(zed)
        transcript.hash_scalar(s1_eval)
        
        s2_eval = self.S2.barycentric_eval(zed)
        transcript.hash_scalar(s2_eval)
        
        # ωζ, the evaluation point shifted once
        shifted_zed = Scalar.root_of_unity(group_order) * zed
        # Z(ωζ), Z evaluated at the shifted evaluation point
        z_shifted_eval = self.Z.barycentric_eval(shifted_zed)
        transcript.hash_scalar(z_shifted_eval)

        self.a_eval = a_eval
        self.b_eval = b_eval
        self.c_eval = c_eval
        self.s1_eval = s1_eval
        self.s2_eval = s2_eval
        self.z_shifted_eval = z_shifted_eval

        return a_eval, b_eval, c_eval, s1_eval, s2_eval, z_shifted_eval

    def round_5(self, transcript: Transcript, setup: Setup):
        group_order = self.group_order

        # Compute the "linearization polynomial" R. This is a clever way to avoid
        # needing to provide evaluations of _all_ the polynomials that we are
        # checking an equation betweeen: instead, we can "skip" the first
        # multiplicand in each term. The idea is that we construct a
        # polynomial which is constructed to equal 0 at ζ only if the equations
        # that we are checking are correct, and which the verifier can reconstruct
        # the KZG commitment to, and we provide proofs to verify that it actually
        # equals 0 at ζ
        #
        # In order for the verifier to be able to reconstruct the commitment to R,
        # it has to be "linear" in the proof items, hence why we can only use each
        # proof item once; any further multiplicands in each term need to be
        # replaced with their evaluations at ζ, which do still need to be provided
        def linearization_poly() -> Polynomial:
            group_order = self.group_order

            def gates():
                # PI(ζ)
                PI_ev = self.eval(self.PI)

                return (
                    self.QM * self.a_eval * self.b_eval +
                    self.QL * self.a_eval +
                    self.QR * self.b_eval +
                    self.QO * self.c_eval +
                    PI_ev +
                    self.QC
                )

            def permutation_accumulator():
                LHS = self.Z * (
                    self.rlc(self.a_eval, self.zed)
                    * self.rlc(self.b_eval, 2 * self.zed)
                    * self.rlc(self.c_eval, 3 * self.zed)
                )
                c_eval = Polynomial(Basis.LAGRANGE, [self.c_eval] * group_order)

                RHS = (
                    self.rlc(c_eval, self.S3)
                    * self.rlc(self.a_eval, self.s1_eval)
                    * self.rlc(self.b_eval, self.s2_eval)  
                ) * self.z_shifted_eval
                return LHS - RHS

            def permutation_start():
                L1_ev = self.eval(
                    Polynomial(
                        Basis.LAGRANGE,
                        [Scalar(1)] + [Scalar(0)] * (group_order - 1)
                    )
                )
                return (self.Z - Scalar(1)) * L1_ev
            
            def quotient_chunks():
                # Z_H(ζ) = ζ^n - 1
                ZH_ev = self.zed ** group_order - 1

                return (
                    self.T1 +
                    self.T2 * (self.zed ** group_order) +
                    self.T3 * (self.zed ** (group_order * 2))
                ) * ZH_ev

            alpha = transcript.alpha
            R = (
                gates()
                + permutation_accumulator() * alpha
                + permutation_start() * alpha ** 2
                - quotient_chunks()
            )
            # Sanity check on linearization polynomial
            print("barycentric eval", R.barycentric_eval(self.zed))
            assert R.barycentric_eval(self.zed) == 0
            print("Generated linearization polynomial R")

            return R

        v = transcript.squeeze()
        transcript.v = v

        roots_poly = Polynomial(
            Basis.LAGRANGE,
            Scalar.roots_of_unity(group_order)
        )

        # Generate proof that W(z) = 0 and that the provided evaluations of
        # A, B, C, S1, S2 are correct
        R = linearization_poly()
        W_z = (
            R +
            (self.A - self.a_eval) * v +
            (self.B - self.b_eval) * v ** 2 +
            (self.C - self.c_eval) * v ** 3 +
            (self.S1 - self.s1_eval) * v ** 4 +
            (self.S2 - self.s2_eval) * v ** 5
        ) / (roots_poly - transcript.zed)
        W_z_1 = setup.commit(W_z)
        transcript.hash_point(W_z_1)

        # Generate proof that the provided evaluation of Z(z*w) is correct. This
        # awkwardly different term is needed because the permutation accumulator
        # polynomial Z is the one place where we have to check between adjacent
        # coordinates, and not just within one coordinate.
        root_of_unity = Scalar.root_of_unity(group_order)
        W_zw = (self.Z - self.z_shifted_eval) / (roots_poly - (self.zed * root_of_unity))

        W_zw_1 = setup.commit(W_zw)
        transcript.hash_point(W_zw_1)

        print("Generated final quotient witness polynomials")

        return W_z_1, W_zw_1

    def fft_expand_to_coset(self, poly: Polynomial):
        return poly.fft_expand_to_coset(self.fft_cofactor)

    def expanded_evals_to_coeffs(self, poly: Polynomial):
        return poly.coset_evals_to_coeffs(self.fft_cofactor)

    # Roots of unity at 4x fineness
    def quarter_roots(self):
        return Polynomial(
            Basis.EXTENDED_LAGRANGE,
            Scalar.roots_of_unity(self.group_order * 4)
        )

    def quarter_roots_shifted(self):
        return self.quarter_roots() * self.fft_cofactor

    # rlc = random linear combination: term_1 + beta * term2 + gamma
    def rlc(self, term_1, term_2):
        return term_1 + (term_2 * self.beta) + self.gamma

    def eval(self, poly: Polynomial) -> Scalar:
        return poly.barycentric_eval(self.zed)

    def shifted_eval(self, poly, shift) -> Scalar:
        return poly.barycentric_eval(shift * self.zed)
