import py_ecc.bn128 as b
from .setup import Setup
from . import G1Point
from curve import Scalar, ec_lincomb
from typing import NewType
from dataclasses import dataclass
from poly import Polynomial

@dataclass
class EvaluationClaim:
    commitment: Commitment
    point: Scalar
    evaluation: Scalar

    # Creates an opening proof for a KZG evaluation claim.