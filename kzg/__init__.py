from typing import NewType
import py_ecc.bn128 as b

G1Point = NewType('G1Point', tuple[b.FQ, b.FQ])
G2Point = NewType('G2Point', tuple[b.FQ2, b.FQ2])
