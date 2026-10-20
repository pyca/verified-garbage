module

public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64
import VerifiedGarbage.Impl.Mont.AArch64.P384Sqr

/-!
# P-384's field operations inline on AArch64

`op` is one field operation (`FOp`) on slots of the working space at `x0`,
in a straight line, for the register allocator (`Impl/P256/VerifyRegisters.lean`):
a product or square by the cores of `vg_p384_mul_mod_p` and `vg_p384_sqr_mod_p`
(`Impl/Mont/AArch64/P384Mul.lean`, `P384Sqr.lean`, adapted from s2n-bignum's
`bignum_montmul_p384_alt` and `bignum_montsqr_p384_alt`), with the operands
loaded from their slots in place of the functions' pointers, and a sum or
difference by `opCode`. Every constant is loaded from the modulus's slot or
computed by register operations, as the allocator follows only those.
-/

@[expose] public section

namespace VG.Impl.P384.Ops
open VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- P-384's field prime's modulus, as ECDH and ECDSA lay it out. -/
def M : Mod := Impl.Ecdsa.AArch64.p384.MP'

/-- The reductions' constants (`P384Mul.redConsts`), from `x7 = 0`: `x17` the
low word of `p`, `0x00000000ffffffff`, and `x16 = 2^64 - x17`. -/
def redLoad : List Instr := [ld .x17 M.mo, .sub .x .x16 .x7 .x17]

/-- After the product or square in `P384Mul.accRegs`: the six reductions of
its low half, the high half added, the sum reduced below `p` and stored at `o`. -/
def finish (o : Nat) : List Instr :=
  redLoad ++ ((List.range 6).flatMap P384Mul.red ++ (P384Mul.addHigh ++
    (csubR M P384Mul.lowRegs .x21 ++ stores P384Mul.lowRegs o)))

/-- `[o] = [a] [b] 2^-384 mod p`. -/
def mul (o a b : Nat) : List Instr :=
  loads P384Mul.bRegs384 b ++ ((zero7 :: P384Mul.prodAt .x0 a) ++ finish o)

/-- `[o] = [a]^2 2^-384 mod p`. -/
def sqr (o a : Nat) : List Instr :=
  loads P384Sqr.aRegs a ++ ((zero7 :: P384Sqr.sq) ++ finish o)

/-- One field operation. -/
def op : FOp → List Instr
  | .mul o a b => if a == b then sqr o a else mul o a b
  | f => opCode M f

end VG.Impl.P384.Ops
