module

public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64.Cfg

/-!
# P-384's field operations inline on AArch64

`op` is one field operation (`FOp`) on slots of the working space at `x0`, in a
straight line: a product or square by the code of the functions
`vg_p384_mul_mod_p` and `vg_p384_sqr_mod_p` (`Impl/Mont/AArch64/P384Field.lean`),
its operands loaded from their slots, and a sum or difference by `opCode`. It
loads every constant from the modulus's slot or computes it in registers, and
its loads and stores are all of words at `x0`.
-/

@[expose] public section

namespace VG.Impl.P384.Ops
open VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- P-384's field modulus, as ECDH, ECDSA and key generation keep it. -/
def M : Mod := Impl.Ecdsa.AArch64.p384.MP'

/-- The reduction of `T`, the conditional subtraction and the store. -/
def finish (o : Nat) : List Instr :=
  P384Field.reduce ++ csubR M P384Field.rs .x13 ++ stores P384Field.rs o

/-- `[o] = [a] [b] R⁻¹ mod p`, for `[b]` below `p`. -/
def mul (o a b : Nat) : List Instr := zero7 :: P384Field.prod .x0 .x0 a b ++ finish o

/-- `[o] = [a]² R⁻¹ mod p`, for `[a]` below `p`. -/
def sqr (o a : Nat) : List Instr := zero7 :: P384Field.sqr .x0 a ++ finish o

/-- A field operation. -/
def op : FOp → List Instr
  | .mul o a b => if a == b then sqr o a else mul o a b
  | f => opCode M f

end VG.Impl.P384.Ops
