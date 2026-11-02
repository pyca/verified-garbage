module

public import VerifiedGarbage.Impl.Ecdsa.P224.RISCV64
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P224Field.Verified
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P224Field.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# P-224's field on RISC-V, for `vg_p224_mul` and its callers

The facts the proofs of `vg_p224_mul` (`Proof/Ecdsa/RISCV64/P224/Window.lean`)
and its callers share: P-224's field functions meet the contracts by register
(`field_ok`), and `R = 2²⁵⁶` is a unit modulo `p` (`unit`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P224

open VG VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- P-224. -/
abbrev W : Curve := Spec.P224.curve

theorem field_ok : FieldOk p224Field :=
  ⟨P224Field.mul_rv, P224Field.add_rv, P224Field.sub_rv, Impl.Ecdsa.RISCV64.p224MulP_noFrames,
    Impl.Ecdsa.RISCV64.p224AddP_noFrames, Impl.Ecdsa.RISCV64.p224SubP_noFrames⟩

instance : NeZero p224Field.S.m := ⟨by decide⟩

theorem p_odd : W.p % 2 = 1 := by decide

theorem unit : UnitMod W.p (2 ^ (64 * 4)) := unitMod_pow_two p_odd _

/-- The number at slot `i`. -/
abbrev sv (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (p224.sl i) 4

end VG.Proof.Ecdsa.RISCV64.P224
