module

public import VerifiedGarbage.Impl.Ecdsa.P192.RISCV64
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P192Field.Verified
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P192Field.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# P-192's field on RISC-V, for `vg_p192_mul` and its callers

The facts the proofs of `vg_p192_mul` (`Proof/Ecdsa/RISCV64/P192/Window.lean`)
and its callers share: P-192's field functions meet the contracts by register
(`field_ok`), and `R = 2²⁵⁶` is a unit modulo `p` (`unit`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P192

open VG VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- P-192. -/
abbrev W : Curve := Spec.P192.curve

theorem field_ok : FieldOk p192Field :=
  ⟨P192Field.mul_rv, P192Field.add_rv, P192Field.sub_rv, Impl.Ecdsa.RISCV64.p192MulP_noFrames,
    Impl.Ecdsa.RISCV64.p192AddP_noFrames, Impl.Ecdsa.RISCV64.p192SubP_noFrames⟩

instance : NeZero p192Field.S.m := ⟨by decide⟩

theorem p_odd : W.p % 2 = 1 := by decide

theorem unit : UnitMod W.p (2 ^ (64 * 4)) := unitMod_pow_two p_odd _

/-- The number at slot `i`. -/
abbrev sv (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (p192.sl i) 4

end VG.Proof.Ecdsa.RISCV64.P192
