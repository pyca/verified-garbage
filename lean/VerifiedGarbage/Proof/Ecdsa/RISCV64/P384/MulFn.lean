module

public import VerifiedGarbage.Impl.Ecdsa.P384.RISCV64
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Verified
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# P-384's field on RISC-V, for `vg_p384_mul` and its callers

The facts the proofs of `vg_p384_mul` (`Proof/Ecdsa/RISCV64/P384/Window.lean`)
and its callers share: P-384's field functions meet the contracts by register
(`field_ok`), and `R = 2³⁸⁴` is a unit modulo `p` (`unit`).
-/

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P384

open VG VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- P-384. -/
abbrev W : Curve := Spec.P384.curve

theorem field_ok : FieldOk p384Field :=
  ⟨P384Field.mul_rv, P384Field.add_rv, P384Field.sub_rv,
    Impl.Weierstrass.RISCV64.P384Field.mulFn_noFrames,
    Impl.Weierstrass.RISCV64.P384Field.addFn_noFrames, Impl.Weierstrass.RISCV64.P384Field.subFn_noFrames,
    P384Field.mulA_rv, P384Field.addA_rv, P384Field.subA_rv,
    Impl.Weierstrass.RISCV64.P384Field.mulFnA_noFrames,
    Impl.Weierstrass.RISCV64.P384Field.addFnA_noFrames, Impl.Weierstrass.RISCV64.P384Field.subFnA_noFrames⟩

instance : NeZero p384Field.S.m := ⟨by decide⟩

theorem p_odd : W.p % 2 = 1 := by decide

theorem unit : UnitMod W.p (2 ^ (64 * 6)) := unitMod_pow_two p_odd _

/-- The number at slot `i`. -/
abbrev sv (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (p384.sl i) 6

theorem mul_zero_pt (P : Point W) : Spec.Weierstrass.mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; simp

end VG.Proof.Ecdsa.RISCV64.P384
