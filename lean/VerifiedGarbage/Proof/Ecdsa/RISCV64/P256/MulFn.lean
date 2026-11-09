module

public import VerifiedGarbage.Impl.Ecdsa.P256.RISCV64
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Verified
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# P-256 on RISC-V: the facts the proofs share

The facts the proofs of `vg_p256_mul` and its callers share: P-256's field
functions meet the contracts by register (`field_ok`), `2^256` is a unit
modulo the odd `p` (`unit`), the number at a slot (`sv`), and `[0]P = O`
(`mul_zero_pt`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P256

open VG VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- P-256. -/
abbrev W : Curve := Spec.P256.curve

theorem field_ok : FieldOk p256Field :=
  ⟨P256Field.mul_rv, P256Field.add_rv, P256Field.sub_rv,
    Impl.Weierstrass.RISCV64.P256Field.mulFn_noFrames,
    Impl.Weierstrass.RISCV64.P256Field.addFn_noFrames, Impl.Weierstrass.RISCV64.P256Field.subFn_noFrames,
    P256Field.mulA_rv, P256Field.addA_rv, P256Field.subA_rv,
    Impl.Weierstrass.RISCV64.P256Field.mulFnA_noFrames,
    Impl.Weierstrass.RISCV64.P256Field.addFnA_noFrames, Impl.Weierstrass.RISCV64.P256Field.subFnA_noFrames⟩

instance : NeZero p256Field.S.m := ⟨by decide⟩

theorem p_odd : W.p % 2 = 1 := by decide

theorem unit : UnitMod W.p (2 ^ (64 * 4)) := unitMod_pow_two p_odd _

/-- The number at slot `i`. -/
abbrev sv (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (p256.sl i) 4

theorem mul_zero_pt (P : Point W) : Spec.Weierstrass.mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; simp

end VG.Proof.Ecdsa.RISCV64.P256
