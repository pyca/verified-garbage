module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.RISCV64
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen4
import VerifiedGarbage.Proof.Weierstrass.RISCV64.BrainpoolP256r1Field.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# brainpoolP256r1's field on RISC-V, for `vg_brainpoolp256r1_mul` and its callers

The facts the proofs of `vg_brainpoolp256r1_mul` (`Proof/Ecdsa/RISCV64/BrainpoolP256r1/Window.lean`)
and its callers share: brainpoolP256r1's field functions meet the contracts by register
(`field_ok`), and `R = 2²⁵⁶` is a unit modulo `p` (`unit`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.BrainpoolP256r1

open VG VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- brainpoolp256r1. -/
abbrev W : Curve := Spec.BrainpoolP256r1.curve

private theorem p_ok : Gen4.Ok Impl.Weierstrass.Mont.brainpoolp256r1p.m := ⟨by decide, by decide, by decide⟩

theorem field_ok : FieldOk brainpoolp256r1Field :=
  ⟨Gen4.mul_rv rfl p_ok, Gen4.add_rv rfl p_ok, Gen4.sub_rv rfl p_ok,
    Impl.Weierstrass.RISCV64.BrainpoolP256r1Field.mulFn_noFrames,
    Impl.Weierstrass.RISCV64.BrainpoolP256r1Field.addFn_noFrames, Impl.Weierstrass.RISCV64.BrainpoolP256r1Field.subFn_noFrames,
    Gen4.mulA_rv rfl p_ok, Gen4.addA_rv rfl p_ok, Gen4.subA_rv rfl p_ok,
    Impl.Weierstrass.RISCV64.BrainpoolP256r1Field.mulFnA_noFrames,
    Impl.Weierstrass.RISCV64.BrainpoolP256r1Field.addFnA_noFrames, Impl.Weierstrass.RISCV64.BrainpoolP256r1Field.subFnA_noFrames⟩

instance : NeZero brainpoolp256r1Field.S.m := ⟨by decide⟩

theorem p_odd : W.p % 2 = 1 := by decide

theorem unit : UnitMod W.p (2 ^ (64 * 4)) := unitMod_pow_two p_odd _

/-- The number at slot `i`. -/
abbrev sv (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (brainpoolp256r1.sl i) 4

end VG.Proof.Ecdsa.RISCV64.BrainpoolP256r1
