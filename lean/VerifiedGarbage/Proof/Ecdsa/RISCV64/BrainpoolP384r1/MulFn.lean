module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.RISCV64
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen6
import VerifiedGarbage.Proof.Weierstrass.RISCV64.BrainpoolP384r1Field.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# brainpoolP384r1's field on RISC-V, for `vg_brainpoolp384r1_mul` and its callers

The facts the proofs of `vg_brainpoolp384r1_mul` (`Proof/Ecdsa/RISCV64/BrainpoolP384r1/Window.lean`)
and its callers share: brainpoolP384r1's field functions, those modulo any six-word
modulus (`Proof/Weierstrass/RISCV64/Gen6.lean`) for its `p` (`p_ok`), meet the
contracts by register (`field_ok`), and `R = 2³⁸⁴` is a unit modulo `p` (`unit`).
-/

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1

open VG VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- brainpoolP384r1. -/
abbrev W : Curve := Spec.BrainpoolP384r1.curve

private theorem p_ok : Gen6.Ok Impl.Weierstrass.Mont.brainpoolp384r1p.m := ⟨by decide, by decide, by decide⟩

theorem field_ok : FieldOk brainpoolp384r1Field :=
  ⟨Gen6.mul_rv rfl p_ok, Gen6.add_rv rfl p_ok, Gen6.sub_rv rfl p_ok,
    Impl.Weierstrass.RISCV64.BrainpoolP384r1Field.mulFn_noFrames,
    Impl.Weierstrass.RISCV64.BrainpoolP384r1Field.addFn_noFrames, Impl.Weierstrass.RISCV64.BrainpoolP384r1Field.subFn_noFrames,
    Gen6.mulA_rv rfl p_ok, Gen6.addA_rv rfl p_ok, Gen6.subA_rv rfl p_ok,
    Impl.Weierstrass.RISCV64.BrainpoolP384r1Field.mulFnA_noFrames,
    Impl.Weierstrass.RISCV64.BrainpoolP384r1Field.addFnA_noFrames, Impl.Weierstrass.RISCV64.BrainpoolP384r1Field.subFnA_noFrames⟩

instance : NeZero brainpoolp384r1Field.S.m := ⟨by decide⟩

theorem p_odd : W.p % 2 = 1 := by decide

theorem unit : UnitMod W.p (2 ^ (64 * 6)) := unitMod_pow_two p_odd _

/-- The number at slot `i`. -/
abbrev sv (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (brainpoolp384r1.sl i) 6

end VG.Proof.Ecdsa.RISCV64.BrainpoolP384r1
