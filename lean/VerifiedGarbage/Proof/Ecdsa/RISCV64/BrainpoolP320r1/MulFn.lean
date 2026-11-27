module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.RISCV64
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen5.Field
import VerifiedGarbage.Proof.Weierstrass.RISCV64.BrainpoolP320r1Field.Lit
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.BrainpoolP320r1Field.Lit
meta import VerifiedGarbage.Impl.Weierstrass.Layout.Mont
meta import VerifiedGarbage.Impl.Weierstrass.RISCV64.BrainpoolP320r1Field

/-!
# brainpoolP320r1's field on RISC-V, for `vg_brainpoolp320r1_mul` and its callers

The facts the proofs of `vg_brainpoolp320r1_mul` (`Proof/Ecdsa/RISCV64/BrainpoolP320r1/Window.lean`)
and its callers share: brainpoolP320r1's field functions, those modulo any five-word
modulus (`Proof/Weierstrass/RISCV64/Gen5/Field.lean`) for its `p` (`p_ok`), meet the
contracts by register (`field_ok`), and `R = 2³²⁰` is a unit modulo `p` (`unit`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.BrainpoolP320r1

open VG VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- brainpoolP320r1. -/
abbrev W : Curve := Spec.BrainpoolP320r1.curve

private theorem p_ok : Gen5.Ok Impl.Weierstrass.Mont.brainpoolp320r1p.m := ⟨by decide, by decide, by decide⟩

theorem field_ok : FieldOk brainpoolp320r1Field :=
  ⟨Gen5.mul_rv rfl p_ok, Gen5.add_rv rfl p_ok, Gen5.sub_rv rfl p_ok,
    Impl.Weierstrass.RISCV64.BrainpoolP320r1Field.mulFn_noFrames,
    Impl.Weierstrass.RISCV64.BrainpoolP320r1Field.addFn_noFrames, Impl.Weierstrass.RISCV64.BrainpoolP320r1Field.subFn_noFrames,
    Gen5.mulA_rv rfl p_ok, Gen5.addA_rv rfl p_ok, Gen5.subA_rv rfl p_ok,
    Impl.Weierstrass.RISCV64.BrainpoolP320r1Field.mulFnA_noFrames,
    Impl.Weierstrass.RISCV64.BrainpoolP320r1Field.addFnA_noFrames, Impl.Weierstrass.RISCV64.BrainpoolP320r1Field.subFnA_noFrames⟩

instance : NeZero brainpoolp320r1Field.S.m := ⟨by decide⟩

theorem p_odd : W.p % 2 = 1 := by decide

theorem unit : UnitMod W.p (2 ^ (64 * 5)) := by
  have h := unitMod_pow_two (m := W.p) p_odd (64 * 5)
  exact h

/-- The number at slot `i`. -/
abbrev sv (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (brainpoolp320r1.sl i) 5

/-! The constant-time analyses of the calls of the functions of brainpoolP320r1's `p` from their
arguments, each done once for every check of code that calls it (`taint_decide_sum`), which keep
what is public of `s0`–`s5`: the functions write none of them. -/
taint_summary pMulSum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.Mont.brainpoolp320r1p.fn "mul") Impl.Weierstrass.RISCV64.BrainpoolP320r1Field.mulFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5])
taint_summary pAddSum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.Mont.brainpoolp320r1p.fn "add") Impl.Weierstrass.RISCV64.BrainpoolP320r1Field.addFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5])
taint_summary pSubSum : taint (Taint.ofRegs [.a0, .a1, .a2, .a3])
  (.call (Impl.Weierstrass.Mont.brainpoolp320r1p.fn "sub") Impl.Weierstrass.RISCV64.BrainpoolP320r1Field.subFnA)
  keeping (Taint.ofRegs [.s0, .s1, .s2, .s3, .s4, .s5])

end VG.Proof.Ecdsa.RISCV64.BrainpoolP320r1
