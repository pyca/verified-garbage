import VerifiedGarbage.Impl.P256.Booth
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lit
import VerifiedGarbage.Proof.EcKey.AArch64.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombMixed
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombOut

/-! The comb that signing and public keys share is checked once, and their
literals read it.

The comb's forwarded field programs (`CombArithmetic.program`) are the
optimizer's output, which `Forward.CombMixed` and `Forward.CombOut` already
have as literals: the comb's literal is its code with those, by rewriting,
rather than the kernel running the optimizer again. -/

namespace VG.Impl.P256.Booth
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

private theorem program_eq (k : CombArithmetic.Kind) :
    CombArithmetic.program CombArithmetic.K.M (CombArithmetic.operations k) =
      .block (VG.Proof.Weierstrass.AArch64.Forward.CombArithmetic.optimized k) := by
  rw [CombArithmetic.program,
    ite_eq_left ⟨rfl, List.mem_map.mpr ⟨k, by cases k <;> decide, rfl⟩⟩]
  rfl

private theorem mixed_eq : CombArithmetic.program CombArithmetic.K.M
    (maddJ CombArithmetic.K.S CombArithmetic.K.A CombArithmetic.K.E CombArithmetic.K.D) =
    .block VG.Proof.Weierstrass.AArch64.Forward.CombMixed.rightCode.lit :=
  (program_eq .mixed).trans
    (congrArg Code.block VG.Proof.Weierstrass.AArch64.Forward.CombMixed.optimized_lit)

private theorem out_eq : CombArithmetic.program CombArithmetic.K.M CombArithmetic.K.outOps =
    .block VG.Proof.Weierstrass.AArch64.Forward.CombOut.rightCode.lit :=
  (program_eq .out).trans
    (congrArg Code.block VG.Proof.Weierstrass.AArch64.Forward.CombOut.optimized_lit)

/-- `comb`, with the literals of its field programs. -/
noncomputable def comb.lit : Prog isa :=
  .seq CombArithmetic.K.first <|
  .seq (.loop
    (.seq (.block (CombArithmetic.K.bdigit true ++ CombArithmetic.K.select)) <|
      .seq (.block CombArithmetic.K.bnegY) <|
      .seq (.block VG.Proof.Weierstrass.AArch64.Forward.CombMixed.rightCode.lit) <|
      .seq (.block (nzMask CombArithmetic.K.M.n CombArithmetic.K.A.z ++
        selPt CombArithmetic.K.M.n CombArithmetic.K.D CombArithmetic.K.E CombArithmetic.K.D)) <|
      .block (CombArithmetic.K.bdigit true ++ [Mont.AArch64.zero7, .movz .x .x5 1 0, .subs .x .x16 .x2 .x5,
        .sbc .x .x3 .x7 .x7] ++ selPt CombArithmetic.K.M.n CombArithmetic.K.A CombArithmetic.K.D
          CombArithmetic.K.A ++
        [.addImm .x .x19 .x19 1, .subImm .x .x4 .x19 CombArithmetic.K.J]))
    (.nonzero .x .x4)) <|
  .seq (.block CombArithmetic.K.outFix) (.block VG.Proof.Weierstrass.AArch64.Forward.CombOut.rightCode.lit)

theorem comb.lit_eq : comb = comb.lit := by
  simp only [comb, TCombCfg.combJWith, TCombCfg.stepJWith]
  rw [mixed_eq, out_eq]
  rfl

materialize_code sign
materialize_code publicKey

end VG.Impl.P256.Booth
