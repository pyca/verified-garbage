module

public import VerifiedGarbage.Proof.Ecdsa.X86.CombRcbCT
public import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP320r1.Verified
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.X86Comb
import VerifiedGarbage.Proof.BrainpoolP320r1.Comb7
import VerifiedGarbage.Proof.BrainpoolP320r1.Comb7Shape
import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP320r1.CombLit
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombRcbCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP320r1.Verified
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.X86Comb
meta import VerifiedGarbage.Proof.BrainpoolP320r1.Comb7
meta import VerifiedGarbage.Proof.BrainpoolP320r1.Comb7Shape
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP320r1.CombLit
meta import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# ECDSA over brainpoolP320r1 on x86 (32-bit): the comb

brainpoolP320r1 with its seven-bit comb by complete additions (`brainpoolp320r1Comb`): the
comb's shape and tables, the taint checks of its code and of the stages of
the signature around it, and the stack the signature uses.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.BrainpoolP320r1

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem brainpoolp320r1Comb_ok : CfgOk brainpoolp320r1Comb := (brainpoolp320r1_ok).withComb brainpoolp320r1d

theorem brainpoolp320r1Comb_shape : CombOk brainpoolp320r1Comb brainpoolp320r1d :=
  ⟨show 1 ≤ 7 ∧ 7 < 9 by decide,
    show 64 * 5 ≤ 7 * 46 ∧ 7 * 46 ≤ 64 * 5 + 8 by decide,
    fun h => Bool.noConfusion h,
    fun _ => show 7 * (46 - 1) ≤ 64 * 5 ∧ 64 * 5 < 7 * 46 by decide⟩

theorem brainpoolp320r1Comb_tables (hL : Law brainpoolp320r1Comb.C) : CombTbls brainpoolp320r1Comb := by
  intro d hd
  have he : brainpoolp320r1d = d := Option.some.inj hd
  subst d
  exact ⟨Proof.BrainpoolP320r1.combOk7 hL, fun h => Bool.noConfusion h⟩

abbrev brainpoolp320r1W : List (BitVec 64) := brainpoolp320r1Comb.combWords brainpoolp320r1d

theorem brainpoolp320r1Comb_consts : brainpoolp320r1Comb.combConsts = [("VG_BRAINPOOLP320R1_COMB", brainpoolp320r1W)] := rfl

theorem brainpoolp320r1W_length : brainpoolp320r1W.length = 29440 :=
  (Proof.Weierstrass.tcombWords_length (n := brainpoolp320r1Comb.n) (R := brainpoolp320r1Comb.R) (p := brainpoolp320r1Comb.C.p)
    (H := 64) (tbl := Impl.BrainpoolP320r1.comb7) Proof.BrainpoolP320r1.comb7_length Proof.BrainpoolP320r1.comb7_rows).trans rfl

/-- An iteration of the comb. -/
def combStep : Prog isa := (brainpoolp320r1Comb.combCfg brainpoolp320r1d).step
materialize_code combStep

/-- The taint checks of the comb's code. -/
theorem combCT : CombRcbCT brainpoolp320r1Comb brainpoolp320r1d where
  prep := RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)
  init := RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)
  step := fun b => by
    change RelCT isa _ combStep _
    cases b <;> exact RelCT.taint (A := sseTaint) _ (fun _ _ h => h) (by taint_decide)
  sp := by
    change SpOk combStep 20
    exact ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

/-- The constant time of the comb, as the stages take it. -/
theorem brainpoolp320r1Comb_gMul (hL : Law brainpoolp320r1Comb.C) {scratchSecond : Bool} :
    GMulRel brainpoolp320r1Comb brainpoolp320r1d scratchSecond :=
  gMulRcb_rel (brainpoolp320r1Comb_ok) hL (brainpoolp320r1Comb_tables hL) rfl brainpoolp320r1Comb_shape rfl combCT

def signPrepCode : Prog isa := brainpoolp320r1Comb.signPrep
def signTailCode : Prog isa := brainpoolp320r1Comb.signTail
materialize_code signPrepCode
materialize_code signTailCode

/-- The taint checks of the stages of the signature around the comb. -/
theorem signCT : SignStagesCT brainpoolp320r1Comb where
  prep := by
    change RelCT isa _ signPrepCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)
  tail := by
    change RelCT isa _ signTailCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)

/-- No instruction of the signature writes `esp`, and its calls use 20 bytes of stack. -/
theorem signComb_sp : SpOk signBrainpoolP320r1Comb brainpoolp320r1Comb.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

end VG.Proof.Ecdsa.X86.BrainpoolP320r1
