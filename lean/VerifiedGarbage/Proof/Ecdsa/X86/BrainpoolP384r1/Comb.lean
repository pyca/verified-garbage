module

public import VerifiedGarbage.Proof.Ecdsa.X86.CombRcbCT
public import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP384r1.Verified
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86Comb
import VerifiedGarbage.Proof.BrainpoolP384r1.Comb7
import VerifiedGarbage.Proof.BrainpoolP384r1.Comb7Shape
import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP384r1.CombLit
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombRcbCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP384r1.Verified
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86Comb
meta import VerifiedGarbage.Proof.BrainpoolP384r1.Comb7
meta import VerifiedGarbage.Proof.BrainpoolP384r1.Comb7Shape
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP384r1.CombLit
meta import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# ECDSA over brainpoolP384r1 on x86 (32-bit): the comb

brainpoolP384r1 with its seven-bit comb by complete additions (`brainpoolp384r1Comb`): the
comb's shape and tables, the taint checks of its code and of the stages of
the signature around it, and the stack the signature uses.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.BrainpoolP384r1

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem brainpoolp384r1Comb_ok : CfgOk brainpoolp384r1Comb := (brainpoolp384r1_ok).withComb brainpoolp384r1d

theorem brainpoolp384r1Comb_shape : CombOk brainpoolp384r1Comb brainpoolp384r1d :=
  ⟨show 1 ≤ 7 ∧ 7 < 9 by decide,
    show 64 * 6 ≤ 7 * 55 ∧ 7 * 55 ≤ 64 * 6 + 8 by decide,
    fun h => Bool.noConfusion h,
    fun _ => show 7 * (55 - 1) ≤ 64 * 6 ∧ 64 * 6 < 7 * 55 by decide⟩

theorem brainpoolp384r1Comb_tables (hL : Law brainpoolp384r1Comb.C) : CombTbls brainpoolp384r1Comb := by
  intro d hd
  have he : brainpoolp384r1d = d := Option.some.inj hd
  subst d
  exact ⟨Proof.BrainpoolP384r1.combOk7 hL, fun h => Bool.noConfusion h⟩

abbrev brainpoolp384r1W : List (BitVec 64) := brainpoolp384r1Comb.combWords brainpoolp384r1d

theorem brainpoolp384r1Comb_consts : brainpoolp384r1Comb.combConsts = [("VG_BRAINPOOLP384R1_COMB", brainpoolp384r1W)] := rfl

theorem brainpoolp384r1W_length : brainpoolp384r1W.length = 42240 :=
  (Proof.Weierstrass.tcombWords_length (n := brainpoolp384r1Comb.n) (R := brainpoolp384r1Comb.R) (p := brainpoolp384r1Comb.C.p)
    (H := 64) (tbl := Impl.BrainpoolP384r1.comb7) Proof.BrainpoolP384r1.comb7_length Proof.BrainpoolP384r1.comb7_rows).trans rfl

/-- An iteration of the comb. -/
def combStep : Prog isa := (brainpoolp384r1Comb.combCfg brainpoolp384r1d).step
materialize_code combStep

/-- The taint checks of the comb's code. -/
theorem combCT : CombRcbCT brainpoolp384r1Comb brainpoolp384r1d where
  prep := RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)
  init := RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)
  step := fun b => by
    change RelCT isa _ combStep _
    cases b <;> exact RelCT.taint (A := sseTaint) _ (fun _ _ h => h) (by taint_decide)
  sp := by
    change SpOk combStep 20
    exact ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

/-- The constant time of the comb, as the stages take it. -/
theorem brainpoolp384r1Comb_gMul (hL : Law brainpoolp384r1Comb.C) {scratchSecond : Bool} :
    GMulRel brainpoolp384r1Comb brainpoolp384r1d scratchSecond :=
  gMulRcb_rel (brainpoolp384r1Comb_ok) hL (brainpoolp384r1Comb_tables hL) rfl brainpoolp384r1Comb_shape rfl combCT

def signPrepCode : Prog isa := brainpoolp384r1Comb.signPrep
def signTailCode : Prog isa := brainpoolp384r1Comb.signTail
materialize_code signPrepCode
materialize_code signTailCode

/-- The taint checks of the stages of the signature around the comb. -/
theorem signCT : SignStagesCT brainpoolp384r1Comb where
  prep := by
    change RelCT isa _ signPrepCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)
  tail := by
    change RelCT isa _ signTailCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)

/-- No instruction of the signature writes `esp`, and its calls use 20 bytes of stack. -/
theorem signComb_sp : SpOk signBrainpoolP384r1Comb brainpoolp384r1Comb.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

end VG.Proof.Ecdsa.X86.BrainpoolP384r1
