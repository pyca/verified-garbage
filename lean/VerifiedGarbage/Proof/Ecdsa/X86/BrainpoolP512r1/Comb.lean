module

public import VerifiedGarbage.Proof.Ecdsa.X86.CombRcbCT
public import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
public import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Config
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86Comb
public import VerifiedGarbage.Proof.Framework.X86.SseTaintMono
import VerifiedGarbage.Proof.BrainpoolP512r1.Comb7
import VerifiedGarbage.Proof.BrainpoolP512r1.Comb7Shape
import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.CombLit
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP512r1
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombRcbCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.Config
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86Comb
meta import VerifiedGarbage.Proof.Framework.X86.SseTaintMono
meta import VerifiedGarbage.Proof.BrainpoolP512r1.Comb7
meta import VerifiedGarbage.Proof.BrainpoolP512r1.Comb7Shape
meta import VerifiedGarbage.Proof.Ecdsa.X86.BrainpoolP512r1.CombLit
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP512r1
meta import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# ECDSA over brainpoolP512r1 on x86 (32-bit): the comb

brainpoolP512r1 with its seven-bit comb by complete additions (`brainpoolp512r1Comb`): the
comb's shape and tables, the taint checks of its code and of the stages of
the signature around it, and the stack the signature uses.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.BrainpoolP512r1

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem brainpoolp512r1Comb_ok : CfgOk brainpoolp512r1Comb := (brainpoolp512r1_ok).withComb brainpoolp512r1d

theorem brainpoolp512r1Comb_shape : CombOk brainpoolp512r1Comb brainpoolp512r1d :=
  ⟨show 1 ≤ 7 ∧ 7 < 9 by decide,
    show 64 * 8 ≤ 7 * 74 ∧ 7 * 74 ≤ 64 * 8 + 8 by decide,
    fun h => Bool.noConfusion h,
    fun _ => show 7 * (74 - 1) ≤ 64 * 8 ∧ 64 * 8 < 7 * 74 by decide⟩

theorem brainpoolp512r1Comb_tables (hL : Law brainpoolp512r1Comb.C) : CombTbls brainpoolp512r1Comb := by
  intro d hd
  have he : brainpoolp512r1d = d := Option.some.inj hd
  subst d
  exact ⟨Proof.BrainpoolP512r1.combOk7 hL, fun h => Bool.noConfusion h⟩

abbrev brainpoolp512r1W : List (BitVec 64) := brainpoolp512r1Comb.combWords brainpoolp512r1d

theorem brainpoolp512r1Comb_consts : brainpoolp512r1Comb.combConsts = [("VG_BRAINPOOLP512R1_COMB", brainpoolp512r1W)] := rfl

theorem brainpoolp512r1W_length : brainpoolp512r1W.length = 75776 :=
  (Proof.Weierstrass.tcombWords_length (n := brainpoolp512r1Comb.n) (R := brainpoolp512r1Comb.R) (p := brainpoolp512r1Comb.C.p)
    (H := 64) (tbl := Impl.BrainpoolP512r1.comb7) Proof.BrainpoolP512r1.comb7_length Proof.BrainpoolP512r1.comb7_rows).trans rfl

/-- An iteration of the comb. -/
def combStep : Prog isa := (brainpoolp512r1Comb.combCfg brainpoolp512r1d).step
materialize_code combStep

/-! The field functions modulo `p`, analysed once from what is public on
entry to their calls from an iteration (`combCallτ`), for each place of the
working space among the regions, in place of each call. -/

taint_summary mulSumF : sseTaint (combCallτ false)
  (Impl.Weierstrass.X86.Mont.mulFn Impl.Weierstrass.Mont.brainpoolp512r1p.k Impl.Weierstrass.Mont.brainpoolp512r1p.m)
taint_summary addSumF : sseTaint (combCallτ false)
  (Impl.Weierstrass.X86.Mont.addFn Impl.Weierstrass.Mont.brainpoolp512r1p.k Impl.Weierstrass.Mont.brainpoolp512r1p.m)
taint_summary subSumF : sseTaint (combCallτ false)
  (Impl.Weierstrass.X86.Mont.subFn Impl.Weierstrass.Mont.brainpoolp512r1p.k Impl.Weierstrass.Mont.brainpoolp512r1p.m)
taint_summary mulSumT : sseTaint (combCallτ true)
  (Impl.Weierstrass.X86.Mont.mulFn Impl.Weierstrass.Mont.brainpoolp512r1p.k Impl.Weierstrass.Mont.brainpoolp512r1p.m)
taint_summary addSumT : sseTaint (combCallτ true)
  (Impl.Weierstrass.X86.Mont.addFn Impl.Weierstrass.Mont.brainpoolp512r1p.k Impl.Weierstrass.Mont.brainpoolp512r1p.m)
taint_summary subSumT : sseTaint (combCallτ true)
  (Impl.Weierstrass.X86.Mont.subFn Impl.Weierstrass.Mont.brainpoolp512r1p.k Impl.Weierstrass.Mont.brainpoolp512r1p.m)

/-- The taint checks of the comb's code. -/
theorem combCT : CombRcbCT brainpoolp512r1Comb brainpoolp512r1d where
  prep := RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)
  init := RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)
  step := fun b => by
    change RelCT isa _ combStep _
    cases b
    · obtain ⟨_, hc⟩ : ∃ h, (sseTaint.check (combτAt false) combStep h).isSome = true := by
        taint_decide_sum [mulSumF, addSumF, subSumF]
      exact RelCT.taint (A := sseTaint) _ (fun _ _ h => h) hc
    · obtain ⟨_, hc⟩ : ∃ h, (sseTaint.check (combτAt true) combStep h).isSome = true := by
        taint_decide_sum [mulSumT, addSumT, subSumT]
      exact RelCT.taint (A := sseTaint) _ (fun _ _ h => h) hc
  sp := by
    change SpOk combStep 20
    exact ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

/-- The constant time of the comb, as the stages take it. -/
theorem brainpoolp512r1Comb_gMul (hL : Law brainpoolp512r1Comb.C) {scratchSecond : Bool} :
    GMulRel brainpoolp512r1Comb brainpoolp512r1d scratchSecond :=
  gMulRcb_rel (brainpoolp512r1Comb_ok) hL (brainpoolp512r1Comb_tables hL) rfl brainpoolp512r1Comb_shape rfl combCT

def signPrepCode : Prog isa := brainpoolp512r1Comb.signPrep
def signTailCode : Prog isa := brainpoolp512r1Comb.signTail
materialize_code signPrepCode
materialize_code signTailCode

/-- The taint checks of the stages of the signature around the comb. -/
theorem signCT : SignStagesCT brainpoolp512r1Comb where
  prep := by
    change RelCT isa _ signPrepCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)
  tail := by
    change RelCT isa _ signTailCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)

/-- No instruction of the signature writes `esp`, and its calls use 20 bytes of stack. -/
theorem signComb_sp : SpOk signBrainpoolP512r1Comb brainpoolp512r1Comb.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

end VG.Proof.Ecdsa.X86.BrainpoolP512r1
