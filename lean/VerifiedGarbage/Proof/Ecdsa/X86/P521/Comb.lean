module

public import VerifiedGarbage.Proof.Ecdsa.X86.CombRcbCT
public import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
public import VerifiedGarbage.Proof.Ecdsa.X86.P521.Verified
public import VerifiedGarbage.Impl.Ecdsa.P521.X86Comb
public import VerifiedGarbage.Proof.Framework.X86.SseTaintMono
import VerifiedGarbage.Proof.P521.Comb7
import VerifiedGarbage.Proof.P521.Comb7Shape
import VerifiedGarbage.Proof.Ecdsa.X86.P521.CombLit
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P521
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombRcbCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.P521.Verified
meta import VerifiedGarbage.Impl.Ecdsa.P521.X86Comb
meta import VerifiedGarbage.Proof.Framework.X86.SseTaintMono
meta import VerifiedGarbage.Proof.P521.Comb7
meta import VerifiedGarbage.Proof.P521.Comb7Shape
meta import VerifiedGarbage.Proof.Ecdsa.X86.P521.CombLit
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P521
meta import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# ECDSA over P-521 on x86 (32-bit): the comb

P-521 with its seven-bit comb by complete additions (`p521Comb`): the
comb's shape and tables, the taint checks of its code and of the stages of
the signature around it, and the stack the signature uses.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.P521

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem p521Comb_ok : CfgOk p521Comb := (p521_ok).withComb p521d

theorem p521Comb_shape : CombOk p521Comb p521d :=
  ⟨show 1 ≤ 7 ∧ 7 < 9 by decide,
    show 64 * 9 ≤ 7 * 83 ∧ 7 * 83 ≤ 64 * 9 + 8 by decide,
    fun h => Bool.noConfusion h,
    fun _ => show 7 * (83 - 1) ≤ 64 * 9 ∧ 64 * 9 < 7 * 83 by decide⟩

theorem p521Comb_tables (hL : Law p521Comb.C) : CombTbls p521Comb := by
  intro d hd
  have he : p521d = d := Option.some.inj hd
  subst d
  exact ⟨Proof.P521.combOk7 hL, fun h => Bool.noConfusion h⟩

abbrev p521W : List (BitVec 64) := p521Comb.combWords p521d

theorem p521Comb_consts : p521Comb.combConsts = [("VG_P521_COMB", p521W)] := rfl

theorem p521W_length : p521W.length = 95616 :=
  (Proof.Weierstrass.tcombWords_length (n := p521Comb.n) (R := p521Comb.R) (p := p521Comb.C.p)
    (H := 64) (tbl := Impl.P521.p521Comb7) Proof.P521.p521Comb7_length Proof.P521.p521Comb7_rows).trans rfl

/-- An iteration of the comb. -/
def combStep : Prog isa := (p521Comb.combCfg p521d).step
materialize_code combStep

/-! The field functions modulo `p`, analysed once from what is public on
entry to their calls from an iteration (`combCallτ`), for each place of the
working space among the regions, in place of each call. -/

taint_summary mulSumF : sseTaint (combCallτ false)
  (Impl.Weierstrass.X86.Mont.mulFn Impl.Weierstrass.Mont.p521p.k Impl.Weierstrass.Mont.p521p.m)
taint_summary addSumF : sseTaint (combCallτ false)
  (Impl.Weierstrass.X86.Mont.addFn Impl.Weierstrass.Mont.p521p.k Impl.Weierstrass.Mont.p521p.m)
taint_summary subSumF : sseTaint (combCallτ false)
  (Impl.Weierstrass.X86.Mont.subFn Impl.Weierstrass.Mont.p521p.k Impl.Weierstrass.Mont.p521p.m)
taint_summary mulSumT : sseTaint (combCallτ true)
  (Impl.Weierstrass.X86.Mont.mulFn Impl.Weierstrass.Mont.p521p.k Impl.Weierstrass.Mont.p521p.m)
taint_summary addSumT : sseTaint (combCallτ true)
  (Impl.Weierstrass.X86.Mont.addFn Impl.Weierstrass.Mont.p521p.k Impl.Weierstrass.Mont.p521p.m)
taint_summary subSumT : sseTaint (combCallτ true)
  (Impl.Weierstrass.X86.Mont.subFn Impl.Weierstrass.Mont.p521p.k Impl.Weierstrass.Mont.p521p.m)

/-- The taint checks of the comb's code. -/
theorem combCT : CombRcbCT p521Comb p521d where
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
theorem p521Comb_gMul (hL : Law p521Comb.C) {scratchSecond : Bool} :
    GMulRel p521Comb p521d scratchSecond :=
  gMulRcb_rel (p521Comb_ok) hL (p521Comb_tables hL) rfl p521Comb_shape rfl combCT

def signPrepCode : Prog isa := p521Comb.signPrep
def signTailCode : Prog isa := p521Comb.signTail
materialize_code signPrepCode
materialize_code signTailCode

/-- The taint checks of the stages of the signature around the comb. -/
theorem signCT : SignStagesCT p521Comb where
  prep := by
    change RelCT isa _ signPrepCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)
  tail := by
    change RelCT isa _ signTailCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)

/-- No instruction of the signature writes `esp`, and its calls use 20 bytes of stack. -/
theorem signComb_sp : SpOk signP521Comb p521Comb.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

end VG.Proof.Ecdsa.X86.P521
