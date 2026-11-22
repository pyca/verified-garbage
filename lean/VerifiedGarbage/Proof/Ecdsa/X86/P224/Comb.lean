module

public import VerifiedGarbage.Proof.Ecdsa.X86.CombRcbCT
import VerifiedGarbage.Proof.Ecdsa.X86.GMul
public import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
public import VerifiedGarbage.Proof.Ecdsa.X86.P224.Verified
public import VerifiedGarbage.Impl.Ecdsa.P224.X86Comb
import VerifiedGarbage.Proof.P224.Comb7
import VerifiedGarbage.Proof.P224.Comb7Shape
import VerifiedGarbage.Proof.Ecdsa.X86.P224.CombLit
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombRcbCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.P224.Verified
meta import VerifiedGarbage.Impl.Ecdsa.P224.X86Comb
meta import VerifiedGarbage.Proof.P224.Comb7
meta import VerifiedGarbage.Proof.P224.Comb7Shape
meta import VerifiedGarbage.Proof.Ecdsa.X86.P224.CombLit
meta import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# ECDSA over P-224 on x86 (32-bit): the comb

P-224 with its seven-bit comb by complete additions (`p224Comb`): the
comb's shape and tables, the taint checks of its code and of the stages of
the signature around it, and the stack the signature uses.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.P224

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem p224Comb_ok : CfgOk p224Comb := (p224_ok).withComb p224d

theorem p224Comb_shape : CombOk p224Comb p224d :=
  ⟨show 1 ≤ 7 ∧ 7 < 9 by decide,
    show 64 * 4 ≤ 7 * 37 ∧ 7 * 37 ≤ 64 * 4 + 8 by decide,
    fun h => Bool.noConfusion h,
    fun _ => show 7 * (37 - 1) ≤ 64 * 4 ∧ 64 * 4 < 7 * 37 by decide⟩

theorem p224Comb_tables (hL : Law p224Comb.C) : CombTbls p224Comb := by
  intro d hd
  have he : p224d = d := Option.some.inj hd
  subst d
  exact ⟨Proof.P224.combOk7 hL, fun h => Bool.noConfusion h⟩

abbrev p224W : List (BitVec 64) := p224Comb.combWords p224d

theorem p224Comb_consts : p224Comb.combConsts = [("VG_P224_COMB", p224W)] := rfl

theorem p224W_length : p224W.length = 18944 :=
  (Proof.Weierstrass.tcombWords_length (n := p224Comb.n) (R := p224Comb.R) (p := p224Comb.C.p)
    (H := 64) (tbl := Impl.P224.p224Comb7) Proof.P224.p224Comb7_length Proof.P224.p224Comb7_rows).trans rfl

/-- An iteration of the comb. -/
def combStep : Prog isa := (p224Comb.combCfg p224d).step
materialize_code combStep

/-- The taint checks of the comb's code. -/
theorem combCT : CombRcbCT p224Comb p224d where
  prep := RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)
  init := RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)
  step := fun b => by
    change RelCT isa _ combStep _
    cases b <;> exact RelCT.taint (A := sseTaint) _ (fun _ _ h => h) (by taint_decide)
  sp := by
    change SpOk combStep 20
    exact ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

/-- The constant time of the comb, as the stages take it. -/
theorem p224Comb_gMul (hL : Law p224Comb.C) {scratchSecond : Bool} :
    GMulRel p224Comb p224d scratchSecond :=
  GMulRel.of_body (d := p224d) (p224Comb_ok) rfl (gMulRcb_rel (p224Comb_ok) hL (p224Comb_tables hL) rfl p224Comb_shape rfl combCT)

def signPrepCode : Prog isa := p224Comb.signPrep
def signTailCode : Prog isa := p224Comb.signTail
materialize_code signPrepCode
materialize_code signTailCode

/-- The taint checks of the stages of the signature around the comb. -/
theorem signCT : SignStagesCT p224Comb where
  prep := by
    change RelCT isa _ signPrepCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)
  tail := by
    change RelCT isa _ signTailCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)

/-- No instruction of the signature writes `esp`, and its calls use 24 bytes of stack. -/
theorem signComb_sp : SpOk signP224Comb p224Comb.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

end VG.Proof.Ecdsa.X86.P224
