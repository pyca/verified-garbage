module

public import VerifiedGarbage.Proof.Ecdsa.X86.CombRcbCT
import VerifiedGarbage.Proof.Ecdsa.X86.GMul
public import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
public import VerifiedGarbage.Proof.Ecdsa.X86.P192.Verified
public import VerifiedGarbage.Impl.Ecdsa.P192.X86Comb
import VerifiedGarbage.Proof.P192.Comb7
import VerifiedGarbage.Proof.P192.Comb7Shape
import VerifiedGarbage.Proof.Ecdsa.X86.P192.CombLit
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombRcbCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.P192.Verified
meta import VerifiedGarbage.Impl.Ecdsa.P192.X86Comb
meta import VerifiedGarbage.Proof.P192.Comb7
meta import VerifiedGarbage.Proof.P192.Comb7Shape
meta import VerifiedGarbage.Proof.Ecdsa.X86.P192.CombLit
meta import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# ECDSA over P-192 on x86 (32-bit): the comb

P-192 with its seven-bit comb by complete additions (`p192Comb`): the
comb's shape and tables, the taint checks of its code and of the stages of
the signature around it, and the stack the signature uses.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.P192

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem p192Comb_ok : CfgOk p192Comb := (p192_ok).withComb p192d

theorem p192Comb_shape : CombOk p192Comb p192d :=
  ⟨show 1 ≤ 7 ∧ 7 < 9 by decide,
    show 64 * 3 ≤ 7 * 28 ∧ 7 * 28 ≤ 64 * 3 + 8 by decide,
    fun h => Bool.noConfusion h,
    fun _ => show 7 * (28 - 1) ≤ 64 * 3 ∧ 64 * 3 < 7 * 28 by decide⟩

theorem p192Comb_tables (hL : Law p192Comb.C) : CombTbls p192Comb := by
  intro d hd
  have he : p192d = d := Option.some.inj hd
  subst d
  exact ⟨Proof.P192.combOk7 hL, fun h => Bool.noConfusion h⟩

abbrev p192W : List (BitVec 64) := p192Comb.combWords p192d

theorem p192Comb_consts : p192Comb.combConsts = [("VG_P192_COMB", p192W)] := rfl

theorem p192W_length : p192W.length = 10752 :=
  (Proof.Weierstrass.tcombWords_length (n := p192Comb.n) (R := p192Comb.R) (p := p192Comb.C.p)
    (H := 64) (tbl := Impl.P192.comb7) Proof.P192.comb7_length Proof.P192.comb7_rows).trans rfl

/-- An iteration of the comb. -/
def combStep : Prog isa := (p192Comb.combCfg p192d).step
materialize_code combStep

/-- The taint checks of the comb's code. -/
theorem combCT : CombRcbCT p192Comb p192d where
  prep := RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)
  init := RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)
  step := fun b => by
    change RelCT isa _ combStep _
    cases b <;> exact RelCT.taint (A := sseTaint) _ (fun _ _ h => h) (by taint_decide)
  sp := by
    change SpOk combStep 20
    exact ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

/-- The constant time of the comb, as the stages take it. -/
theorem p192Comb_gMul (hL : Law p192Comb.C) {scratchSecond : Bool} :
    GMulRel p192Comb p192d scratchSecond :=
  GMulRel.of_body (d := p192d) (p192Comb_ok) rfl (gMulRcb_rel (p192Comb_ok) hL (p192Comb_tables hL) rfl p192Comb_shape rfl combCT)

def signPrepCode : Prog isa := p192Comb.signPrep
def signTailCode : Prog isa := p192Comb.signTail
materialize_code signPrepCode
materialize_code signTailCode

/-- The taint checks of the stages of the signature around the comb. -/
theorem signCT : SignStagesCT p192Comb where
  prep := by
    change RelCT isa _ signPrepCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)
  tail := by
    change RelCT isa _ signTailCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)

/-- No instruction of the signature writes `esp`, and its calls use 24 bytes of stack. -/
theorem signComb_sp : SpOk signP192Comb p192Comb.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

end VG.Proof.Ecdsa.X86.P192
