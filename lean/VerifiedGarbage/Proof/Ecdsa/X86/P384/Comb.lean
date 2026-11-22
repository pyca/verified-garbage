module

public import VerifiedGarbage.Proof.Ecdsa.X86.CombRcbCT
import VerifiedGarbage.Proof.Ecdsa.X86.GMul
public import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
public import VerifiedGarbage.Proof.Ecdsa.X86.P384.Verified
public import VerifiedGarbage.Impl.Ecdsa.P384.X86Comb
import VerifiedGarbage.Proof.P384.Comb7
import VerifiedGarbage.Proof.P384.Comb7Shape
import VerifiedGarbage.Proof.Ecdsa.X86.P384.CombLit
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombRcbCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.P384.Verified
meta import VerifiedGarbage.Impl.Ecdsa.P384.X86Comb
meta import VerifiedGarbage.Proof.P384.Comb7
meta import VerifiedGarbage.Proof.P384.Comb7Shape
meta import VerifiedGarbage.Proof.Ecdsa.X86.P384.CombLit
meta import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# ECDSA over P-384 on x86 (32-bit): the comb

P-384 with its seven-bit comb by complete additions (`p384Comb`): the
comb's shape and tables, the taint checks of its code and of the stages of
the signature around it, and the stack the signature uses.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.P384

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem p384Comb_ok : CfgOk p384Comb := (p384_ok).withComb p384d

theorem p384Comb_shape : CombOk p384Comb p384d :=
  ⟨show 1 ≤ 7 ∧ 7 < 9 by decide,
    show 64 * 6 ≤ 7 * 55 ∧ 7 * 55 ≤ 64 * 6 + 8 by decide,
    fun h => Bool.noConfusion h,
    fun _ => show 7 * (55 - 1) ≤ 64 * 6 ∧ 64 * 6 < 7 * 55 by decide⟩

theorem p384Comb_tables (hL : Law p384Comb.C) : CombTbls p384Comb := by
  intro d hd
  have he : p384d = d := Option.some.inj hd
  subst d
  exact ⟨Proof.P384.combOk7 hL, fun h => Bool.noConfusion h⟩

abbrev p384W : List (BitVec 64) := p384Comb.combWords p384d

theorem p384Comb_consts : p384Comb.combConsts = [("VG_P384_COMB", p384W)] := rfl

theorem p384W_length : p384W.length = 42240 :=
  (Proof.Weierstrass.tcombWords_length (n := p384Comb.n) (R := p384Comb.R) (p := p384Comb.C.p)
    (H := 64) (tbl := Impl.P384.p384Comb7) Proof.P384.p384Comb7_length Proof.P384.p384Comb7_rows).trans rfl

/-- An iteration of the comb. -/
def combStep : Prog isa := (p384Comb.combCfg p384d).step
materialize_code combStep

/-- The taint checks of the comb's code. -/
theorem combCT : CombRcbCT p384Comb p384d where
  prep := RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)
  init := RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)
  step := fun b => by
    change RelCT isa _ combStep _
    cases b <;> exact RelCT.taint (A := sseTaint) _ (fun _ _ h => h) (by taint_decide)
  sp := by
    change SpOk combStep 20
    exact ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

/-- The constant time of the comb, as the stages take it. -/
theorem p384Comb_gMul (hL : Law p384Comb.C) {scratchSecond : Bool} :
    GMulRel p384Comb p384d scratchSecond :=
  GMulRel.of_body (d := p384d) (p384Comb_ok) rfl (gMulRcb_rel (p384Comb_ok) hL (p384Comb_tables hL) rfl p384Comb_shape rfl combCT)

def signPrepCode : Prog isa := p384Comb.signPrep
def signTailCode : Prog isa := p384Comb.signTail
materialize_code signPrepCode
materialize_code signTailCode

/-- The taint checks of the stages of the signature around the comb. -/
theorem signCT : SignStagesCT p384Comb where
  prep := by
    change RelCT isa _ signPrepCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)
  tail := by
    change RelCT isa _ signTailCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)

/-- No instruction of the signature writes `esp`, and its calls use 24 bytes of stack. -/
theorem signComb_sp : SpOk signP384Comb p384Comb.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

end VG.Proof.Ecdsa.X86.P384
