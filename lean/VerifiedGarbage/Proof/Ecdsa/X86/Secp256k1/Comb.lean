module

public import VerifiedGarbage.Proof.Ecdsa.X86.CombRcbCT
import VerifiedGarbage.Proof.Ecdsa.X86.GMul
public import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
public import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.Verified
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86Comb
import VerifiedGarbage.Proof.Secp256k1.Comb7
import VerifiedGarbage.Proof.Secp256k1.Point
import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.CombLit
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombRcbCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombFunctionCT
meta import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.Verified
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86Comb
meta import VerifiedGarbage.Proof.Secp256k1.Comb7
meta import VerifiedGarbage.Proof.Secp256k1.Point
meta import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.CombLit
meta import VerifiedGarbage.Proof.Weierstrass.TCombWords
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# ECDSA over secp256k1 on x86 (32-bit): the comb

secp256k1 with its seven-bit comb by complete additions (`secp256k1Comb`): the
comb's shape and tables, the taint checks of its code and of the stages of
the signature around it, and the stack the signature uses.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86.Secp256k1

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem secp256k1Comb_ok (hI : Inv.InvSounds) : CfgOk secp256k1Comb := (secp256k1_ok hI).withComb secp256k1d

theorem secp256k1Comb_shape : CombOk secp256k1Comb secp256k1d :=
  ⟨show 1 ≤ 7 ∧ 7 < 9 by decide,
    show 64 * 4 ≤ 7 * 37 ∧ 7 * 37 ≤ 64 * 4 + 8 by decide,
    fun h => Bool.noConfusion h,
    fun _ => show 7 * (37 - 1) ≤ 64 * 4 ∧ 64 * 4 < 7 * 37 by decide⟩

theorem secp256k1Comb_tables (hL : Law secp256k1Comb.C) : CombTbls secp256k1Comb := by
  intro d hd
  have he : secp256k1d = d := Option.some.inj hd
  subst d
  exact ⟨Proof.Secp256k1.combOk7 hL Proof.Secp256k1.onCurve_G, fun h => Bool.noConfusion h⟩

abbrev secp256k1W : List (BitVec 64) := secp256k1Comb.combWords secp256k1d

theorem secp256k1Comb_consts : secp256k1Comb.combConsts = [("VG_SECP256K1_COMB", secp256k1W)] := rfl

/-- The comb has 37 tables (the kernel walks the list once). -/
theorem secp256k1Comb7_length : Impl.Secp256k1.secp256k1Comb7.length = 37 := by decide +kernel

/-- Every table has 64 points (checked by `List.all`, which walks the tables once). -/
theorem secp256k1Comb7_rows : ∀ j < 37, (Impl.Secp256k1.secp256k1Comb7.getD j []).length = 64 := by
  have h := List.all_eq_true.mp (show Impl.Secp256k1.secp256k1Comb7.all (·.length == 64) = true by decide +kernel)
  intro j hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (secp256k1Comb7_length ▸ hj), Option.getD_some]
  exact beq_iff_eq.mp (h _ (List.getElem_mem _))

theorem secp256k1W_length : secp256k1W.length = 18944 :=
  (Proof.Weierstrass.tcombWords_length (n := secp256k1Comb.n) (R := secp256k1Comb.R) (p := secp256k1Comb.C.p)
    (H := 64) (tbl := Impl.Secp256k1.secp256k1Comb7) secp256k1Comb7_length secp256k1Comb7_rows).trans rfl

/-- An iteration of the comb. -/
def combStep : Prog isa := (secp256k1Comb.combCfg secp256k1d).step
materialize_code combStep

/-- The taint checks of the comb's code. -/
theorem combCT : CombRcbCT secp256k1Comb secp256k1d where
  prep := RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)
  init := RelCT.taint (A := taint) _ (fun _ _ h => h) (by taint_decide)
  step := fun b => by
    change RelCT isa _ combStep _
    cases b <;> exact RelCT.taint (A := sseTaint) _ (fun _ _ h => h) (by taint_decide)
  sp := by
    change SpOk combStep 20
    exact ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

/-- The constant time of the comb, as the stages take it. -/
theorem secp256k1Comb_gMul (hL : Law secp256k1Comb.C) (hI : Inv.InvSounds) {scratchSecond : Bool} :
    GMulRel secp256k1Comb secp256k1d scratchSecond :=
  GMulRel.of_body (d := secp256k1d) (secp256k1Comb_ok hI) rfl (gMulRcb_rel (secp256k1Comb_ok hI) hL (secp256k1Comb_tables hL) rfl secp256k1Comb_shape rfl combCT)

def signPrepCode : Prog isa := secp256k1Comb.signPrep
def signTailCode : Prog isa := secp256k1Comb.signTail
materialize_code signPrepCode
materialize_code signTailCode

/-- The taint checks of the stages of the signature around the comb. -/
theorem signCT : SignStagesCT secp256k1Comb where
  prep := by
    change RelCT isa _ signPrepCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)
  tail := by
    change RelCT isa _ signTailCode _
    exact RelCT.taint (A := taint) _ (fun _ _ h => h) (by native_taint_decide)

/-- No instruction of the signature writes `esp`, and its calls use 24 bytes of stack. -/
theorem signComb_sp : SpOk signSecp256k1Comb secp256k1Comb.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

end VG.Proof.Ecdsa.X86.Secp256k1
