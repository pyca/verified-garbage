module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.Arm.P224.CombGenerator
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Comb
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.CombLit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Ecdsa.P224.ArmComb
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P224.CombGenerator
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Comb
meta import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P224.CombLit
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.P224.ArmComb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
public import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Umaal
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Lit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Umaal
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP

/-! ### `Ecdsa.Rfc6979.Arm.P224`, which only this module used -/

section

/-!
# Deterministic ECDSA on 32-bit ARM: P-224

P-224 as the proof's curve (`p224`): scalars of 28 bytes in 4 64-bit words, the order
`n` of exactly 224 bits with `2^224 < 2 n`, and `vg_ecdsa_p224_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at P-224's sizes, which is `Proof.Ecdsa.Arm.P224.signArm`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm

theorem p224_nBits : Spec.Ecdsa.nBits Spec.P224.curve = 224 := by
  show Spec.P224.curve.n.log2 + 1 = 224
  have h₁ : 223 ≤ Spec.P224.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P224.curve.n.log2 < 224 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h₁, h₂]

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end

/-! Deterministic P-224/SHA-224 signing through the generator comb: the comb
signer as RFC 6979's core (`p224CombCurve`), and the contract with its table. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Rfc6979.Arm
open VG VG.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P224

theorem p224_comb_core_pre {u : Bool} {s : State}
    (h : (coreK Impl.Ecdsa.Arm.p224 (combSignK u)).pre s) : combSignPre u s := by
  have hk := constsOk_of_core h
  obtain ⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,-⟩ := h
  exact ⟨⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,fun _ => tbl_of_consts hk
    (List.mem_append_right _ (List.mem_singleton_self _)) (by rw [wr]; simp)⟩,hk⟩

theorem p224_comb_core_ctWith (u : Bool)
    (hct : ConstantTime isa (combSignPre u) (combSignPub u) (Impl.Ecdsa.Arm.signP224CombWith u)) : ConstantTime isa
    (coreK Impl.Ecdsa.Arm.p224 (combSignK u)).pre
    (coreK Impl.Ecdsa.Arm.p224 (combSignK u)).pub (Impl.Ecdsa.Arm.signP224CombWith u) := by
  intro s t ts tt s' t' hs ht pub e1 e2
  obtain ⟨sp,h0,h1,h2,h3,arg,sy⟩ := pub
  exact hct s t ts tt s' t' (p224_comb_core_pre hs) (p224_comb_core_pre ht)
    ⟨⟨sp,h0,h1,h2,h3,arg⟩,sy (p224Comb.tsym, p224CombWords) List.mem_cons_self,
      sy ((Impl.Ecdsa.Arm.p224With u).constSym, (Impl.Ecdsa.Arm.p224With u).constTbl)
        (List.mem_append_right _ (List.mem_singleton_self _))⟩ e1 e2

/-- P-224 with the generator comb, with the group law `hL`, calling
`vg_ecdsa_p224_sign_k`, or with `u` its `_umaal` variant. -/
def p224CombCurveWith (hL : Weierstrass.Law Spec.P224.curve) (u : Bool) : RfcCurve where
  E := Impl.Ecdsa.Arm.p224
  inst := Spec.Ecdsa.P224.inst
  curve := rfl
  big := false
  sizes := ⟨.inr (.inl rfl), .inr ⟨rfl, rfl⟩, p224_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 28 - Spec.Ecdsa.nBits Spec.P224.curve = 0; rw [p224_nBits]
  coreN := if u then "vg_ecdsa_p224_sign_k" ++ "_umaal" else "vg_ecdsa_p224_sign_k"
  coreConsts := combSignK u
  coreC := Impl.Ecdsa.Arm.signP224CombWith u
  coreX := by
    intro s hs
    obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hL (u := u) (p224_comb_core_pre hs)
    refine ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,?_⟩
    simp only [coreK,coreSigOf]
    rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
    exact post
  coreCT := p224_comb_core_ctWith u (by cases u; exacts [combSign_ct, combSignU_ct])
  coreStack := by cases u <;> lit_decide
  blk := by rfcT_decide

/-- P-224 with the generator comb, with the group law `hL`. -/
def p224CombCurve (hL : Weierstrass.Law Spec.P224.curve) : RfcCurve := p224CombCurveWith hL false

/-- `p224CombCurve`, calling `vg_ecdsa_p224_sign_umaal`. -/
def p224CombCurveU (hL : Weierstrass.Law Spec.P224.curve) : RfcCurve := p224CombCurveWith hL true

/-! ## With the tables of every hash function with HMAC -/

theorem p224T_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified Arm.target (signCodeT (p224CombCurve hL) Spec.Ecdsa.Rfc6979.Curves.p224.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.p224 (p224CombCurve hL).coreConsts HmacTable.Arm.vars) :=
  twoT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl (by decide) (by decide) (by decide)
    (by rw [Proof.P224.Arm.comb_words_length]; decide) (by rw [constTbl_length]; decide)

theorem p224UT_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified Arm.target (signCodeT (p224CombCurveU hL) Spec.Ecdsa.Rfc6979.Curves.p224.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.p224 (p224CombCurveU hL).coreConsts HmacTable.Arm.vars) :=
  twoT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl (by decide) (by decide) (by decide)
    (by rw [Proof.P224.Arm.comb_words_length]; decide) (by rw [constTbl_length]; decide)

end VG.Proof.Ecdsa.Rfc6979.Arm
