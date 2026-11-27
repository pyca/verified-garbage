module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.CombGenerator
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Comb
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Ecdsa.Arm.P384.CombLit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Ecdsa.P384.ArmComb
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P384.CombGenerator
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Comb
meta import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P384.CombLit
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.P384.ArmComb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Umaal
import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Umaal
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP

/-! ### `Ecdsa.Rfc6979.Arm.P384`, which only this module used -/

section

/-!
# Deterministic ECDSA on 32-bit ARM: P-384

P-384 as the proof's curve (`p384`): scalars of 6 64-bit words, the order
`n` of exactly 384 bits with `2^384 < 2 n`, and `vg_ecdsa_p384_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at P-384's sizes, which is `Proof.Ecdsa.Arm.P384.signArm`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm

theorem p384_nBits : Spec.Ecdsa.nBits Spec.P384.curve = 384 := by
  show Spec.P384.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.P384.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P384.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h₁, h₂]

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end

/-! Deterministic P-384/SHA-384 signing through the generator comb: the comb
signer as RFC 6979's core (`p384CombCurve`), and the contract with its table. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Rfc6979.Arm
open VG VG.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P384

theorem p384_comb_core_pre {u : Bool} {s : State}
    (h : (coreK Impl.Ecdsa.Arm.p384 (combSignK u)).pre s) : combSignPre u s := by
  have hk := constsOk_of_core h
  obtain ⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,-⟩ := h
  exact ⟨⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,tbl_of_consts hk
    (List.mem_append_right _ (List.mem_singleton_self _)) (by rw [wr]; simp)⟩,hk⟩

theorem p384_comb_core_ctWith (u : Bool)
    (hct : ConstantTime isa (combSignPre u) (combSignPub u) (Impl.Ecdsa.Arm.signP384CombWith u)) : ConstantTime isa
    (coreK Impl.Ecdsa.Arm.p384 (combSignK u)).pre
    (coreK Impl.Ecdsa.Arm.p384 (combSignK u)).pub (Impl.Ecdsa.Arm.signP384CombWith u) := by
  intro s t ts tt s' t' hs ht pub e1 e2
  obtain ⟨sp,h0,h1,h2,h3,arg,sy⟩ := pub
  exact hct s t ts tt s' t' (p384_comb_core_pre hs) (p384_comb_core_pre ht)
    ⟨⟨sp,h0,h1,h2,h3,arg⟩,sy (p384Comb.tsym, p384CombWords) List.mem_cons_self,
      sy ((Impl.Ecdsa.Arm.p384With u).constSym, (Impl.Ecdsa.Arm.p384With u).constTbl)
        (List.mem_append_right _ (List.mem_singleton_self _))⟩ e1 e2

/-- P-384 with the generator comb, with the group law `hL`, calling
`vg_ecdsa_p384_sign_k`, or with `u` its `_umaal` variant. -/
def p384CombCurveWith (hL : Weierstrass.Law Spec.P384.curve) (u : Bool) : RfcCurve where
  E := Impl.Ecdsa.Arm.p384
  inst := Spec.Ecdsa.P384.inst
  curve := rfl
  big := false
  sizes := ⟨.inr (.inr (.inl rfl)), .inl rfl, p384_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 48 - Spec.Ecdsa.nBits Spec.P384.curve = 0; rw [p384_nBits]
  coreN := if u then "vg_ecdsa_p384_sign_k" ++ "_umaal" else "vg_ecdsa_p384_sign_k"
  coreConsts := combSignK u
  coreC := Impl.Ecdsa.Arm.signP384CombWith u
  coreX := by
    intro s hs
    obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hL (u := u) (p384_comb_core_pre hs)
    refine ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,?_⟩
    simp only [coreK,coreSigOf]
    rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
    exact post
  coreCT := p384_comb_core_ctWith u (by cases u; exacts [combSign_ct, combSignU_ct])
  coreStack := by cases u <;> lit_decide
  blk := by rfcT_decide

/-- P-384 with the generator comb, with the group law `hL`. -/
def p384CombCurve (hL : Weierstrass.Law Spec.P384.curve) : RfcCurve := p384CombCurveWith hL false

/-- `p384CombCurve`, calling `vg_ecdsa_p384_sign_umaal`. -/
def p384CombCurveU (hL : Weierstrass.Law Spec.P384.curve) : RfcCurve := p384CombCurveWith hL true

/-! ## With the tables of every hash function with HMAC -/

theorem p384T_verified (hL : Weierstrass.Law Spec.P384.curve) :
    Verified Arm.target (signCodeT (p384CombCurve hL) Spec.Ecdsa.Rfc6979.Curves.p384.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.p384 (p384CombCurve hL).coreConsts HmacTable.Arm.vars) :=
  twoT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl (by decide) (by decide) (by decide)
    (by rw [Proof.P384.Arm.comb_words_length]; decide) (by rw [constTbl_length]; decide)

theorem p384UT_verified (hL : Weierstrass.Law Spec.P384.curve) :
    Verified Arm.target (signCodeT (p384CombCurveU hL) Spec.Ecdsa.Rfc6979.Curves.p384.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.p384 (p384CombCurveU hL).coreConsts HmacTable.Arm.vars) :=
  twoT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl (by decide) (by decide) (by decide)
    (by rw [Proof.P384.Arm.comb_words_length]; decide) (by rw [constTbl_length]; decide)

end VG.Proof.Ecdsa.Rfc6979.Arm
