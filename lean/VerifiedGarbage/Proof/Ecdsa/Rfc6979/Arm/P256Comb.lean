module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.Arm.P256.CombGenerator
public import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Comb
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Ecdsa.Arm.P256.CombLit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Ecdsa.P256.ArmComb
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P256.CombGenerator
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Comb
meta import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P256.CombLit
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.P256.ArmComb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
public import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Umaal
import VerifiedGarbage.Proof.Ecdsa.Arm.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Umaal
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP

/-! ### `Ecdsa.Rfc6979.Arm.P256`, which only this module used -/

section

/-!
# Deterministic ECDSA on 32-bit ARM: P-256

P-256 as the proof's curve (`p256`): scalars of 4 64-bit words, the order
`n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_p256_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at P-256's sizes, which is `Proof.Ecdsa.Arm.signArm`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm

theorem p256_nBits : Spec.Ecdsa.nBits Spec.P256.curve = 256 := by
  show Spec.P256.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.P256.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P256.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h₁, h₂]

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end

/-! RFC 6979 calls the same comb signer as the raw signing API. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Rfc6979.Arm
open VG VG.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P256

theorem p256_comb_core_pre {u : Bool} {s : State}
    (h : (coreK Impl.Ecdsa.Arm.p256 (combSignK u)).pre s) : combSignPre u s := by
  have hk := constsOk_of_core h
  obtain ⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,-⟩ := h
  exact ⟨⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,tbl_of_consts hk
    (List.mem_append_right _ (List.mem_singleton_self _)) (by rw [wr]; simp)⟩,hk⟩

theorem p256_comb_core_ctWith (u : Bool)
    (hct : ConstantTime isa (combSignPre u) (combSignPub u) (Impl.Ecdsa.Arm.signP256CombWith u)) : ConstantTime isa
    (coreK Impl.Ecdsa.Arm.p256 (combSignK u)).pre
    (coreK Impl.Ecdsa.Arm.p256 (combSignK u)).pub (Impl.Ecdsa.Arm.signP256CombWith u) := by
  intro s t ts tt s' t' hs ht pub e1 e2
  obtain ⟨sp,h0,h1,h2,h3,arg,sy⟩ := pub
  exact hct s t ts tt s' t' (p256_comb_core_pre hs) (p256_comb_core_pre ht)
    ⟨⟨sp,h0,h1,h2,h3,arg⟩,sy (p256Comb.tsym, p256CombWords) List.mem_cons_self,
      sy ((Impl.Ecdsa.Arm.p256With u).constSym, (Impl.Ecdsa.Arm.p256With u).constTbl)
        (List.mem_append_right _ (List.mem_singleton_self _))⟩ e1 e2

/-- P-256 with the generator comb, with the group law `hL`, calling
`vg_ecdsa_p256_sign_k`, or with `u` its `_umaal` variant. -/
def p256CombCurveWith (hL : Weierstrass.Law Spec.P256.curve) (u : Bool) : RfcCurve where
  E := Impl.Ecdsa.Arm.p256
  inst := Spec.Ecdsa.P256.inst
  curve := rfl
  big := false
  sizes := ⟨.inr (.inl rfl), .inl rfl, p256_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 32 - Spec.Ecdsa.nBits Spec.P256.curve = 0; rw [p256_nBits]
  coreN := if u then "vg_ecdsa_p256_sign_k" ++ "_umaal" else "vg_ecdsa_p256_sign_k"
  coreConsts := combSignK u
  coreC := Impl.Ecdsa.Arm.signP256CombWith u
  coreX := by
    intro s hs
    obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hL (u := u) (p256_comb_core_pre hs)
    refine ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,?_⟩
    simp only [coreK,coreSigOf]
    rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
    exact post
  coreCT := p256_comb_core_ctWith u (by cases u; exacts [combSign_ct, combSignU_ct])
  coreStack := by cases u <;> lit_decide
  blk := by rfcT_decide

/-- P-256 with the generator comb, with the group law `hL`. -/
def p256CombCurve (hL : Weierstrass.Law Spec.P256.curve) : RfcCurve := p256CombCurveWith hL false

/-- `p256CombCurve`, calling `vg_ecdsa_p256_sign_umaal`. -/
def p256CombCurveU (hL : Weierstrass.Law Spec.P256.curve) : RfcCurve := p256CombCurveWith hL true

/-! ## With the tables of every hash function with HMAC -/

theorem p256T_verified (hL : Weierstrass.Law Spec.P256.curve) :
    Verified Arm.target (signCodeT (p256CombCurve hL) Spec.Ecdsa.Rfc6979.Curves.p256.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.p256 (p256CombCurve hL).coreConsts HmacTable.Arm.vars) :=
  twoT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl (by decide) (by decide) (by decide)
    (by rw [Proof.P256.Arm.comb_words_length]; decide) (by rw [constTbl_length]; decide)

theorem p256UT_verified (hL : Weierstrass.Law Spec.P256.curve) :
    Verified Arm.target (signCodeT (p256CombCurveU hL) Spec.Ecdsa.Rfc6979.Curves.p256.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.p256 (p256CombCurveU hL).coreConsts HmacTable.Arm.vars) :=
  twoT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl (by decide) (by decide) (by decide)
    (by rw [Proof.P256.Arm.comb_words_length]; decide) (by rw [constTbl_length]; decide)

end VG.Proof.Ecdsa.Rfc6979.Arm
