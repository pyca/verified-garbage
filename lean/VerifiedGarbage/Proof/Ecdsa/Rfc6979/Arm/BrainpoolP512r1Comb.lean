module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.CombGenerator
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Comb
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.CombLit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.ArmComb
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.CombGenerator
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Comb
meta import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.CombLit
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.ArmComb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Verified
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Config
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Lit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Config
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP

/-! ### `Ecdsa.Rfc6979.Arm.BrainpoolP512r1`, which only this module used -/

section

/-!
# Deterministic ECDSA on 32-bit ARM: brainpoolP512r1

brainpoolP512r1 as the proof's curve (`brainpoolp512r1`): scalars of 8 64-bit words, the order
`n` of exactly 512 bits with `2^512 < 2 n`, and `vg_ecdsa_brainpoolp512r1_sign_k`, proven
correct (given the group law) and constant time against its contract
(`coreK` at brainpoolP512r1's sizes, which is `Proof.Ecdsa.Arm.BrainpoolP512r1.signArm`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm

theorem brainpoolp512r1_nBits : Spec.Ecdsa.nBits Spec.BrainpoolP512r1.curve = 512 := by
  show Spec.BrainpoolP512r1.curve.n.log2 + 1 = 512
  have h₁ : 511 ≤ Spec.BrainpoolP512r1.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.BrainpoolP512r1.curve.n.log2 < 512 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h₁, h₂]

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end

/-! Deterministic brainpoolP512r1 signing through the generator comb: the comb
signer as RFC 6979's core (`brainpoolp512r1CombCurve`), and the contract with its table. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Rfc6979.Arm
open VG VG.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.BrainpoolP512r1

theorem brainpoolp512r1_comb_core_pre {u : Bool} {s : State}
    (h : (coreK Impl.Ecdsa.Arm.brainpoolp512r1 (combSignK u)).pre s) : combSignPre u s := by
  have hk := constsOk_of_core h
  obtain ⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,-⟩ := h
  exact ⟨⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,tbl_of_consts hk
    (List.mem_append_right _ (List.mem_singleton_self _)) (by rw [wr]; simp)⟩,hk⟩

theorem brainpoolp512r1_comb_core_ctWith (u : Bool)
    (hct : ConstantTime isa (combSignPre u) (combSignPub u) (Impl.Ecdsa.Arm.signBrainpoolP512r1CombWith u)) : ConstantTime isa
    (coreK Impl.Ecdsa.Arm.brainpoolp512r1 (combSignK u)).pre
    (coreK Impl.Ecdsa.Arm.brainpoolp512r1 (combSignK u)).pub (Impl.Ecdsa.Arm.signBrainpoolP512r1CombWith u) := by
  intro s t ts tt s' t' hs ht pub e1 e2
  obtain ⟨sp,h0,h1,h2,h3,arg,sy⟩ := pub
  exact hct s t ts tt s' t' (brainpoolp512r1_comb_core_pre hs) (brainpoolp512r1_comb_core_pre ht)
    ⟨⟨sp,h0,h1,h2,h3,arg⟩,sy (brainpoolp512r1Comb.tsym, brainpoolp512r1CombWords) List.mem_cons_self,
      sy ((Impl.Ecdsa.Arm.brainpoolp512r1With u).constSym, (Impl.Ecdsa.Arm.brainpoolp512r1With u).constTbl)
        (List.mem_append_right _ (List.mem_singleton_self _))⟩ e1 e2

/-- brainpoolP512r1 with the generator comb, with the group law `hL`, calling
`vg_ecdsa_brainpoolp512r1_sign_k`, or with `u` its `_umaal` variant. -/
def brainpoolp512r1CombCurveWith (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (u : Bool) : RfcCurve where
  E := Impl.Ecdsa.Arm.brainpoolp512r1
  inst := Spec.Ecdsa.BrainpoolP512r1.inst
  curve := rfl
  big := false
  sizes := ⟨.inr (.inr (.inr (.inl rfl))), .inl rfl, brainpoolp512r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.Arm.BrainpoolP512r1.brainpoolp512r1_sh
  coreN := if u then "vg_ecdsa_brainpoolp512r1_sign_k" ++ "_umaal" else "vg_ecdsa_brainpoolp512r1_sign_k"
  coreConsts := combSignK u
  coreC := Impl.Ecdsa.Arm.signBrainpoolP512r1CombWith u
  coreX := by
    intro s hs
    obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hL (u := u) (brainpoolp512r1_comb_core_pre hs)
    refine ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,?_⟩
    simp only [coreK,coreSigOf]
    rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
    exact post
  coreCT := brainpoolp512r1_comb_core_ctWith u (by cases u; exacts [combSign_ct, combSignU_ct])
  coreStack := by cases u <;> lit_decide
  blk := by rfcT_decide

/-- brainpoolP512r1 with the generator comb, with the group law `hL`. -/
def brainpoolp512r1CombCurve (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) : RfcCurve := brainpoolp512r1CombCurveWith hL false

/-- `brainpoolp512r1CombCurve`, calling `vg_ecdsa_brainpoolp512r1_sign_umaal`. -/
def brainpoolp512r1CombCurveU (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) : RfcCurve := brainpoolp512r1CombCurveWith hL true

/-! ## With the tables of every hash function with HMAC -/

theorem brainpoolp512r1T_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target (signCodeT (brainpoolp512r1CombCurve hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 (brainpoolp512r1CombCurve hL).coreConsts HmacTable.Arm.vars) :=
  twoT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl (by decide) (by decide) (by decide)
    (by rw [Proof.BrainpoolP512r1.Arm.comb_words_length]; decide) (by rw [constTbl_length]; decide)

theorem brainpoolp512r1UT_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target (signCodeT (brainpoolp512r1CombCurveU hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 (brainpoolp512r1CombCurveU hL).coreConsts HmacTable.Arm.vars) :=
  twoT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl (by decide) (by decide) (by decide)
    (by rw [Proof.BrainpoolP512r1.Arm.comb_words_length]; decide) (by rw [constTbl_length]; decide)

end VG.Proof.Ecdsa.Rfc6979.Arm
