module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.Arm.P192.CombGenerator
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Comb
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Ecdsa.Arm.P192.CombLit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Ecdsa.P192.ArmComb
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P192.CombGenerator
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Comb
meta import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P192.CombLit
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.P192.ArmComb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
public import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Lit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP

/-! ### `Ecdsa.Rfc6979.Arm.P192`, which only this module used -/

section

/-!
# Deterministic ECDSA on 32-bit ARM: P-192

P-192 as the proof's curve (`p192`): scalars of 3 64-bit words, the order
`n` of exactly 192 bits with `2^192 < 2 n`, and `vg_ecdsa_p192_sign`, proven
correct (given the group law) and constant time against its contract
(`coreK` at P-192's sizes, which is `Proof.Ecdsa.Arm.P192.signArm`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm

theorem p192_nBits : Spec.Ecdsa.nBits Spec.P192.curve = 192 := by
  show Spec.P192.curve.n.log2 + 1 = 192
  have h₁ : 191 ≤ Spec.P192.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P192.curve.n.log2 < 192 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h₁, h₂]

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end

/-! Deterministic P-192 signing through the generator comb: the comb
signer as RFC 6979's core (`p192CombCurve`), and the contract with its table. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Rfc6979.Arm
open VG VG.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P192

theorem p192_comb_core_pre {u : Bool} {s : State}
    (h : (coreK Impl.Ecdsa.Arm.p192 (combSignK u)).pre s) : combSignPre u s := by
  obtain ⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,tables⟩ := h
  have hk : ConstsOk (combSignK u) 0 s := by
    refine ⟨?_,?_,?_,?_⟩
    · rw [rd]
      rfl
    · exact fun c hc i hi => (tables c hc).1 i hi
    · intro r hr
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hr
      refine ⟨?_,?_,?_⟩
      · change (State.addr (s.syms c.1)).toNat+8*c.2.length≤2^32
        rw [VG.Proof.X25519.Arm.addr_toNat]
        exact (tables c hc).2.1
      · intro w hw
        rw [wr] at hw
        exact (tables c hc).2.2.1 w hw
      · intro w hw
        change w∈[] at hw
        cases hw
    · intro r hr
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hr
      exact (tables c hc).2.2.2
  exact ⟨⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,fun _ => tbl_of_consts hk
    (List.mem_append_right _ (List.mem_singleton_self _)) (by rw [wr]; simp)⟩,hk⟩

theorem p192_comb_core_ctWith (u : Bool)
    (hct : ConstantTime isa (combSignPre u) (combSignPub u) (Impl.Ecdsa.Arm.signP192CombWith u)) : ConstantTime isa
    (coreK Impl.Ecdsa.Arm.p192 (combSignK u)).pre
    (coreK Impl.Ecdsa.Arm.p192 (combSignK u)).pub (Impl.Ecdsa.Arm.signP192CombWith u) := by
  intro s t ts tt s' t' hs ht pub e1 e2
  obtain ⟨sp,h0,h1,h2,h3,arg,sy⟩ := pub
  exact hct s t ts tt s' t' (p192_comb_core_pre hs) (p192_comb_core_pre ht)
    ⟨⟨sp,h0,h1,h2,h3,arg⟩,sy (p192Comb.tsym, p192CombWords) List.mem_cons_self,
      sy ((Impl.Ecdsa.Arm.p192With u).constSym, (Impl.Ecdsa.Arm.p192With u).constTbl) (List.mem_append_right _ (List.mem_singleton_self _))⟩ e1 e2

/-- P-192 with the generator comb, with the group law `hL`, calling
`vg_ecdsa_p192_sign`, or with `u` its `_umaal` variant. -/
def p192CombCurveWith (hL : Weierstrass.Law Spec.P192.curve) (u : Bool) : RfcCurve where
  E := Impl.Ecdsa.Arm.p192
  inst := Spec.Ecdsa.P192.inst
  curve := rfl
  big := false
  sizes := ⟨.inl rfl, .inl rfl, p192_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 24 - Spec.Ecdsa.nBits Spec.P192.curve = 0; rw [p192_nBits]
  coreN := if u then "vg_ecdsa_p192_sign_k" ++ "_umaal" else "vg_ecdsa_p192_sign_k"
  coreConsts := combSignK u
  coreC := Impl.Ecdsa.Arm.signP192CombWith u
  coreX := by
    intro s hs
    obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hL (u := u) (p192_comb_core_pre hs)
    refine ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,?_⟩
    simp only [coreK,coreSigOf]
    rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
    exact post
  coreCT := p192_comb_core_ctWith u (by cases u; exacts [combSign_ct, combSignU_ct])
  coreStack := by cases u <;> lit_decide
  blk := by rfcT_decide

/-- P-192 with the generator comb, with the group law `hL`. -/
def p192CombCurve (hL : Weierstrass.Law Spec.P192.curve) : RfcCurve := p192CombCurveWith hL false

/-- `p192CombCurve`, calling `vg_ecdsa_p192_sign_umaal`. -/
def p192CombCurveU (hL : Weierstrass.Law Spec.P192.curve) : RfcCurve := p192CombCurveWith hL true

/-! ## With the tables of every hash function with HMAC -/

theorem p192T_verified (hL : Weierstrass.Law Spec.P192.curve) :
    Verified Arm.target (signCodeT (p192CombCurve hL) Spec.Ecdsa.Rfc6979.Curves.p192.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.p192 (p192CombCurve hL).coreConsts HmacTable.Arm.vars) :=
  twoT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl (by decide) (by decide) (by decide)
    (by rw [Proof.P192.Arm.comb_words_length]; decide) (by rw [constTbl_length]; decide)

theorem p192UT_verified (hL : Weierstrass.Law Spec.P192.curve) :
    Verified Arm.target (signCodeT (p192CombCurveU hL) Spec.Ecdsa.Rfc6979.Curves.p192.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.p192 (p192CombCurveU hL).coreConsts HmacTable.Arm.vars) :=
  twoT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl (by decide) (by decide) (by decide)
    (by rw [Proof.P192.Arm.comb_words_length]; decide) (by rw [constTbl_length]; decide)

end VG.Proof.Ecdsa.Rfc6979.Arm
