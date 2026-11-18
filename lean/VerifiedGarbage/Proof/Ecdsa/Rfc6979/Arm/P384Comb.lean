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
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Verified
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

/-- P-384, with the group law `hL`. -/
def p384 (hL : Weierstrass.Law Spec.P384.curve) : RfcCurve where
  E := Impl.Ecdsa.Arm.p384
  inst := Spec.Ecdsa.P384.inst
  curve := rfl
  big := false
  sizes := ⟨.inr (.inr (.inl rfl)), .inl rfl, p384_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 48 - Spec.Ecdsa.nBits Spec.P384.curve = 0; rw [p384_nBits]
  coreN := "vg_ecdsa_p384_sign_k"
  coreC := Impl.Ecdsa.Arm.signP384
  coreConsts := []
  coreX := by
    intro s hs
    have pre : Proof.Ecdsa.Arm.P384.signArm.pre s := by
      simpa only [coreK,TablesOk,Impl.Ecdsa.Arm.p384,Impl.Ecdsa.Arm.p384With,Spec.P384.curve,Nat.reduceMul,List.not_mem_nil,forall_const,
        false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,Proof.Ecdsa.Arm.P384.signArm] using hs
    obtain ⟨tr,t,exec,abi,post⟩ := Proof.Ecdsa.Arm.P384.sign_arm hL s pre
    refine ⟨tr,t,exec,abi,?_⟩
    change Proof.Ecdsa.Arm.P384.signArm.post s t
    exact post
  coreCT := by
    simpa only [coreK,coreSigOf,Spec.P384.curve,Nat.reduceMul,Impl.Ecdsa.Arm.p384,Impl.Ecdsa.Arm.p384With,Proof.Ecdsa.Arm.P384.sig,TablesOk,List.not_mem_nil,forall_const,false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,
      Proof.Ecdsa.Arm.P384.signArm] using Proof.Ecdsa.Arm.P384.sign_ct
  coreStack := by lit_decide
  blk := by rfcT_decide

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
    (h : (coreK Impl.Ecdsa.Arm.p384 p384CombConsts).pre s) : combSignPre u s := by
  obtain ⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,tables⟩ := h
  have hp : Pre (Impl.Ecdsa.Arm.p384With u) s (constRegs p384CombConsts s) :=
    ⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp⟩
  refine ⟨hp,?_,?_,?_,?_⟩
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

theorem p384_comb_core_ct : ConstantTime isa
    (coreK Impl.Ecdsa.Arm.p384 p384CombConsts).pre
    (coreK Impl.Ecdsa.Arm.p384 p384CombConsts).pub Impl.Ecdsa.Arm.signP384Comb := by
  intro s t ts tt s' t' hs ht pub e1 e2
  obtain ⟨sp,h0,h1,h2,h3,arg,sy⟩ := pub
  exact combSign_ct s t ts tt s' t' (p384_comb_core_pre hs) (p384_comb_core_pre ht)
    ⟨⟨sp,h0,h1,h2,h3,arg⟩,sy _ (List.mem_singleton_self _)⟩ e1 e2

theorem p384_comb_core_ctU : ConstantTime isa
    (coreK Impl.Ecdsa.Arm.p384 p384CombConsts).pre
    (coreK Impl.Ecdsa.Arm.p384 p384CombConsts).pub Impl.Ecdsa.Arm.signP384CombU := by
  intro s t ts tt s' t' hs ht pub e1 e2
  obtain ⟨sp,h0,h1,h2,h3,arg,sy⟩ := pub
  exact combSignU_ct s t ts tt s' t' (p384_comb_core_pre hs) (p384_comb_core_pre ht)
    ⟨⟨sp,h0,h1,h2,h3,arg⟩,sy _ (List.mem_singleton_self _)⟩ e1 e2

/-- P-384 with the generator comb, with the group law `hL`. -/
def p384CombCurve (hL : Weierstrass.Law Spec.P384.curve) : RfcCurve :=
  {p384 hL with
    coreConsts := p384CombConsts
    coreC := Impl.Ecdsa.Arm.signP384Comb
    coreX := by
      intro s hs
      obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hL (p384_comb_core_pre hs)
      refine ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,?_⟩
      simp only [coreK,coreSigOf]
      rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
      exact post
    coreCT := p384_comb_core_ct
    coreStack := by lit_decide }

/-- `p384CombCurve`, calling `vg_ecdsa_p384_sign_umaal`. -/
def p384CombCurveU (hL : Weierstrass.Law Spec.P384.curve) : RfcCurve :=
  {p384CombCurve hL with
    coreN := "vg_ecdsa_p384_sign_k" ++ "_umaal"
    coreC := Impl.Ecdsa.Arm.signP384CombU
    coreX := by
      intro s hs
      obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hL (u := true) (p384_comb_core_pre hs)
      refine ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,?_⟩
      simp only [coreK,coreSigOf]
      rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
      exact post
    coreCT := p384_comb_core_ctU
    coreStack := by lit_decide }

/-! ## With the tables of every hash function with HMAC -/

theorem p384T_verified (hL : Weierstrass.Law Spec.P384.curve) :
    Verified Arm.target (signCodeT (p384CombCurve hL) Spec.Ecdsa.Rfc6979.Curves.p384.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.p384 (p384CombCurve hL).coreConsts HmacTable.Arm.vars) :=
  oneT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl Proof.P384.Arm.combSatMem (by decide)
    (by rw [Proof.P384.Arm.comb_words_length]; decide) Proof.P384.Arm.combSat_held

theorem p384UT_verified (hL : Weierstrass.Law Spec.P384.curve) :
    Verified Arm.target (signCodeT (p384CombCurveU hL) Spec.Ecdsa.Rfc6979.Curves.p384.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.p384 (p384CombCurveU hL).coreConsts HmacTable.Arm.vars) :=
  oneT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl Proof.P384.Arm.combSatMem (by decide)
    (by rw [Proof.P384.Arm.comb_words_length]; decide) Proof.P384.Arm.combSat_held

end VG.Proof.Ecdsa.Rfc6979.Arm
