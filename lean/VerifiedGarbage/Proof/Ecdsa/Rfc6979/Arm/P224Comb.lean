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
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
public import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Lit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Verified
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

/-- P-224, with the group law `hL`. -/
def p224 (hL : Weierstrass.Law Spec.P224.curve) : RfcCurve where
  E := Impl.Ecdsa.Arm.p224
  inst := Spec.Ecdsa.P224.inst
  curve := rfl
  big := false
  sizes := ⟨.inr (.inl rfl), .inr ⟨rfl, rfl⟩, p224_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 28 - Spec.Ecdsa.nBits Spec.P224.curve = 0; rw [p224_nBits]
  coreN := "vg_ecdsa_p224_sign_k"
  coreC := Impl.Ecdsa.Arm.signP224
  coreConsts := []
  coreX := by
    intro s hs
    have pre : Proof.Ecdsa.Arm.P224.signArm.pre s := by
      simpa only [coreK,TablesOk,Impl.Ecdsa.Arm.p224,Impl.Ecdsa.Arm.p224With,Spec.P224.curve,Nat.reduceMul,List.not_mem_nil,forall_const,
        false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,Proof.Ecdsa.Arm.P224.signArm] using hs
    obtain ⟨tr,t,exec,abi,post⟩ := Proof.Ecdsa.Arm.P224.sign_arm hL s pre
    refine ⟨tr,t,exec,abi,?_⟩
    change Proof.Ecdsa.Arm.P224.signArm.post s t
    exact post
  coreCT := by
    simpa only [coreK,coreSigOf,Spec.P224.curve,Nat.reduceMul,Impl.Ecdsa.Arm.p224,Impl.Ecdsa.Arm.p224With,Proof.Ecdsa.Arm.P224.sig,TablesOk,List.not_mem_nil,forall_const,false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,
      Proof.Ecdsa.Arm.P224.signArm] using Proof.Ecdsa.Arm.P224.sign_ct
  coreStack := by lit_decide
  blk := by rfcT_decide

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
    (h : (coreK Impl.Ecdsa.Arm.p224 p224CombConsts).pre s) : combSignPre u s := by
  obtain ⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,tables⟩ := h
  have hp : Pre (Impl.Ecdsa.Arm.p224With u) s (constRegs p224CombConsts s) :=
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

theorem p224_comb_core_ct : ConstantTime isa
    (coreK Impl.Ecdsa.Arm.p224 p224CombConsts).pre
    (coreK Impl.Ecdsa.Arm.p224 p224CombConsts).pub Impl.Ecdsa.Arm.signP224Comb := by
  intro s t ts tt s' t' hs ht pub e1 e2
  obtain ⟨sp,h0,h1,h2,h3,arg,sy⟩ := pub
  exact combSign_ct s t ts tt s' t' (p224_comb_core_pre hs) (p224_comb_core_pre ht)
    ⟨⟨sp,h0,h1,h2,h3,arg⟩,sy _ (List.mem_singleton_self _)⟩ e1 e2

theorem p224_comb_core_ctU : ConstantTime isa
    (coreK Impl.Ecdsa.Arm.p224 p224CombConsts).pre
    (coreK Impl.Ecdsa.Arm.p224 p224CombConsts).pub Impl.Ecdsa.Arm.signP224CombU := by
  intro s t ts tt s' t' hs ht pub e1 e2
  obtain ⟨sp,h0,h1,h2,h3,arg,sy⟩ := pub
  exact combSignU_ct s t ts tt s' t' (p224_comb_core_pre hs) (p224_comb_core_pre ht)
    ⟨⟨sp,h0,h1,h2,h3,arg⟩,sy _ (List.mem_singleton_self _)⟩ e1 e2

/-- P-224 with the generator comb, with the group law `hL`. -/
def p224CombCurve (hL : Weierstrass.Law Spec.P224.curve) : RfcCurve :=
  {p224 hL with
    coreConsts := p224CombConsts
    coreC := Impl.Ecdsa.Arm.signP224Comb
    coreX := by
      intro s hs
      obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hL (p224_comb_core_pre hs)
      refine ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,?_⟩
      simp only [coreK,coreSigOf]
      rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
      exact post
    coreCT := p224_comb_core_ct
    coreStack := by lit_decide }

/-- `p224CombCurve`, calling `vg_ecdsa_p224_sign_umaal`. -/
def p224CombCurveU (hL : Weierstrass.Law Spec.P224.curve) : RfcCurve :=
  {p224CombCurve hL with
    coreN := "vg_ecdsa_p224_sign_k" ++ "_umaal"
    coreC := Impl.Ecdsa.Arm.signP224CombU
    coreX := by
      intro s hs
      obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hL (u := true) (p224_comb_core_pre hs)
      refine ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,?_⟩
      simp only [coreK,coreSigOf]
      rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
      exact post
    coreCT := p224_comb_core_ctU
    coreStack := by lit_decide }

/-! ## With the tables of every hash function with HMAC -/

theorem p224T_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified Arm.target (signCodeT (p224CombCurve hL) Spec.Ecdsa.Rfc6979.Curves.p224.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.p224 (p224CombCurve hL).coreConsts HmacTable.Arm.vars) :=
  oneT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl Proof.P224.Arm.combSatMem (by decide)
    (by rw [Proof.P224.Arm.comb_words_length]; decide) Proof.P224.Arm.combSat_held

theorem p224UT_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified Arm.target (signCodeT (p224CombCurveU hL) Spec.Ecdsa.Rfc6979.Curves.p224.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.p224 (p224CombCurveU hL).coreConsts HmacTable.Arm.vars) :=
  oneT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl Proof.P224.Arm.combSatMem (by decide)
    (by rw [Proof.P224.Arm.comb_words_length]; decide) Proof.P224.Arm.combSat_held

end VG.Proof.Ecdsa.Rfc6979.Arm
