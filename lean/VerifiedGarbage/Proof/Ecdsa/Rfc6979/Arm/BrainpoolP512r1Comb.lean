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

/-- brainpoolP512r1, with the group law `hL`. -/
def brainpoolp512r1 (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) : RfcCurve where
  E := Impl.Ecdsa.Arm.brainpoolp512r1
  inst := Spec.Ecdsa.BrainpoolP512r1.inst
  curve := rfl
  big := false
  sizes := ⟨.inr (.inr (.inr rfl)), .inl rfl, brainpoolp512r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.Arm.BrainpoolP512r1.brainpoolp512r1_sh
  coreN := "vg_ecdsa_brainpoolp512r1_sign_k"
  coreC := Impl.Ecdsa.Arm.signBrainpoolP512r1
  coreConsts := []
  coreX := by
    intro s hs
    have pre : Proof.Ecdsa.Arm.BrainpoolP512r1.signArm.pre s := by
      simpa only [coreK,TablesOk,Impl.Ecdsa.Arm.brainpoolp512r1,Impl.Ecdsa.Arm.brainpoolp512r1With,Spec.BrainpoolP512r1.curve,Nat.reduceMul,List.not_mem_nil,forall_const,
        false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,Proof.Ecdsa.Arm.BrainpoolP512r1.signArm] using hs
    obtain ⟨tr,t,exec,abi,post⟩ := Proof.Ecdsa.Arm.BrainpoolP512r1.sign_arm hL s pre
    refine ⟨tr,t,exec,abi,?_⟩
    change Proof.Ecdsa.Arm.BrainpoolP512r1.signArm.post s t
    exact post
  coreCT := by
    simpa only [coreK,coreSigOf,Spec.BrainpoolP512r1.curve,Nat.reduceMul,Impl.Ecdsa.Arm.brainpoolp512r1,Impl.Ecdsa.Arm.brainpoolp512r1With,Proof.Ecdsa.Arm.BrainpoolP512r1.sig,TablesOk,List.not_mem_nil,forall_const,false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,
      Proof.Ecdsa.Arm.BrainpoolP512r1.signArm] using Proof.Ecdsa.Arm.BrainpoolP512r1.sign_ct
  coreStack := by lit_decide
  blk := by rfcT_decide

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
    (h : (coreK Impl.Ecdsa.Arm.brainpoolp512r1 brainpoolp512r1CombConsts).pre s) : combSignPre u s := by
  obtain ⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,tables⟩ := h
  have hp : Pre (Impl.Ecdsa.Arm.brainpoolp512r1With u) s (constRegs brainpoolp512r1CombConsts s) :=
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

theorem brainpoolp512r1_comb_core_ct : ConstantTime isa
    (coreK Impl.Ecdsa.Arm.brainpoolp512r1 brainpoolp512r1CombConsts).pre
    (coreK Impl.Ecdsa.Arm.brainpoolp512r1 brainpoolp512r1CombConsts).pub Impl.Ecdsa.Arm.signBrainpoolP512r1Comb := by
  intro s t ts tt s' t' hs ht pub e1 e2
  obtain ⟨sp,h0,h1,h2,h3,arg,sy⟩ := pub
  exact combSign_ct s t ts tt s' t' (brainpoolp512r1_comb_core_pre hs) (brainpoolp512r1_comb_core_pre ht)
    ⟨⟨sp,h0,h1,h2,h3,arg⟩,sy _ (List.mem_singleton_self _)⟩ e1 e2

theorem brainpoolp512r1_comb_core_ctU : ConstantTime isa
    (coreK Impl.Ecdsa.Arm.brainpoolp512r1 brainpoolp512r1CombConsts).pre
    (coreK Impl.Ecdsa.Arm.brainpoolp512r1 brainpoolp512r1CombConsts).pub Impl.Ecdsa.Arm.signBrainpoolP512r1CombU := by
  intro s t ts tt s' t' hs ht pub e1 e2
  obtain ⟨sp,h0,h1,h2,h3,arg,sy⟩ := pub
  exact combSignU_ct s t ts tt s' t' (brainpoolp512r1_comb_core_pre hs) (brainpoolp512r1_comb_core_pre ht)
    ⟨⟨sp,h0,h1,h2,h3,arg⟩,sy _ (List.mem_singleton_self _)⟩ e1 e2

/-- brainpoolP512r1 with the generator comb, with the group law `hL`. -/
def brainpoolp512r1CombCurve (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) : RfcCurve :=
  {brainpoolp512r1 hL with
    coreConsts := brainpoolp512r1CombConsts
    coreC := Impl.Ecdsa.Arm.signBrainpoolP512r1Comb
    coreX := by
      intro s hs
      obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hL (brainpoolp512r1_comb_core_pre hs)
      refine ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,?_⟩
      simp only [coreK,coreSigOf]
      rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
      exact post
    coreCT := brainpoolp512r1_comb_core_ct
    coreStack := by lit_decide }

/-- `brainpoolp512r1CombCurve`, calling `vg_ecdsa_brainpoolp512r1_sign_umaal`. -/
def brainpoolp512r1CombCurveU (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) : RfcCurve :=
  {brainpoolp512r1CombCurve hL with
    coreN := "vg_ecdsa_brainpoolp512r1_sign_k" ++ "_umaal"
    coreC := Impl.Ecdsa.Arm.signBrainpoolP512r1CombU
    coreX := by
      intro s hs
      obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hL (u := true) (brainpoolp512r1_comb_core_pre hs)
      refine ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,?_⟩
      simp only [coreK,coreSigOf]
      rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
      exact post
    coreCT := brainpoolp512r1_comb_core_ctU
    coreStack := by lit_decide }

/-! ## With the tables of every hash function with HMAC -/

theorem brainpoolp512r1T_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target (signCodeT (brainpoolp512r1CombCurve hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 (brainpoolp512r1CombCurve hL).coreConsts HmacTable.Arm.vars) :=
  oneT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl Proof.BrainpoolP512r1.Arm.combSatMem (by decide)
    (by rw [Proof.BrainpoolP512r1.Arm.comb_words_length]; decide) Proof.BrainpoolP512r1.Arm.combSat_held

theorem brainpoolp512r1UT_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    Verified Arm.target (signCodeT (brainpoolp512r1CombCurveU hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp512r1 (brainpoolp512r1CombCurveU hL).coreConsts HmacTable.Arm.vars) :=
  oneT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl Proof.BrainpoolP512r1.Arm.combSatMem (by decide)
    (by rw [Proof.BrainpoolP512r1.Arm.comb_words_length]; decide) Proof.BrainpoolP512r1.Arm.combSat_held

end VG.Proof.Ecdsa.Rfc6979.Arm
