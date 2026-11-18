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
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Ecdsa.P256.ArmComb
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P256.CombGenerator
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Comb
meta import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P256.CombLit
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.P256.ArmComb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
public import VerifiedGarbage.Proof.Ecdsa.Arm.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Verified
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

/-- P-256, with the group law `hL`. -/
def p256 (hL : Weierstrass.Law Spec.P256.curve) : RfcCurve where
  E := Impl.Ecdsa.Arm.p256
  inst := Spec.Ecdsa.P256.inst
  curve := rfl
  big := false
  sizes := ⟨.inr (.inl rfl), .inl rfl, p256_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := by show 8 * 32 - Spec.Ecdsa.nBits Spec.P256.curve = 0; rw [p256_nBits]
  coreN := "vg_ecdsa_p256_sign_k"
  coreC := Impl.Ecdsa.Arm.signP256
  coreConsts := []
  coreX := by
    intro s hs
    have pre : Proof.Ecdsa.Arm.signArm.pre s := by
      simpa only [coreK,TablesOk,Impl.Ecdsa.Arm.p256, Impl.Ecdsa.Arm.p256With,Spec.P256.curve,Nat.reduceMul,List.not_mem_nil,forall_const,false_implies,implies_true,and_true,
        Abi.constRegions,List.map_nil,List.append_nil,Proof.Ecdsa.Arm.signArm] using hs
    obtain ⟨tr,t,exec,abi,post⟩ := Proof.Ecdsa.Arm.sign_arm hL s pre
    refine ⟨tr,t,exec,abi,?_⟩
    change Proof.Ecdsa.Arm.signArm.post s t
    exact post
  coreCT := by
    simpa only [coreK,coreSigOf,Spec.P256.curve,Nat.reduceMul,Impl.Ecdsa.Arm.p256, Impl.Ecdsa.Arm.p256With,Proof.Ecdsa.Arm.sig,TablesOk,List.not_mem_nil,forall_const,false_implies,implies_true,and_true,Abi.constRegions,List.map_nil,List.append_nil,
      Proof.Ecdsa.Arm.signArm] using Proof.Ecdsa.Arm.sign_ct
  coreStack := by lit_decide
  blk := by rfcT_decide

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end

/-! RFC 6979 calls the same comb signer as the raw signing API. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Rfc6979.Arm
open VG VG.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P256

theorem p256_comb_core_pre {u : Bool} {s : State}
    (h : (coreK Impl.Ecdsa.Arm.p256 p256CombConsts).pre s) : combSignPre u s := by
  obtain ⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,tables⟩ := h
  have hp : Pre (Impl.Ecdsa.Arm.p256With u) s (constRegs p256CombConsts s) :=
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

theorem p256_comb_core_ct : ConstantTime isa
    (coreK Impl.Ecdsa.Arm.p256 p256CombConsts).pre
    (coreK Impl.Ecdsa.Arm.p256 p256CombConsts).pub Impl.Ecdsa.Arm.signP256Comb := by
  intro s t ts tt s' t' hs ht pub e1 e2
  obtain ⟨sp,h0,h1,h2,h3,arg,sy⟩ := pub
  exact combSign_ct s t ts tt s' t' (p256_comb_core_pre hs) (p256_comb_core_pre ht)
    ⟨⟨sp,h0,h1,h2,h3,arg⟩,sy _ (List.mem_singleton_self _)⟩ e1 e2

theorem p256_comb_core_ctU : ConstantTime isa
    (coreK Impl.Ecdsa.Arm.p256 p256CombConsts).pre
    (coreK Impl.Ecdsa.Arm.p256 p256CombConsts).pub Impl.Ecdsa.Arm.signP256CombU := by
  intro s t ts tt s' t' hs ht pub e1 e2
  obtain ⟨sp,h0,h1,h2,h3,arg,sy⟩ := pub
  exact combSignU_ct s t ts tt s' t' (p256_comb_core_pre hs) (p256_comb_core_pre ht)
    ⟨⟨sp,h0,h1,h2,h3,arg⟩,sy _ (List.mem_singleton_self _)⟩ e1 e2

/-- P-256 with the generator comb, with the group law `hL`. -/
def p256CombCurve (hL : Weierstrass.Law Spec.P256.curve) : RfcCurve :=
  {p256 hL with
    coreConsts := p256CombConsts
    coreC := Impl.Ecdsa.Arm.signP256Comb
    coreX := by
      intro s hs
      obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hL (p256_comb_core_pre hs)
      refine ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,?_⟩
      simp only [coreK,coreSigOf]
      rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
      exact post
    coreCT := p256_comb_core_ct
    coreStack := by lit_decide }

/-- `p256CombCurve`, calling `vg_ecdsa_p256_sign_umaal`. -/
def p256CombCurveU (hL : Weierstrass.Law Spec.P256.curve) : RfcCurve :=
  {p256CombCurve hL with
    coreN := "vg_ecdsa_p256_sign_k" ++ "_umaal"
    coreC := Impl.Ecdsa.Arm.signP256CombU
    coreX := by
      intro s hs
      obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hL (u := true) (p256_comb_core_pre hs)
      refine ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,?_⟩
      simp only [coreK,coreSigOf]
      rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
      exact post
    coreCT := p256_comb_core_ctU
    coreStack := by lit_decide }

/-! ## With the tables of every hash function with HMAC -/

theorem p256T_verified (hL : Weierstrass.Law Spec.P256.curve) :
    Verified Arm.target (signCodeT (p256CombCurve hL) Spec.Ecdsa.Rfc6979.Curves.p256.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.p256 (p256CombCurve hL).coreConsts HmacTable.Arm.vars) :=
  oneT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl Proof.P256.Arm.combSatMem (by decide)
    (by rw [Proof.P256.Arm.comb_words_length]; decide) Proof.P256.Arm.combSat_held

theorem p256UT_verified (hL : Weierstrass.Law Spec.P256.curve) :
    Verified Arm.target (signCodeT (p256CombCurveU hL) Spec.Ecdsa.Rfc6979.Curves.p256.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.p256 (p256CombCurveU hL).coreConsts HmacTable.Arm.vars) :=
  oneT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl Proof.P256.Arm.combSatMem (by decide)
    (by rw [Proof.P256.Arm.comb_words_length]; decide) Proof.P256.Arm.combSat_held

end VG.Proof.Ecdsa.Rfc6979.Arm
