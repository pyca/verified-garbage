module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P256
public import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Comb
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Ecdsa.Arm.P256.CombLit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Ecdsa.P256.ArmComb

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
    coreN := "vg_ecdsa_p256_sign" ++ "_umaal"
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

end VG.Proof.Ecdsa.Rfc6979.Arm
