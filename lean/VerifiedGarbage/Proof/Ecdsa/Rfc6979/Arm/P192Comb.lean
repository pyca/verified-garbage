module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.P192.Arm.Comb
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P192
public import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Comb
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Ecdsa.Arm.P192.CombLit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Ecdsa.P192.ArmComb
meta import VerifiedGarbage.Proof.P192.Arm.Comb
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P192
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P192.Comb
meta import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P192.CombLit
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.P192.ArmComb

/-! Deterministic P-192 signing through the generator comb: the comb
signer as RFC 6979's core (`p192CombCurve`), and the contract with its table. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Rfc6979.Arm
open VG VG.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P192

theorem p192_comb_core_pre {u : Bool} {s : State}
    (h : (coreK Impl.Ecdsa.Arm.p192 p192CombConsts).pre s) : combSignPre u s := by
  obtain ⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,tables⟩ := h
  have hp : Pre (Impl.Ecdsa.Arm.p192With u) s (constRegs p192CombConsts s) :=
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

theorem p192_comb_core_ct : ConstantTime isa
    (coreK Impl.Ecdsa.Arm.p192 p192CombConsts).pre
    (coreK Impl.Ecdsa.Arm.p192 p192CombConsts).pub Impl.Ecdsa.Arm.signP192Comb := by
  intro s t ts tt s' t' hs ht pub e1 e2
  obtain ⟨sp,h0,h1,h2,h3,arg,sy⟩ := pub
  exact combSign_ct s t ts tt s' t' (p192_comb_core_pre hs) (p192_comb_core_pre ht)
    ⟨⟨sp,h0,h1,h2,h3,arg⟩,sy _ (List.mem_singleton_self _)⟩ e1 e2

theorem p192_comb_core_ctU : ConstantTime isa
    (coreK Impl.Ecdsa.Arm.p192 p192CombConsts).pre
    (coreK Impl.Ecdsa.Arm.p192 p192CombConsts).pub Impl.Ecdsa.Arm.signP192CombU := by
  intro s t ts tt s' t' hs ht pub e1 e2
  obtain ⟨sp,h0,h1,h2,h3,arg,sy⟩ := pub
  exact combSignU_ct s t ts tt s' t' (p192_comb_core_pre hs) (p192_comb_core_pre ht)
    ⟨⟨sp,h0,h1,h2,h3,arg⟩,sy _ (List.mem_singleton_self _)⟩ e1 e2

/-- P-192 with the generator comb, with the group law `hL`. -/
def p192CombCurve (hL : Weierstrass.Law Spec.P192.curve) : RfcCurve :=
  {p192 hL with
    coreConsts := p192CombConsts
    coreC := Impl.Ecdsa.Arm.signP192Comb
    coreX := by
      intro s hs
      obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hL (p192_comb_core_pre hs)
      refine ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,?_⟩
      simp only [coreK,coreSigOf]
      rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
      exact post
    coreCT := p192_comb_core_ct
    coreStack := by lit_decide }

/-- `p192CombCurve`, calling `vg_ecdsa_p192_sign_umaal`. -/
def p192CombCurveU (hL : Weierstrass.Law Spec.P192.curve) : RfcCurve :=
  {p192CombCurve hL with
    coreN := "vg_ecdsa_p192_sign_k" ++ "_umaal"
    coreC := Impl.Ecdsa.Arm.signP192CombU
    coreX := by
      intro s hs
      obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hL (u := true) (p192_comb_core_pre hs)
      refine ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,?_⟩
      simp only [coreK,coreSigOf]
      rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
      exact post
    coreCT := p192_comb_core_ctU
    coreStack := by lit_decide }

/-! ## With the tables of every hash function with HMAC -/

theorem p192T_verified (hL : Weierstrass.Law Spec.P192.curve) :
    Verified Arm.target (signCodeT (p192CombCurve hL) Spec.Ecdsa.Rfc6979.Curves.p192.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.p192 (p192CombCurve hL).coreConsts HmacTable.Arm.vars) :=
  oneT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl Proof.P192.Arm.combSatMem (by decide)
    (by rw [Proof.P192.Arm.comb_words_length]; decide) Proof.P192.Arm.combSat_held

theorem p192UT_verified (hL : Weierstrass.Law Spec.P192.curve) :
    Verified Arm.target (signCodeT (p192CombCurveU hL) Spec.Ecdsa.Rfc6979.Curves.p192.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.p192 (p192CombCurveU hL).coreConsts HmacTable.Arm.vars) :=
  oneT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl Proof.P192.Arm.combSatMem (by decide)
    (by rw [Proof.P192.Arm.comb_words_length]; decide) Proof.P192.Arm.combSat_held

end VG.Proof.Ecdsa.Rfc6979.Arm
