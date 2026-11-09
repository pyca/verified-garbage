module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.BrainpoolP256r1.Arm.Comb
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP256r1
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Comb
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.CombLit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.ArmComb
meta import VerifiedGarbage.Proof.BrainpoolP256r1.Arm.Comb
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP256r1
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Comb
meta import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.CombLit
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.ArmComb

/-! Deterministic brainpoolP256r1/SHA-256 signing through the generator comb: the comb
signer as RFC 6979's core (`brainpoolp256r1CombCurve`), and the contract with its table. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Rfc6979.Arm
open VG VG.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.BrainpoolP256r1

theorem brainpoolp256r1_comb_core_pre {u : Bool} {s : State}
    (h : (coreK Impl.Ecdsa.Arm.brainpoolp256r1 brainpoolp256r1CombConsts).pre s) : combSignPre u s := by
  obtain ⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp,tables⟩ := h
  have hp : Pre (Impl.Ecdsa.Arm.brainpoolp256r1With u) s (constRegs brainpoolp256r1CombConsts s) :=
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

theorem brainpoolp256r1_comb_core_ct : ConstantTime isa
    (coreK Impl.Ecdsa.Arm.brainpoolp256r1 brainpoolp256r1CombConsts).pre
    (coreK Impl.Ecdsa.Arm.brainpoolp256r1 brainpoolp256r1CombConsts).pub Impl.Ecdsa.Arm.signBrainpoolP256r1Comb := by
  intro s t ts tt s' t' hs ht pub e1 e2
  obtain ⟨sp,h0,h1,h2,h3,arg,sy⟩ := pub
  exact combSign_ct s t ts tt s' t' (brainpoolp256r1_comb_core_pre hs) (brainpoolp256r1_comb_core_pre ht)
    ⟨⟨sp,h0,h1,h2,h3,arg⟩,sy _ (List.mem_singleton_self _)⟩ e1 e2

theorem brainpoolp256r1_comb_core_ctU : ConstantTime isa
    (coreK Impl.Ecdsa.Arm.brainpoolp256r1 brainpoolp256r1CombConsts).pre
    (coreK Impl.Ecdsa.Arm.brainpoolp256r1 brainpoolp256r1CombConsts).pub Impl.Ecdsa.Arm.signBrainpoolP256r1CombU := by
  intro s t ts tt s' t' hs ht pub e1 e2
  obtain ⟨sp,h0,h1,h2,h3,arg,sy⟩ := pub
  exact combSignU_ct s t ts tt s' t' (brainpoolp256r1_comb_core_pre hs) (brainpoolp256r1_comb_core_pre ht)
    ⟨⟨sp,h0,h1,h2,h3,arg⟩,sy _ (List.mem_singleton_self _)⟩ e1 e2

/-- brainpoolP256r1 with the generator comb, with the group law `hL`. -/
def brainpoolp256r1CombCurve (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) : RfcCurve :=
  {brainpoolp256r1 hL with
    coreConsts := brainpoolp256r1CombConsts
    coreC := Impl.Ecdsa.Arm.signBrainpoolP256r1Comb
    coreX := by
      intro s hs
      obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hL (brainpoolp256r1_comb_core_pre hs)
      refine ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,?_⟩
      simp only [coreK,coreSigOf]
      rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
      exact post
    coreCT := brainpoolp256r1_comb_core_ct
    coreStack := by lit_decide }

/-- `brainpoolp256r1CombCurve`, calling `vg_ecdsa_brainpoolp256r1_sign_umaal`. -/
def brainpoolp256r1CombCurveU (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) : RfcCurve :=
  {brainpoolp256r1CombCurve hL with
    coreN := "vg_ecdsa_brainpoolp256r1_sign_k" ++ "_umaal"
    coreC := Impl.Ecdsa.Arm.signBrainpoolP256r1CombU
    coreX := by
      intro s hs
      obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hL (u := true) (brainpoolp256r1_comb_core_pre hs)
      refine ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,?_⟩
      simp only [coreK,coreSigOf]
      rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
      exact post
    coreCT := brainpoolp256r1_comb_core_ctU
    coreStack := by lit_decide }

/-! ## With the tables of every hash function with HMAC -/

theorem brainpoolp256r1T_verified (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) :
    Verified Arm.target (signCodeT (brainpoolp256r1CombCurve hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1 (brainpoolp256r1CombCurve hL).coreConsts HmacTable.Arm.vars) :=
  oneT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl Proof.BrainpoolP256r1.Arm.combSatMem (by decide)
    (by rw [Proof.BrainpoolP256r1.Arm.comb_words_length]; decide) Proof.BrainpoolP256r1.Arm.combSat_held

theorem brainpoolp256r1UT_verified (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) :
    Verified Arm.target (signCodeT (brainpoolp256r1CombCurveU hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries HmacTable.Arm.vars)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1 (brainpoolp256r1CombCurveU hL).coreConsts HmacTable.Arm.vars) :=
  oneT_verified ⟨rfl, by decide, by decide⟩ rfl (by decide) rfl Proof.BrainpoolP256r1.Arm.combSatMem (by decide)
    (by rw [Proof.BrainpoolP256r1.Arm.comb_words_length]; decide) Proof.BrainpoolP256r1.Arm.combSat_held

end VG.Proof.Ecdsa.Rfc6979.Arm
