module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.BrainpoolP256r1.Arm.Comb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.BrainpoolP256r1
public import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Comb
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.CombLit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.ArmComb

/-! RFC 6979 on brainpoolP256r1 calls the same comb signer as the raw signing API (`brainpoolP256r1CombCurve`). -/

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

/-- `brainpoolp256r1CombCurve`, calling `vg_ecdsa_brainpoolp256r1_sign_k_umaal`. -/
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

/-- brainpoolP256r1 with the comb, multiplying with UMAAL (`u`) or not. -/
def brainpoolp256r1Of (u : Bool) (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) : RfcCurve :=
  bif u then brainpoolp256r1CombCurveU hL else brainpoolp256r1CombCurve hL

/-- `vg_ecdsa_brainpoolp256r1_sign` (`_umaal`, multiplying with UMAAL), with the tables of `vs`. -/
theorem brainpoolp256r1T_verified (u : Bool) (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (vs : List Proof.HashTable.Arm.TVar)
    (h : OK vs ∧ ∀ c ∈ brainpoolp256r1CombConsts, c.1 ∉ Proof.HashTable.Arm.names vs) :
    Verified Arm.target (signCode (brainpoolp256r1Of u hL) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1 brainpoolp256r1CombConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1) h.1 VG.Proof.BrainpoolP256r1.Arm.combSatMem
    (h.2 _ (List.mem_singleton_self _)) (by rw [VG.Proof.BrainpoolP256r1.Arm.comb_words_length]; decide)
    VG.Proof.BrainpoolP256r1.Arm.combSat_held (by decide) rfl
  cases u
  · exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h.1 hsat
  · exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h.1 hsat

end VG.Proof.Ecdsa.Rfc6979.Arm
