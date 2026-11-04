module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.P384.Arm.Comb
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P384
public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Comb
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Ecdsa.Arm.P384.CombLit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Ecdsa.P384.ArmComb

/-! RFC 6979 on P-384 calls the same comb signer as the raw signing API (`p384CombCurve`). -/

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
    coreN := "vg_ecdsa_p384_sign" ++ "_umaal"
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

/-- P-384 with the comb, multiplying with UMAAL (`u`) or not. -/
def p384Of (u : Bool) (hL : Weierstrass.Law Spec.P384.curve) : RfcCurve :=
  bif u then p384CombCurveU hL else p384CombCurve hL

/-- `vg_ecdsa_p384_sign` (`_umaal`, multiplying with UMAAL), with the tables of `vs`. -/
theorem p384T_verified (u : Bool) (hL : Weierstrass.Law Spec.P384.curve) (vs : List Proof.HashTable.Arm.TVar)
    (h : OK vs ∧ ∀ c ∈ p384CombConsts, c.1 ∉ Proof.HashTable.Arm.names vs) :
    Verified Arm.target (signCode (p384Of u hL) Spec.Ecdsa.Rfc6979.Curves.p384.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p384 p384CombConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.p384) h.1 VG.Proof.P384.Arm.combSatMem
    (h.2 _ (List.mem_singleton_self _)) (by rw [VG.Proof.P384.Arm.comb_words_length]; decide)
    VG.Proof.P384.Arm.combSat_held (by decide) rfl
  cases u
  · exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h.1 hsat
  · exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h.1 hsat

end VG.Proof.Ecdsa.Rfc6979.Arm
