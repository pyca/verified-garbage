module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P384Sha384
public import VerifiedGarbage.Proof.P384.Arm.Comb
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P384
public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Comb
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Ecdsa.Arm.P384.CombLit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Ecdsa.P384.ArmComb

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

end VG.Proof.Ecdsa.Rfc6979.Arm

namespace VG.Proof.Ecdsa.Rfc6979.Arm.P384Sha384Comb
open VG VG.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.P384.Arm

def pack (hL : Weierstrass.Law Spec.P384.curve) : RfcHash :=
  {P384Sha384.pack hL with R := p384CombCurve hL}

/-- `pack`, calling `vg_ecdsa_p384_sign_umaal`. -/
def packU (hL : Weierstrass.Law Spec.P384.curve) : RfcHash :=
  {P384Sha384.pack hL with R := p384CombCurveU hL}

abbrev rfcCombSpec : Contract isa := Spec.Ecdsa.Rfc6979.P384Sha384.inst.signContract
  (abi.withConsts p384CombConsts) 240

def rfcCombSat : State := {combSatState with
  gpr := fun r => match r with | .r0 => 0x10000 | .r1 => 0x12000 | .r2 => 0x14000 | _ => 0
  rd := [⟨0x12000,48⟩,⟨0x14000,48⟩,⟨0x100000,337920⟩]
  wr := [⟨0x10000,96⟩,⟨0,8192⟩] }

theorem rfcComb_sat : rfcCombSpec.pre rfcCombSat := by
  have held := combSat_held
  generalize eqs : rfcCombSat=s
  sig_pre [rfcCombSpec,Spec.Ecdsa.Rfc6979.P384Sha384.inst,Spec.Ecdsa.Rfc6979.Instance.signContract,
    Spec.Ecdsa.Rfc6979.Instance.signSig,Spec.Ecdsa.P384.inst,Spec.P384.curve,Spec.Ecdsa.scratchWords,
    abi,argRegs,reduceClassify,Loc.val,State.addr,p384CombConsts,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,stackBelow]
  subst s
  rw [comb_words_length]
  rw [comb_words_length] at held
  refine ⟨by decide,by decide,by decide,held,by decide,?_,?_,by decide,by decide,by decide,?_⟩
  · intro r hr
    change r∈[⟨0x10000,96⟩,⟨0,8192⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact Region.disjoint_of_sep (by decide)
  · exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

theorem implies : (rfcArm Spec.Ecdsa.Rfc6979.P384Sha384.inst 240 p384CombConsts).Implies rfcCombSpec where
  pre s h := by
    sig_pre [rfcCombSpec,Spec.Ecdsa.Rfc6979.P384Sha384.inst,Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig,Spec.Ecdsa.P384.inst,Spec.P384.curve,Spec.Ecdsa.scratchWords,
      abi,argRegs,reduceClassify,Loc.val,State.addr,p384CombConsts,Abi.withConsts,
      Abi.constRegions,Abi.constsHeld,stackBelow] at h
    obtain ⟨sp,_spf,drop,held,fit,apart,stk,al,take,wr,od,oh,os,ds,hs,so,sd,sh,ss,fo,fd,fh,fs⟩ := h
    refine ⟨?_,wr,od,oh,os,ds,hs,so,sd,sh,ss,fo,fd,fh,fs,sp,?_⟩
    · rw [← List.take_append_drop (s.rd.length-1) s.rd,take,drop]
      rfl
    · intro c hc
      simp only [p384CombConsts,List.mem_cons,List.not_mem_nil,or_false] at hc
      subst c
      refine ⟨held,fit,?_,al⟩
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      · exact apart _ (by rw [wr];exact .head _)
      · exact apart _ (by rw [wr];exact .tail _ (.head _))
      · exact stk
  post := by
    sig_implies_post [rfcCombSpec,Spec.Ecdsa.Rfc6979.P384Sha384.inst,Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig,Spec.Ecdsa.P384.inst,Spec.P384.curve,Spec.Ecdsa.scratchWords,
      abi,argRegs,reduceClassify,Loc.val,State.addr,Abi.withConsts,rfcArm,stkR]
  pub s t _ _ h := by
    sig_pub [rfcCombSpec,Spec.Ecdsa.Rfc6979.P384Sha384.inst,Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig,Spec.Ecdsa.P384.inst,Spec.P384.curve,Spec.Ecdsa.scratchWords,
      abi,argRegs,reduceClassify,Loc.val,State.addr,p384CombConsts,Abi.withConsts] at h
    obtain ⟨sp,sy,leak,h0,h1,h2,h3⟩ := h
    refine ⟨sp,h0,h1,h2,h3,(List.cons.inj leak).1,?_⟩
    intro c hc
    simp only [p384CombConsts,List.mem_cons,List.not_mem_nil,or_false] at hc
    subst c
    exact sy
  sat := ⟨rfcCombSat,rfcComb_sat⟩

theorem sign_verified (hL : Weierstrass.Law Spec.P384.curve) :
    Verified Arm.target (cfgOf (pack hL)).sign rfcCombSpec :=
  Arm.sign_verified (pack hL) implies

theorem signU_verified (hL : Weierstrass.Law Spec.P384.curve) :
    Verified Arm.target (cfgOf (packU hL)).sign rfcCombSpec :=
  Arm.sign_verified (packU hL) implies

end VG.Proof.Ecdsa.Rfc6979.Arm.P384Sha384Comb
