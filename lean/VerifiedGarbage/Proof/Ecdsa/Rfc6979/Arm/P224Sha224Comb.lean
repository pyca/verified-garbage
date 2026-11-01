module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P224Sha224
public import VerifiedGarbage.Proof.P224.Arm.Comb
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Verified
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.P224
public import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Comb
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.CombLit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Impl.Ecdsa.P224.ArmComb

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
    coreN := "vg_ecdsa_p224_sign" ++ "_umaal"
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

end VG.Proof.Ecdsa.Rfc6979.Arm

namespace VG.Proof.Ecdsa.Rfc6979.Arm.P224Sha224Comb
open VG VG.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.P224.Arm

def pack (hL : Weierstrass.Law Spec.P224.curve) : RfcHash :=
  {P224Sha224.pack hL with R := p224CombCurve hL}

/-- `pack`, calling `vg_ecdsa_p224_sign_umaal`. -/
def packU (hL : Weierstrass.Law Spec.P224.curve) : RfcHash :=
  {P224Sha224.pack hL with R := p224CombCurveU hL}

abbrev rfcCombSpec : Contract isa := Spec.Ecdsa.Rfc6979.P224Sha224.inst.signContract
  (abi.withConsts p224CombConsts) 240

def rfcCombSat : State := {combSatState with
  gpr := fun r => match r with | .r0 => 0x10000 | .r1 => 0x12000 | .r2 => 0x14000 | _ => 0
  rd := [⟨0x12000,28⟩,⟨0x14000,28⟩,⟨0x100000,131072⟩]
  wr := [⟨0x10000,56⟩,⟨0,8192⟩] }

theorem rfcComb_sat : rfcCombSpec.pre rfcCombSat := by
  have held := combSat_held
  generalize eqs : rfcCombSat=s
  sig_pre [rfcCombSpec,Spec.Ecdsa.Rfc6979.P224Sha224.inst,Spec.Ecdsa.Rfc6979.Instance.signContract,
    Spec.Ecdsa.Rfc6979.Instance.signSig,Spec.Ecdsa.P224.inst,Spec.P224.curve,Spec.Ecdsa.scratchWords,
    abi,argRegs,reduceClassify,Loc.val,State.addr,p224CombConsts,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,stackBelow]
  subst s
  rw [comb_words_length]
  rw [comb_words_length] at held
  refine ⟨by decide,by decide,by decide,held,by decide,?_,?_,by decide,by decide,by decide,?_⟩
  · intro r hr
    change r∈[⟨0x10000,56⟩,⟨0,8192⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact Region.disjoint_of_sep (by decide)
  · exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

theorem implies : (rfcArm Spec.Ecdsa.Rfc6979.P224Sha224.inst 240 p224CombConsts).Implies rfcCombSpec where
  pre s h := by
    sig_pre [rfcCombSpec,Spec.Ecdsa.Rfc6979.P224Sha224.inst,Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig,Spec.Ecdsa.P224.inst,Spec.P224.curve,Spec.Ecdsa.scratchWords,
      abi,argRegs,reduceClassify,Loc.val,State.addr,p224CombConsts,Abi.withConsts,
      Abi.constRegions,Abi.constsHeld,stackBelow] at h
    obtain ⟨sp,_spf,drop,held,fit,apart,stk,al,take,wr,od,oh,os,ds,hs,so,sd,sh,ss,fo,fd,fh,fs⟩ := h
    refine ⟨?_,wr,od,oh,os,ds,hs,so,sd,sh,ss,fo,fd,fh,fs,sp,?_⟩
    · rw [← List.take_append_drop (s.rd.length-1) s.rd,take,drop]
      rfl
    · intro c hc
      simp only [p224CombConsts,List.mem_cons,List.not_mem_nil,or_false] at hc
      subst c
      refine ⟨held,fit,?_,al⟩
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl
      · exact apart _ (by rw [wr];exact .head _)
      · exact apart _ (by rw [wr];exact .tail _ (.head _))
      · exact stk
  post := by
    sig_implies_post [rfcCombSpec,Spec.Ecdsa.Rfc6979.P224Sha224.inst,Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig,Spec.Ecdsa.P224.inst,Spec.P224.curve,Spec.Ecdsa.scratchWords,
      abi,argRegs,reduceClassify,Loc.val,State.addr,Abi.withConsts,rfcArm,stkR]
  pub s t _ _ h := by
    sig_pub [rfcCombSpec,Spec.Ecdsa.Rfc6979.P224Sha224.inst,Spec.Ecdsa.Rfc6979.Instance.signContract,
      Spec.Ecdsa.Rfc6979.Instance.signSig,Spec.Ecdsa.P224.inst,Spec.P224.curve,Spec.Ecdsa.scratchWords,
      abi,argRegs,reduceClassify,Loc.val,State.addr,p224CombConsts,Abi.withConsts] at h
    obtain ⟨sp,sy,leak,h0,h1,h2,h3⟩ := h
    refine ⟨sp,h0,h1,h2,h3,(List.cons.inj leak).1,?_⟩
    intro c hc
    simp only [p224CombConsts,List.mem_cons,List.not_mem_nil,or_false] at hc
    subst c
    exact sy
  sat := ⟨rfcCombSat,rfcComb_sat⟩

theorem sign_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified Arm.target (cfgOf (pack hL)).sign rfcCombSpec :=
  Arm.sign_verified (pack hL) implies

theorem signU_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified Arm.target (cfgOf (packU hL)).sign rfcCombSpec :=
  Arm.sign_verified (packU hL) implies

end VG.Proof.Ecdsa.Rfc6979.Arm.P224Sha224Comb
