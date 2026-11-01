module

public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.NatPairs
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Contract
public import VerifiedGarbage.Impl.Ecdsa.P384.ArmComb
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.P384.CombGenerator
import VerifiedGarbage.Proof.Ecdsa.Arm.P384.CombLit
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
public import VerifiedGarbage.Proof.P384.Arm.Comb
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Umaal
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp
import Mathlib.Logic.Function.Basic
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Verified
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P384.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.P384.ArmComb
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-!
# ECDSA over P-384 on 32-bit ARM with the generator comb

`vg_ecdsa_p384_sign` with `[k]G` by the shared signed seven-bit comb, whose
table is a read-only constant: the contract with the table, its constant
time, and `Verified`.
-/

@[expose] public section
namespace VG.Proof.Ecdsa.Arm.P384
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm.TComb
open VG.Proof.Ecdsa.Arm

abbrev combSignSpec : Contract isa :=
  Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P384.inst (abi.withConsts p384CombConsts)

def combSignPre (u : Bool) (s : State) : Prop :=
  Pre (p384With u) s (constRegs p384CombConsts s) ∧ ConstsOk p384CombConsts 0 s

theorem sign_spec_pre {u : Bool} {s : State}
    (h : (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P384.inst abi).pre s) : Pre (p384With u) s := by
  sig_pre [Spec.Ecdsa.P384.inst,Proof.Ecdsa.Instance.signContract,Proof.Ecdsa.Instance.signSig,
    Spec.P384.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,Loc.val,State.addr,stackArgAddr,
    BitVec.add_zero] at h
  obtain ⟨sp,rd,wr,_od,_oh,_ok,os,oa,ds,hs,ks,sa,fo,fd,fh,fk,fs⟩ := h
  exact ⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp⟩

theorem combSign_pre {u : Bool} {s : State} (h : combSignSpec.pre s) : combSignPre u s := by
  have hp : (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P384.inst abi).pre (stripConsts p384CombConsts s) ∧
      ConstsOk p384CombConsts 0 s := pre_consts.mp h
  have p := sign_spec_pre (u := u) hp.1
  refine ⟨⟨?_,p.wr,p.out_sc,p.d_sc,p.digest_sc,p.k_sc,p.out_args,p.sc_args,
    p.out_fit,p.d_fit,p.digest_fit,p.k_fit,p.sc_fit,p.sp_fit⟩,hp.2⟩
  rw [← List.take_append_drop (s.rd.length-p384CombConsts.length) s.rd,hp.2.1]
  exact congrArg (fun rs => rs++constRegs p384CombConsts s) p.rd

def combSignPub (s t : State) : Prop := signArm.pub s t ∧ s.syms p384Comb.tsym=t.syms p384Comb.tsym

theorem combSign_ct : ConstantTime isa (combSignPre false) combSignPub signP384Comb := by
  refine VG.Taint.constantTime (A := taintSym [p384Comb.tsym]) τ₀ ?_ (by native_taint_decide)
  intro s t hs ht pub
  exact ⟨agree₀ hs.1 ht.1 pub.1,fun n hn => by
    obtain rfl := List.mem_singleton.mp hn
    exact pub.2⟩

theorem combSignU_ct : ConstantTime isa (combSignPre true) combSignPub signP384CombU := by
  refine VG.Taint.constantTime (A := taintSymU [p384Comb.tsym]) τ₀ ?_ (by taint_decide)
  intro s t hs ht pub
  exact ⟨agree₀ hs.1 ht.1 pub.1,fun n hn => by
    obtain rfl := List.mem_singleton.mp hn
    exact pub.2⟩

theorem combSign_ok (hC : Law Spec.P384.curve) {u : Bool} {s₀ : State} (hp : combSignPre u s₀) :
    WP isa (signP384CombWith u) s₀ fun t => SignKeep (p384With u) s₀ t ∧ SignPost (p384With u) s₀ t := by
  have member : (p384Comb.tsym,p384CombWords)∈p384CombConsts := List.mem_singleton_self _
  have ht := tableMem_of_consts hp.2 member
  have hd := table_disjoint_of_consts hp.2 member
    (show scR s₀∈s₀.wr by rw [hp.1.wr]; simp)
  exact signWith_ok (p384With_ok u) hC hp.1 fun _ S sy => comb_generator_stage hC S sy ht rfl hd

open VG.Proof.P384.Arm in
theorem combSign_sat : combSignSpec.pre combSatState := by
  have arg := combSat_stackArg
  have held := combSat_held
  generalize eqs : combSatState=s
  sig_pre [combSignSpec,Spec.Ecdsa.P384.inst,Proof.Ecdsa.Instance.signContract,
    Proof.Ecdsa.Instance.signSig,Spec.P384.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
    Loc.val,State.addr,stackArgAddr,BitVec.add_zero,p384CombConsts,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,stackBelow]
  subst s
  rw [arg,comb_words_length]
  rw [comb_words_length] at held
  refine ⟨by decide,by decide,held,by decide,?_,by decide,by decide,?_⟩
  · intro r hr
    change r∈[⟨0x10000,96⟩,⟨0,8192⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

def combSignLocal (u : Bool) : Contract isa where
  pre := combSignPre u
  post := SignPost (p384With u)
  pub := combSignPub

theorem combSignWith_verified (hC : Weierstrass.Law Spec.P384.curve) (u : Bool)
    (hct : ConstantTime isa (combSignPre u) combSignPub (signP384CombWith u)) :
    Verified Arm.target (signP384CombWith u) combSignSpec := by
  refine Verified.of_correct (k := combSignLocal u) (fun s hs => ?_) hct
    ⟨fun _ h => combSign_pre h,?_,?_,⟨VG.Proof.P384.Arm.combSatState,combSign_sat⟩⟩
  · obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hC hs
    exact ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,post⟩
  · intro s t _ post
    sig_post [combSignSpec,Spec.Ecdsa.P384.inst,Proof.Ecdsa.Instance.signContract,
      Proof.Ecdsa.Instance.signSig,Spec.P384.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,stackArgAddr,BitVec.add_zero,Abi.withConsts]
    rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
    exact post
  · intro s t _ _ pub
    sig_pub [combSignSpec,Spec.Ecdsa.P384.inst,Proof.Ecdsa.Instance.signContract,
      Proof.Ecdsa.Instance.signSig,Spec.P384.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,stackArgAddr,BitVec.add_zero,p384CombConsts,Abi.withConsts] at pub
    obtain ⟨sp,sy,h0,h1,h2,h3,ha⟩ := pub
    exact ⟨⟨sp,h0,h1,h2,h3,ha⟩,sy⟩

theorem combSign_verified (hC : Weierstrass.Law Spec.P384.curve) :
    Verified Arm.target signP384Comb combSignSpec :=
  combSignWith_verified hC false combSign_ct

theorem combSignU_verified (hC : Weierstrass.Law Spec.P384.curve) :
    Verified Arm.target signP384CombU combSignSpec :=
  combSignWith_verified hC true combSignU_ct

end VG.Proof.Ecdsa.Arm.P384
