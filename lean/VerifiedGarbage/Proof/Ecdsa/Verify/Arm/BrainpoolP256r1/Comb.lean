module

public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Front
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.ArmComb
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP256r1.Contract
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.BrainpoolP256r1.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.CombGenerator
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.CombLit
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
public import VerifiedGarbage.Proof.BrainpoolP256r1.Arm.Comb
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombScan
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.ArmComb
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-!
# ECDSA verification over brainpoolP256r1 on 32-bit ARM with the generator comb

`vg_ecdsa_brainpoolp256r1_verify` with `[u]G` by the comb signing uses (`[v]Q` stays
the ladder): the contract with the comb's table, its constant
time, and `Verified`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.Arm.BrainpoolP256r1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Impl.Ecdsa.Verify.Arm (U)
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.BrainpoolP256r1 VG.Proof.Ecdsa.Verify.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass.Arm.TComb
open VG.Proof.Mont VG.Proof.Mont.Arm

abbrev combVerifySpec : Contract isa :=
  Spec.Ecdsa.BrainpoolP256r1.inst.verifyContract (abi.withConsts brainpoolp256r1CombConsts)

def combVerifyPre (um : Bool) (s : State) : Prop :=
  VPre (brainpoolp256r1With um) s (constRegs brainpoolp256r1CombConsts s) ∧ ConstsOk brainpoolp256r1CombConsts 0 s

theorem verify_spec_pre {um : Bool} {s : State}
    (h : (Spec.Ecdsa.BrainpoolP256r1.inst.verifyContract abi).pre s) : VPre (brainpoolp256r1With um) s := by
  sig_pre [Spec.Ecdsa.BrainpoolP256r1.inst,Spec.Ecdsa.Instance.verifyContract,Spec.Ecdsa.Instance.verifySig,
    Spec.BrainpoolP256r1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,Loc.val,State.addr] at h
  obtain ⟨_sp,rd,wr,ps,ds,ss,fp,fd,fs,fc⟩ := h
  exact ⟨rd,wr,ps,ds,ss,fp,fd,fs,fc⟩

theorem combVerify_pre {um : Bool} {s : State} (h : combVerifySpec.pre s) : combVerifyPre um s := by
  have hp : (Spec.Ecdsa.BrainpoolP256r1.inst.verifyContract abi).pre (stripConsts brainpoolp256r1CombConsts s) ∧
      ConstsOk brainpoolp256r1CombConsts 0 s := pre_consts.mp h
  have p := verify_spec_pre (um := um) hp.1
  refine ⟨⟨?_,p.wr,p.pk_sc,p.dg_sc,p.sig_sc,p.pk_fit,p.dg_fit,p.sig_fit,p.sc_fit⟩,hp.2⟩
  rw [← List.take_append_drop (s.rd.length-brainpoolp256r1CombConsts.length) s.rd,hp.2.1]
  exact congrArg (fun rs => rs++constRegs brainpoolp256r1CombConsts s) p.rd

theorem combVerify_ok (hC : Law Spec.BrainpoolP256r1.curve) {um : Bool} {s₀ : State} (hp : combVerifyPre um s₀) :
    WP isa (verifyBrainpoolP256r1CombWith um) s₀ fun t => VKeep s₀ t ∧ VPost (brainpoolp256r1With um) s₀ t := by
  have member : (brainpoolp256r1Comb.tsym,brainpoolp256r1CombWords)∈brainpoolp256r1CombConsts := List.mem_singleton_self _
  have ht := tableMem_of_consts hp.2 member
  have hd := table_disjoint_of_consts hp.2 member
    (show (⟨ptr s₀ .r3,8192⟩ : Region)∈s₀.wr by rw [hp.1.wr]; simp)
  apply verifyWith_ok (brainpoolp256r1With_ok um) hC hp.1 (a0₁ := false) nofun
  intro s M syms
  intro u hs hf F _ _ _ _ _ _ bits _ keep unch syu
  have frame : Frame [⟨ptr s₀ .r3,8192⟩] s₀.mem u.mem := outside_frame
    (unch.outside (o := 0) (n := 8192) (by simp)) (Nat.le_refl _)
  have hu := ht.of_frame (by rw [keep.rd,keep.wr]) frame
    (by simpa only [List.mem_singleton,forall_eq] using hd)
  have mul := comb_generator_ok hC hs hf F hu (by rw [syu,syms]; rfl)
    (hd.sub_right (Region.sub_prefix (by decide))) (k := sv (brainpoolp256r1With um) (ptr s₀ .r3) s U)
    (VG.Proof.Mont.wordsVal_lt _ _ _ _) (bits rfl)
  exact WP.mono mul fun _ post => by simpa only [GeneratorPost,Nat.shiftRight_zero] using post

def combVerifyPub (s t : State) : Prop := verifyArm.pub s t ∧ s.syms brainpoolp256r1Comb.tsym=t.syms brainpoolp256r1Comb.tsym

theorem combVerify_ct : ConstantTime isa (combVerifyPre false) combVerifyPub verifyBrainpoolP256r1Comb := by
  refine VG.Taint.constantTime (A := taintSym [brainpoolp256r1Comb.tsym]) (Taint.ofRegs [.r0,.r1,.r2,.r3]) ?_
    (by native_taint_decide)
  intro s t _ _ ⟨⟨_,h0,h1,h2,h3⟩,sy⟩
  refine ⟨Taint.agree_ofRegs (fun r hr => ?_),fun n hn => ?_⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    exacts [h0,h1,h2,h3]
  · obtain rfl := List.mem_singleton.mp hn
    exact sy

theorem combVerifyU_ct : ConstantTime isa (combVerifyPre true) combVerifyPub verifyBrainpoolP256r1CombU := by
  refine VG.Taint.constantTime (A := taintSymU [brainpoolp256r1Comb.tsym]) (Taint.ofRegs [.r0,.r1,.r2,.r3]) ?_
    (by taint_decide)
  intro s t _ _ ⟨⟨_,h0,h1,h2,h3⟩,sy⟩
  refine ⟨Taint.agree_ofRegs (fun r hr => ?_),fun n hn => ?_⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    exacts [h0,h1,h2,h3]
  · obtain rfl := List.mem_singleton.mp hn
    exact sy

open VG.Proof.BrainpoolP256r1.Arm in
def combVerifySat : State := {combSatState with
  gpr := fun r => match r with | .r0 => 0x10000 | .r1 => 0x12000 | .r2 => 0x14000 | _ => 0
  rd := [⟨0x10000,65⟩,⟨0x12000,32⟩,⟨0x14000,64⟩,⟨0x100000,151552⟩]
  wr := [⟨0,8192⟩] }

open VG.Proof.BrainpoolP256r1.Arm in
theorem combVerify_sat : combVerifySpec.pre combVerifySat := by
  have held := combSat_held
  generalize eqs : combVerifySat=s
  sig_pre [combVerifySpec,Spec.Ecdsa.BrainpoolP256r1.inst,Spec.Ecdsa.Instance.verifyContract,
    Spec.Ecdsa.Instance.verifySig,Spec.BrainpoolP256r1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
    Loc.val,State.addr,brainpoolp256r1CombConsts,Abi.withConsts,Abi.constRegions,Abi.constsHeld,stackBelow]
  subst s
  rw [comb_words_length]
  rw [comb_words_length] at held
  refine ⟨by decide,by decide,held,by decide,?_,by decide,by decide,?_⟩
  · intro r hr
    change r∈[⟨0,8192⟩] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

def combVerifyLocal (um : Bool) : Contract isa where
  pre := combVerifyPre um
  post := VPost (brainpoolp256r1With um)
  pub := combVerifyPub

theorem combVerifyWith_verified (hC : Weierstrass.Law Spec.BrainpoolP256r1.curve) (um : Bool)
    (hct : ConstantTime isa (combVerifyPre um) combVerifyPub (verifyBrainpoolP256r1CombWith um)) :
    Verified Arm.target (verifyBrainpoolP256r1CombWith um) combVerifySpec := by
  refine Verified.of_correct (k := combVerifyLocal um) (fun s hs => ?_) hct
    ⟨fun _ h => combVerify_pre h,?_,?_,⟨combVerifySat,combVerify_sat⟩⟩
  · obtain ⟨tr,t,exec,keep,post⟩ := combVerify_ok hC hs
    exact ⟨tr,t,exec,VG.Proof.Ecdsa.Arm.abi_of_saved keep.saved keep.sp,post⟩
  · intro s t _ post
    sig_post [combVerifySpec,Spec.Ecdsa.BrainpoolP256r1.inst,Spec.Ecdsa.Instance.verifyContract,
      Spec.Ecdsa.Instance.verifySig,Spec.BrainpoolP256r1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,Abi.withConsts]
    rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
    exact post
  · intro s t _ _ pub
    sig_pub [combVerifySpec,Spec.Ecdsa.BrainpoolP256r1.inst,Spec.Ecdsa.Instance.verifyContract,
      Spec.Ecdsa.Instance.verifySig,Spec.BrainpoolP256r1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,brainpoolp256r1CombConsts,Abi.withConsts] at pub
    obtain ⟨sp,sy,_inputs,h0,h1,h2,h3⟩ := pub
    exact ⟨⟨sp,h0,h1,h2,h3⟩,sy⟩

theorem combVerify_verified (hC : Weierstrass.Law Spec.BrainpoolP256r1.curve) :
    Verified Arm.target verifyBrainpoolP256r1Comb combVerifySpec :=
  combVerifyWith_verified hC false combVerify_ct

theorem combVerifyU_verified (hC : Weierstrass.Law Spec.BrainpoolP256r1.curve) :
    Verified Arm.target verifyBrainpoolP256r1CombU combVerifySpec :=
  combVerifyWith_verified hC true combVerifyU_ct

end VG.Proof.Ecdsa.Verify.Arm.BrainpoolP256r1
