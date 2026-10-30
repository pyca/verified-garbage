module

public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Spec.Ecdsa.P224
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Front
public import VerifiedGarbage.Impl.Ecdsa.P224.ArmComb
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P224.Contract
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.P224.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.CombGenerator
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.CombLit
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
public import VerifiedGarbage.Proof.P224.Arm.Comb
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombScan
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P224.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.P224.ArmComb
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-!
# ECDSA verification over P-224 on 32-bit ARM with the generator comb

`vg_ecdsa_p224_verify` with `[u]G` by the comb signing uses (`[v]Q` stays a
call of `vg_p224_mul`): the contract with the comb's table, its constant
time, and `Verified`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.Arm.P224
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Impl.Ecdsa.Verify.Arm (U)
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P224 VG.Proof.Ecdsa.Verify.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass.Arm.TComb
open VG.Proof.Mont VG.Proof.Mont.Arm

abbrev combVerifySpec : Contract isa :=
  Spec.Ecdsa.P224.inst.verifyContract (abi.withConsts p224CombConsts)

def combVerifyPre (s : State) : Prop :=
  VPre p224 s (constRegs p224CombConsts s) ∧ ConstsOk p224CombConsts 0 s

theorem verify_spec_pre {s : State}
    (h : (Spec.Ecdsa.P224.inst.verifyContract abi).pre s) : VPre p224 s := by
  sig_pre [Spec.Ecdsa.P224.inst,Spec.Ecdsa.Instance.verifyContract,Spec.Ecdsa.Instance.verifySig,
    Spec.P224.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,Loc.val,State.addr] at h
  obtain ⟨_sp,rd,wr,ps,ds,ss,fp,fd,fs,fc⟩ := h
  exact ⟨rd,wr,ps,ds,ss,fp,fd,fs,fc⟩

theorem combVerify_pre {s : State} (h : combVerifySpec.pre s) : combVerifyPre s := by
  have hp : (Spec.Ecdsa.P224.inst.verifyContract abi).pre (stripConsts p224CombConsts s) ∧
      ConstsOk p224CombConsts 0 s := pre_consts.mp h
  have p := verify_spec_pre hp.1
  refine ⟨⟨?_,p.wr,p.pk_sc,p.dg_sc,p.sig_sc,p.pk_fit,p.dg_fit,p.sig_fit,p.sc_fit⟩,hp.2⟩
  rw [← List.take_append_drop (s.rd.length-p224CombConsts.length) s.rd,hp.2.1]
  exact congrArg (fun rs => rs++constRegs p224CombConsts s) p.rd

theorem combVerify_ok (hC : Law Spec.P224.curve) {s₀ : State} (hp : combVerifyPre s₀) :
    WP isa verifyP224Comb s₀ fun t => VKeep s₀ t ∧ VPost p224 s₀ t := by
  have member : (p224Comb.tsym,p224CombWords)∈p224CombConsts := List.mem_singleton_self _
  have ht := tableMem_of_consts hp.2 member
  have hd := table_disjoint_of_consts hp.2 member
    (show (⟨ptr s₀ .r3,8192⟩ : Region)∈s₀.wr by rw [hp.1.wr]; simp)
  apply verifyWith_ok p224_ok hC hp.1 (a0₁ := false) nofun
  intro s M syms
  intro u hs hf F _ _ _ _ _ _ _ kv keep unch syu
  have frame : Frame [⟨ptr s₀ .r3,8192⟩] s₀.mem u.mem := outside_frame
    (unch.outside (o := 0) (n := 8192) (by simp)) (Nat.le_refl _)
  have hu := ht.of_frame (by rw [keep.rd,keep.wr]) frame
    (by simpa only [List.mem_singleton,forall_eq] using hd)
  have k_eq : sv p224 (ptr s₀ .r3) u K=sv p224 (ptr s₀ .r3) s U := kv rfl
  -- The table of `u`'s bits, from `K`'s slot.
  refine WP.seq (WP.mono_syms (tbl_bits_ok p224_ok hs hf (i := K) (j := 0) (by decide) (by decide))
    fun u₂ ⟨b₂,k₂,O₂⟩ sy₂ => ?_)
  have hs₂ := hs.of_rest k₂ (by decide)
  have hf₂ := hf.of_rest k₂
  have F₂ := F.unch p224_ok.n10 hs.nowrap (W := [(bitsAt p224.n 0,64*p224.n)])
    (fun w hw => Or.inr (by rw [List.mem_singleton.mp hw]; decide)) O₂.unch
  have hu₂ := hu.of_frame (by rw [k₂.rd,k₂.wr]) (outside_frame O₂ (size := 8192) (by decide))
    (by simpa only [List.mem_singleton,forall_eq] using hd)
  have bits : ∀ i<224,u₂.mem (off (ptr s₀ .r3) (bitsAt p224.n 0+i))=
      if (sv p224 (ptr s₀ .r3) s U).testBit i then 1 else 0 := fun i hi => by
    rw [b₂ i (by change i < 64 * 4; omega)]
    simp only [sv] at k_eq
    rw [k_eq]
  have mul := comb_generator_ok hC hs₂ hf₂ F₂ hu₂ (by rw [sy₂,syu,syms])
    (hd.sub_right (Region.sub_prefix (by decide))) (k := sv p224 (ptr s₀ .r3) s U)
    (Nat.lt_trans M.u_lt (by decide)) bits
  refine WP.mono mul fun t ⟨R,U',Mo,L,Rp⟩ => ⟨(k₂.mono (by decide)).trans R,
    (O₂.unch.trans U').mono fun w hw => ?_,Mo,L,by simpa only [Nat.shiftRight_zero] using Rp⟩
  rcases List.mem_append.mp hw with h|h
  · rw [List.mem_singleton.mp h]
    exact List.mem_append_right _ (by simp [genX])
  · exact h

def combVerifyPub (s t : State) : Prop := verifyArm.pub s t ∧ s.syms p224Comb.tsym=t.syms p224Comb.tsym

theorem combVerify_ct : ConstantTime isa combVerifyPre combVerifyPub verifyP224Comb := by
  refine VG.Taint.constantTime (A := taintSym [p224Comb.tsym]) (Taint.ofRegs [.r0,.r1,.r2,.r3]) ?_
    (by native_taint_decide)
  intro s t _ _ ⟨⟨_,h0,h1,h2,h3⟩,sy⟩
  refine ⟨Taint.agree_ofRegs (fun r hr => ?_),fun n hn => ?_⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    exacts [h0,h1,h2,h3]
  · obtain rfl := List.mem_singleton.mp hn
    exact sy

open VG.Proof.P224.Arm in
def combVerifySat : State := {combSatState with
  gpr := fun r => match r with | .r0 => 0x10000 | .r1 => 0x12000 | .r2 => 0x14000 | _ => 0
  rd := [⟨0x10000,57⟩,⟨0x12000,28⟩,⟨0x14000,56⟩,⟨0x100000,131072⟩]
  wr := [⟨0,8192⟩] }

open VG.Proof.P224.Arm in
theorem combVerify_sat : combVerifySpec.pre combVerifySat := by
  have held := combSat_held
  generalize eqs : combVerifySat=s
  sig_pre [combVerifySpec,Spec.Ecdsa.P224.inst,Spec.Ecdsa.Instance.verifyContract,
    Spec.Ecdsa.Instance.verifySig,Spec.P224.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
    Loc.val,State.addr,p224CombConsts,Abi.withConsts,Abi.constRegions,Abi.constsHeld,stackBelow]
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

def combVerifyLocal : Contract isa where
  pre := combVerifyPre
  post := VPost p224
  pub := combVerifyPub

theorem combVerify_verified (hC : Weierstrass.Law Spec.P224.curve) :
    Verified Arm.target verifyP224Comb combVerifySpec := by
  refine Verified.of_correct (k := combVerifyLocal) (fun s hs => ?_) combVerify_ct
    ⟨fun _ h => combVerify_pre h,?_,?_,⟨combVerifySat,combVerify_sat⟩⟩
  · obtain ⟨tr,t,exec,keep,post⟩ := combVerify_ok hC hs
    exact ⟨tr,t,exec,VG.Proof.Ecdsa.Arm.abi_of_saved keep.saved keep.sp,post⟩
  · intro s t _ post
    sig_post [combVerifySpec,Spec.Ecdsa.P224.inst,Spec.Ecdsa.Instance.verifyContract,
      Spec.Ecdsa.Instance.verifySig,Spec.P224.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,Abi.withConsts]
    rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
    exact post
  · intro s t _ _ pub
    sig_pub [combVerifySpec,Spec.Ecdsa.P224.inst,Spec.Ecdsa.Instance.verifyContract,
      Spec.Ecdsa.Instance.verifySig,Spec.P224.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,p224CombConsts,Abi.withConsts] at pub
    obtain ⟨sp,sy,_inputs,h0,h1,h2,h3⟩ := pub
    exact ⟨⟨sp,h0,h1,h2,h3⟩,sy⟩

end VG.Proof.Ecdsa.Verify.Arm.P224
