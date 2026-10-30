module

public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.EcKey.P224
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.Ecdsa.P224.ArmComb
public import VerifiedGarbage.Proof.EcKey.Arm.Main
public import VerifiedGarbage.Proof.EcKey.Arm.P224.Contract
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
import VerifiedGarbage.Proof.EcKey.Arm.P224.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.CombGenerator
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.CombLit
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
public import VerifiedGarbage.Proof.P224.Arm.Comb
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
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
# P-224 public keys on 32-bit ARM with the generator comb

`vg_ec_p224_public_key` with `[d]G` by the comb signing uses: the contract
with the comb's table, its constant time, and `Verified`.
-/

@[expose] public section
namespace VG.Proof.EcKey.Arm.P224
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm.TComb
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P224 VG.Proof.EcKey.Arm

abbrev combPkSpec : Contract isa :=
  Spec.EcKey.P224.inst.publicKeyContract (abi.withConsts p224CombConsts)

def combPkPre (s : State) : Prop :=
  PkPre p224 s (constRegs p224CombConsts s) ∧ ConstsOk p224CombConsts 0 s

theorem pk_spec_pre {s : State}
    (h : (Spec.EcKey.P224.inst.publicKeyContract abi).pre s) : PkPre p224 s := by
  sig_pre [Spec.EcKey.P224.inst,Spec.EcKey.Instance.publicKeyContract,Spec.EcKey.Instance.publicKeySig,
    Spec.P224.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,Loc.val,State.addr] at h
  obtain ⟨_sp,rd,wr,_od,os,ds,fo,fd,fs⟩ := h
  exact ⟨rd,wr,os,ds,fo,fd,fs⟩

theorem combPk_pre {s : State} (h : combPkSpec.pre s) : combPkPre s := by
  have hp : (Spec.EcKey.P224.inst.publicKeyContract abi).pre (stripConsts p224CombConsts s) ∧
      ConstsOk p224CombConsts 0 s := pre_consts.mp h
  have p := pk_spec_pre hp.1
  refine ⟨⟨?_,p.wr,p.out_sc,p.d_sc,p.out_fit,p.d_fit,p.sc_fit⟩,hp.2⟩
  rw [← List.take_append_drop (s.rd.length-p224CombConsts.length) s.rd,hp.2.1]
  exact congrArg (fun rs => rs++constRegs p224CombConsts s) p.rd

theorem combPk_ok (hC : Law Spec.P224.curve) {s₀ : State} (hp : combPkPre s₀) :
    WP isa publicKeyP224Comb s₀ fun t => PkKeep p224 s₀ t ∧ PkPost p224 s₀ t := by
  have member : (p224Comb.tsym,p224CombWords)∈p224CombConsts := List.mem_singleton_self _
  have ht := tableMem_of_consts hp.2 member
  have hd := table_disjoint_of_consts hp.2 member
    (show (⟨ptr s₀ .r2,8192⟩ : Region)∈s₀.wr by rw [hp.1.wr]; simp)
  exact publicKeyWith_ok p224_ok hC hp.1 fun _ S sy => comb_generator_stage hC S sy ht rfl hd

def combPkPub (s t : State) : Prop := pkArm.pub s t ∧ s.syms p224Comb.tsym=t.syms p224Comb.tsym

theorem combPk_ct : ConstantTime isa combPkPre combPkPub publicKeyP224Comb := by
  refine VG.Taint.constantTime (A := taintSym [p224Comb.tsym]) (Taint.ofRegs [.r0,.r1,.r2]) ?_
    (by native_taint_decide)
  intro s t _ _ ⟨⟨_,h0,h1,h2⟩,sy⟩
  refine ⟨Taint.agree_ofRegs (fun r hr => ?_),fun n hn => ?_⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    exacts [h0,h1,h2]
  · obtain rfl := List.mem_singleton.mp hn
    exact sy

open VG.Proof.P224.Arm in
def combPkSat : State := {combSatState with
  gpr := fun r => match r with | .r0 => 0x10000 | .r1 => 0x12000 | _ => 0
  rd := [⟨0x12000,28⟩,⟨0x100000,131072⟩]
  wr := [⟨0x10000,57⟩,⟨0,8192⟩] }

open VG.Proof.P224.Arm in
theorem combPk_sat : combPkSpec.pre combPkSat := by
  have held := combSat_held
  generalize eqs : combPkSat=s
  sig_pre [combPkSpec,Spec.EcKey.P224.inst,Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig,Spec.P224.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,
    Loc.val,State.addr,p224CombConsts,Abi.withConsts,Abi.constRegions,Abi.constsHeld,stackBelow]
  subst s
  rw [comb_words_length]
  rw [comb_words_length] at held
  refine ⟨by decide,by decide,held,by decide,?_,by decide,by decide,?_⟩
  · intro r hr
    change r∈[⟨0x10000,57⟩,⟨0,8192⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

def combPkLocal : Contract isa where
  pre := combPkPre
  post := PkPost p224
  pub := combPkPub

theorem combPk_verified (hC : Weierstrass.Law Spec.P224.curve) :
    Verified Arm.target publicKeyP224Comb combPkSpec := by
  refine Verified.of_correct (k := combPkLocal) (fun s hs => ?_) combPk_ct
    ⟨fun _ h => combPk_pre h,?_,?_,⟨combPkSat,combPk_sat⟩⟩
  · obtain ⟨tr,t,exec,keep,post⟩ := combPk_ok hC hs
    exact ⟨tr,t,exec,VG.Proof.Ecdsa.Arm.abi_of_saved keep.saved keep.sp,post⟩
  · intro s t _ post
    sig_post [combPkSpec,Spec.EcKey.P224.inst,Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig,Spec.P224.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,Abi.withConsts]
    have pp := post_of post
    simp only [pkArm,pk,Spec.P224.curve,State.addr] at pp
    revert pp
    generalize Spec.EcKey.publicKey _ _=q
    rcases q with _|_|⟨x,y⟩ <;> exact id
  · intro s t _ _ pub
    sig_pub [combPkSpec,Spec.EcKey.P224.inst,Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig,Spec.P224.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,p224CombConsts,Abi.withConsts] at pub
    obtain ⟨sp,sy,h0,h1,h2⟩ := pub
    exact ⟨⟨sp,h0,h1,h2⟩,sy⟩

end VG.Proof.EcKey.Arm.P224
