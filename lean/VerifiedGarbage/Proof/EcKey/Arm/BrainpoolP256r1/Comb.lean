module

public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.EcKey.BrainpoolP256r1
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.ArmComb
public import VerifiedGarbage.Proof.EcKey.Arm.Main
public import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP256r1.Contract
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP256r1.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.Verified
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.CombGenerator
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.CombLit
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
public import VerifiedGarbage.Proof.BrainpoolP256r1.Arm.Comb
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
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
public import VerifiedGarbage.Proof.Weierstrass.MulContract
meta import VerifiedGarbage.Proof.Weierstrass.MulContract

/-!
# brainpoolP256r1 public keys on 32-bit ARM with the generator comb

`vg_ec_brainpoolp256r1_public_key` with `[d]G` by the comb signing uses: the contract
with the comb's table, its constant time, and `Verified`.
-/

@[expose] public section
namespace VG.Proof.EcKey.Arm.BrainpoolP256r1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm.TComb
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.BrainpoolP256r1 VG.Proof.EcKey.Arm

abbrev combPkSpec : Contract isa :=
  Spec.EcKey.BrainpoolP256r1.inst.publicKeyContract (abi.withConsts brainpoolp256r1CombConsts)

def combPkPre (u : Bool) (s : State) : Prop :=
  PkPre (brainpoolp256r1With u) s (constRegs brainpoolp256r1CombConsts s) ∧ ConstsOk brainpoolp256r1CombConsts 0 s

theorem pk_spec_pre {u : Bool} {s : State}
    (h : (Spec.EcKey.BrainpoolP256r1.inst.publicKeyContract abi).pre s) : PkPre (brainpoolp256r1With u) s := by
  sig_pre [Spec.EcKey.BrainpoolP256r1.inst,Spec.EcKey.Instance.publicKeyContract,Spec.EcKey.Instance.publicKeySig,
    Spec.BrainpoolP256r1.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,Loc.val,State.addr] at h
  obtain ⟨_sp,rd,wr,_od,os,ds,fo,fd,fs⟩ := h
  exact ⟨rd,wr,os,ds,fo,fd,fs⟩

theorem combPk_pre {u : Bool} {s : State} (h : combPkSpec.pre s) : combPkPre u s := by
  have hp : (Spec.EcKey.BrainpoolP256r1.inst.publicKeyContract abi).pre (stripConsts brainpoolp256r1CombConsts s) ∧
      ConstsOk brainpoolp256r1CombConsts 0 s := pre_consts.mp h
  have p := pk_spec_pre (u := u) hp.1
  refine ⟨⟨?_,p.wr,p.out_sc,p.d_sc,p.out_fit,p.d_fit,p.sc_fit⟩,hp.2⟩
  rw [← List.take_append_drop (s.rd.length-brainpoolp256r1CombConsts.length) s.rd,hp.2.1]
  exact congrArg (fun rs => rs++constRegs brainpoolp256r1CombConsts s) p.rd

theorem combPk_ok (hC : Law Spec.BrainpoolP256r1.curve) {u : Bool} {s₀ : State} (hp : combPkPre u s₀) :
    WP isa (publicKeyBrainpoolP256r1CombWith u) s₀ fun t => PkKeep (brainpoolp256r1With u) s₀ t ∧ PkPost (brainpoolp256r1With u) s₀ t := by
  have member : (brainpoolp256r1Comb.tsym,brainpoolp256r1CombWords)∈brainpoolp256r1CombConsts := List.mem_singleton_self _
  have ht := tableMem_of_consts hp.2 member
  have hd := table_disjoint_of_consts hp.2 member
    (show (⟨ptr s₀ .r2,8192⟩ : Region)∈s₀.wr by rw [hp.1.wr]; simp)
  exact publicKeyWith_ok (brainpoolp256r1With_ok u) hC hp.1 fun _ S sy => comb_generator_stage hC S sy ht rfl hd

def combPkPub (s t : State) : Prop := pkArm.pub s t ∧ s.syms brainpoolp256r1Comb.tsym=t.syms brainpoolp256r1Comb.tsym

theorem combPk_ct : ConstantTime isa (combPkPre false) combPkPub publicKeyBrainpoolP256r1Comb := by
  refine VG.Taint.constantTime (A := taintSym [brainpoolp256r1Comb.tsym]) (Taint.ofRegs [.r0,.r1,.r2]) ?_
    (by native_taint_decide)
  intro s t _ _ ⟨⟨_,h0,h1,h2⟩,sy⟩
  refine ⟨Taint.agree_ofRegs (fun r hr => ?_),fun n hn => ?_⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    exacts [h0,h1,h2]
  · obtain rfl := List.mem_singleton.mp hn
    exact sy

theorem combPkU_ct : ConstantTime isa (combPkPre true) combPkPub publicKeyBrainpoolP256r1CombU := by
  refine VG.Taint.constantTime (A := taintSymU [brainpoolp256r1Comb.tsym]) (Taint.ofRegs [.r0,.r1,.r2]) ?_
    (by taint_decide)
  intro s t _ _ ⟨⟨_,h0,h1,h2⟩,sy⟩
  refine ⟨Taint.agree_ofRegs (fun r hr => ?_),fun n hn => ?_⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    exacts [h0,h1,h2]
  · obtain rfl := List.mem_singleton.mp hn
    exact sy

open VG.Proof.BrainpoolP256r1.Arm in
def combPkSat : State := {combSatState with
  gpr := fun r => match r with | .r0 => 0x10000 | .r1 => 0x12000 | _ => 0
  rd := [⟨0x12000,32⟩,⟨0x100000,151552⟩]
  wr := [⟨0x10000,65⟩,⟨0,8192⟩] }

open VG.Proof.BrainpoolP256r1.Arm in
theorem combPk_sat : combPkSpec.pre combPkSat := by
  have held := combSat_held
  generalize eqs : combPkSat=s
  sig_pre [combPkSpec,Spec.EcKey.BrainpoolP256r1.inst,Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig,Spec.BrainpoolP256r1.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,
    Loc.val,State.addr,brainpoolp256r1CombConsts,Abi.withConsts,Abi.constRegions,Abi.constsHeld,stackBelow]
  subst s
  rw [comb_words_length]
  rw [comb_words_length] at held
  refine ⟨by decide,by decide,held,by decide,?_,by decide,by decide,?_⟩
  · intro r hr
    change r∈[⟨0x10000,65⟩,⟨0,8192⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

def combPkLocal (u : Bool) : Contract isa where
  pre := combPkPre u
  post := PkPost (brainpoolp256r1With u)
  pub := combPkPub

theorem combPkWith_verified (hC : Weierstrass.Law Spec.BrainpoolP256r1.curve) (u : Bool)
    (hct : ConstantTime isa (combPkPre u) combPkPub (publicKeyBrainpoolP256r1CombWith u)) :
    Verified Arm.target (publicKeyBrainpoolP256r1CombWith u) combPkSpec := by
  refine Verified.of_correct (k := combPkLocal u) (fun s hs => ?_) hct
    ⟨fun _ h => combPk_pre h,?_,?_,⟨combPkSat,combPk_sat⟩⟩
  · obtain ⟨tr,t,exec,keep,post⟩ := combPk_ok hC hs
    exact ⟨tr,t,exec,VG.Proof.Ecdsa.Arm.abi_of_saved keep.saved keep.sp,post⟩
  · intro s t _ post
    sig_post [combPkSpec,Spec.EcKey.BrainpoolP256r1.inst,Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig,Spec.BrainpoolP256r1.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,Abi.withConsts]
    have pp := post_of (u := u) post
    simp only [pkArm,pk,Spec.BrainpoolP256r1.curve,State.addr] at pp
    revert pp
    generalize Spec.EcKey.publicKey _ _=q
    rcases q with _|_|⟨x,y⟩ <;> exact id
  · intro s t _ _ pub
    sig_pub [combPkSpec,Spec.EcKey.BrainpoolP256r1.inst,Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig,Spec.BrainpoolP256r1.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,brainpoolp256r1CombConsts,Abi.withConsts] at pub
    obtain ⟨sp,sy,h0,h1,h2⟩ := pub
    exact ⟨⟨sp,h0,h1,h2⟩,sy⟩

theorem combPk_verified (hC : Weierstrass.Law Spec.BrainpoolP256r1.curve) :
    Verified Arm.target publicKeyBrainpoolP256r1Comb combPkSpec :=
  combPkWith_verified hC false combPk_ct

theorem combPkU_verified (hC : Weierstrass.Law Spec.BrainpoolP256r1.curve) :
    Verified Arm.target publicKeyBrainpoolP256r1CombU combPkSpec :=
  combPkWith_verified hC true combPkU_ct

end VG.Proof.EcKey.Arm.BrainpoolP256r1
