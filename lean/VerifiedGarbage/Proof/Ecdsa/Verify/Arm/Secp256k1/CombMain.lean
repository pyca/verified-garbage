module

public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Front
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.Arm
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.ArmComb
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.Verified
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombGenerator
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Verified
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombScan
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Verification shares the generator comb with signing and key generation. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Impl.Ecdsa.Verify.Arm (U)
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.Secp256k1
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass.Arm.TComb

abbrev combVerifySpec : Contract isa :=
  Spec.Ecdsa.Secp256k1.inst.verifyContract (abi.withConsts secp256k1CombConsts)

def combVerifyPre (s : State) : Prop :=
  VPre secp256k1 s (constRegs secp256k1CombConsts s) ∧ ConstsOk secp256k1CombConsts 0 s

theorem verify_spec_pre {s : State}
    (h : (Spec.Ecdsa.Secp256k1.inst.verifyContract abi).pre s) : VPre secp256k1 s := by
  sig_pre [Spec.Ecdsa.Secp256k1.inst,Spec.Ecdsa.Instance.verifyContract,Spec.Ecdsa.Instance.verifySig,
    Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,Loc.val,State.addr] at h
  obtain ⟨_sp,rd,wr,ps,ds,ss,fp,fd,fs,fc⟩ := h
  exact ⟨rd,wr,ps,ds,ss,fp,fd,fs,fc⟩

theorem combVerify_pre {s : State} (h : combVerifySpec.pre s) : combVerifyPre s := by
  have hp : (Spec.Ecdsa.Secp256k1.inst.verifyContract abi).pre (stripConsts secp256k1CombConsts s) ∧
      ConstsOk secp256k1CombConsts 0 s := pre_consts.mp h
  have p := verify_spec_pre hp.1
  refine ⟨⟨?_,p.wr,p.pk_sc,p.dg_sc,p.sig_sc,p.pk_fit,p.dg_fit,p.sig_fit,p.sc_fit⟩,hp.2⟩
  rw [← List.take_append_drop (s.rd.length-secp256k1CombConsts.length) s.rd,hp.2.1]
  exact congrArg (fun rs => rs++constRegs secp256k1CombConsts s) p.rd

theorem combVerify_ok (hC : Law Spec.Secp256k1.curve) {s₀ : State} (hp : combVerifyPre s₀) :
    WP isa verifySecp256k1Comb s₀ fun t => VKeep s₀ t ∧ VPost secp256k1 s₀ t := by
  have member : (secp256k1Comb.tsym,secp256k1CombWords)∈secp256k1CombConsts := List.mem_singleton_self _
  have ht := tableMem_of_consts hp.2 member
  have hd := table_disjoint_of_consts hp.2 member
    (show (⟨ptr s₀ .r3,8192⟩ : Region)∈s₀.wr by rw [hp.1.wr]; simp)
  apply verifyWith_ok secp256k1_ok hC hp.1 (a0₁ := false) nofun
  intro s M syms
  intro u hs hf F _ _ _ _ _ _ bits _ keep unch syu
  have frame : Frame [⟨ptr s₀ .r3,8192⟩] s₀.mem u.mem := outside_frame
    (unch.outside (o := 0) (n := 8192) (by simp)) (Nat.le_refl _)
  have hu := ht.of_frame (by rw [keep.rd,keep.wr]) frame
    (by simpa only [List.mem_singleton,forall_eq] using hd)
  have mul := comb_generator_ok hC hs hf F hu (by rw [syu,syms])
    (hd.sub_right (Region.sub_prefix (by decide))) (k := sv secp256k1 (ptr s₀ .r3) s U)
    (VG.Proof.Mont.wordsVal_lt _ _ _ _) (bits rfl)
  exact WP.mono mul fun _ post => by simpa only [GeneratorPost,Nat.shiftRight_zero] using post

end VG.Proof.Ecdsa.Verify.Arm.Secp256k1
