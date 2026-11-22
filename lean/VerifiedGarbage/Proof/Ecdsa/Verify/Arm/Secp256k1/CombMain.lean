module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Main
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.Arm
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.ArmComb
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombGenerator
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Verified
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombConsts
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombCorrect
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Verification shares the generator comb with signing and key generation. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Impl.Ecdsa.Verify.Arm (U)
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.Secp256k1
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass.Arm.TComb
open VG.Proof.Mont VG.Proof.Mont.Arm

/-- The tables verification reads: the comb's, and the setup's constants. -/
abbrev combVerifyK (um : Bool) : List (String × List (BitVec 64)) := secp256k1CombConsts ++ (secp256k1With um).constsK

abbrev combVerifySpec (um : Bool) : Contract isa :=
  Proof.Ecdsa.verifyContract Spec.Ecdsa.Secp256k1.inst (abi.withConsts (combVerifyK um))

def combVerifyPre (um : Bool) (s : State) : Prop :=
  VPre (secp256k1With um) s (constRegs (combVerifyK um) s) ∧ ConstsOk (combVerifyK um) 0 s

theorem combVerify_pre {um : Bool} {s : State} (h : (combVerifySpec um).pre s) : combVerifyPre um s := by
  have hp : (Proof.Ecdsa.verifyContract Spec.Ecdsa.Secp256k1.inst abi).pre (stripConsts (combVerifyK um) s) ∧
      ConstsOk (combVerifyK um) 0 s := pre_consts.mp h
  obtain ⟨h₁, hk⟩ := hp
  sig_pre [Spec.Ecdsa.Secp256k1.inst,Proof.Ecdsa.verifyContract,Proof.Ecdsa.verifySig,
    Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,Loc.val,State.addr] at h₁
  obtain ⟨_sp,rd,wr,ps,ds,ss,fp,fd,fs,fc⟩ := h₁
  refine ⟨⟨hk.rd_strip rd,wr,ps,ds,ss,fp,fd,fs,fc,fun _ => tbl_of_consts hk
    (List.mem_append_right _ (List.mem_singleton_self _)) ?_⟩,hk⟩
  rw [wr]; exact List.mem_singleton_self _

/-- Verification's `[u]G` by the comb, as `verifyWith_ok` and `verifyHead_ok` ask. -/
theorem comb_generatorWP (hC : Law Spec.Secp256k1.curve) {um : Bool} {s₀ : State} (hp : combVerifyPre um s₀) :
    ∀ s, Mid (secp256k1With um) s₀ (ptr s₀ .r3) s → s.syms = s₀.syms →
      GeneratorWP (secp256k1With um) (verifyGeneratorSecp256k1With um) s₀ (ptr s₀ .r3)
        (sv (secp256k1With um) (ptr s₀ .r3) s U)
        (fun j X Y Z => Rep (secp256k1With um).C X Y Z
          (Spec.Weierstrass.mul (sv (secp256k1With um) (ptr s₀ .r3) s U >>> j) (Spec.Weierstrass.G (secp256k1With um).C)))
        s.syms false := by
  have member : (secp256k1Comb.tsym,secp256k1CombWords)∈combVerifyK um := List.mem_cons_self
  have ht := tableMem_of_consts hp.2 member
  have hd := table_disjoint_of_consts hp.2 member
    (show (⟨ptr s₀ .r3,8192⟩ : Region)∈s₀.wr by rw [hp.1.wr]; simp)
  intro s M syms
  intro u hs hf F _ _ _ _ _ _ _ kv keep unch syu
  have frame : Frame [⟨ptr s₀ .r3,8192⟩] s₀.mem u.mem := outside_frame
    (unch.outside (o := 0) (n := 8192) (by simp)) (Nat.le_refl _)
  have hu := ht.of_frame (by rw [keep.rd,keep.wr]) frame
    (by simpa only [List.mem_singleton,forall_eq] using hd)
  have k_eq : sv (secp256k1With um) (ptr s₀ .r3) u K=sv (secp256k1With um) (ptr s₀ .r3) s U := kv rfl
  -- The table of `u`'s bits, from `K`'s slot.
  refine WP.seq (WP.mono_syms (tbl_bits_ok (secp256k1With_ok um) hs hf (i := K) (j := 0) (by decide) (by decide))
    fun u₂ ⟨b₂,k₂,O₂⟩ sy₂ => ?_)
  have hs₂ := hs.of_rest k₂ (by decide)
  have hf₂ := hf.of_rest k₂
  have F₂ := F.unch (secp256k1With_ok um).n10 hs.nowrap (W := [(bitsAt (secp256k1With um).n 0,64*(secp256k1With um).n)])
    (fun w hw => Or.inr (by rw [List.mem_singleton.mp hw]; exact Nat.le_of_ble_eq_true rfl)) O₂.unch
  have hu₂ := hu.of_frame (by rw [k₂.rd,k₂.wr]) (outside_frame O₂ (size := 8192) (Nat.le_of_ble_eq_true rfl))
    (by simpa only [List.mem_singleton,forall_eq] using hd)
  have bits : ∀ i<256,u₂.mem (off (ptr s₀ .r3) (bitsAt (secp256k1With um).n 0+i))=
      if (sv (secp256k1With um) (ptr s₀ .r3) s U).testBit i then 1 else 0 := fun i hi => by
    rw [b₂ i hi]
    simp only [sv] at k_eq
    rw [k_eq]
  have mul := comb_generator_ok hC hs₂ hf₂ F₂ hu₂ (by rw [sy₂,syu,syms]; rfl)
    (hd.sub_right (Region.sub_prefix (by decide))) (k := sv (secp256k1With um) (ptr s₀ .r3) s U)
    (VG.Proof.Mont.wordsVal_lt _ _ _ _) bits
  refine WP.mono mul fun t ⟨R,U',Mo,L,Rp⟩ => ⟨(k₂.mono (by decide)).trans R,
    (O₂.unch.trans U').mono fun w hw => ?_,Mo,L,by simpa only [Nat.shiftRight_zero] using Rp⟩
  rcases List.mem_append.mp hw with h|h
  · rw [List.mem_singleton.mp h]
    exact List.mem_append_right _ (by simp [genX])
  · exact h

theorem combVerify_ok (hC : Law Spec.Secp256k1.curve) {um : Bool} {s₀ : State} (hp : combVerifyPre um s₀) :
    WP isa (verifySecp256k1CombWith um) s₀ fun t => VKeep s₀ t ∧ VPost (secp256k1With um) s₀ t :=
  verifyWith_ok (secp256k1With_ok um) hC hp.1 (a0₁ := false) nofun (comb_generatorWP hC hp)

end VG.Proof.Ecdsa.Verify.Arm.Secp256k1
