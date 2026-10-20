module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleHead
public import VerifiedGarbage.Impl.Dsa.X86.Generation.SampleWitness
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleHeadCT

/-! # Forced sampling branches only on the public draw's range -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def SampleAt (len : Nat) (p : PrimeConfig × Nat) (s : State) : Prop :=
  p.1.len = len ∧ PrimeReady p.1 s ∧ s.gpr .esi = p.1.witness ∧
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.1.witness.setWidth 64) len) = p.2

def SampleBranchAt (p : PrimeConfig × Nat) (s : State) : Prop :=
  (s.gpr .edi).toNat = p.1.base.toNat ∧ s.gpr .esi = p.1.witness ∧
    s.zf = some (decide (¬ (2 ≤ p.2 ∧ p.2 < p.1.modulus - 1)))

theorem sampleClassify_ct (len : Nat) :
    RelCT isa (Two (SampleAt len)) (sampleHead len) (Two SampleBranchAt) := by
  refine two_post ((sampleHead_ct len).mono ?_ (fun _ _ h => h)) ?_
  · rintro s t ⟨p, hs, ht⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (hs.2.1.context.scr.edi_toNat.trans ht.2.1.context.scr.edi_toNat.symm)
    · exact hs.2.2.1.trans ht.2.2.1.symm
  · rintro p s ⟨hl, R, si, value⟩
    rw [← hl] at value ⊢
    refine WP.mono (sampleHead_ok R.context p.1.width p.1.flagRoom R.one rfl p.1.lenMin p.1.lenWords
      (by rw [si]; exact p.1.witnessFit) (fun d hd => by rw [si]; exact R.witnessRead d hd)
      (by rw [si]; exact p.1.witnessScratch)) fun t ⟨C, _, _, zf, _, _, K⟩ => ?_
    rw [si, value] at zf
    exact ⟨C.scr.edi_toNat, (K.1 _ (by decide)).trans si, zf⟩

theorem sampleWitness_ct (len : Nat) :
    RelCT isa (Two (SampleAt len)) (sampleWitness len) (fun _ _ => True) := by
  unfold sampleWitness
  refine RelCT.seq (sampleClassify_ct len) ?_
  apply two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2.2, ht.2.2])
  · refine (forceSample_ct len).mono ?_ (fun _ _ h => h)
    rintro s t ⟨p, hs, ht⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (hs.1.1.trans ht.1.1.symm)
    · exact hs.1.2.1.trans ht.1.2.1.symm
  · exact RelCT.nil (fun _ _ _ => trivial)
end VG.Proof.Dsa.X86.Generation
