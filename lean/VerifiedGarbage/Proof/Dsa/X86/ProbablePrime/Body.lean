module

public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Test
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Enter
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Width
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Load
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Sieve
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinish
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-! # Trial division, then the blinded loop -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86
open VG.Impl.Dsa.X86.ProbablePrime

theorem used_tail {E : Environment} (v : E.Valid) {m m' : Mem} (F : Frame [E.usedRegion] m m') :
    Tail E m m' := by
  intro i _ hi
  apply F
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  intro contains
  have fit := v.workspaceFit
  exact v.usedWorkspace _ contains (Offset.contains_base E.base (by omega) (by omega))

theorem sieved_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (L : Loaded E c entropy s) (odd : c % 2 = 1) (length : Spec.Dsa.bitLength c = E.bits) :
    WP isa (sieved E.bits montName mont roundName round) s fun t =>
      Outputs E (Spec.Dsa.probablePrime c entropy) t ∧ MutableFrame E s.mem t.mem ∧ Tail E s.mem t.mem ∧
      Keeps WitnessStep.clob s t := by
  have shape := candidate_shape odd length (by have := v.bits.low; omega)
  have big : 2 ^ 63 ≤ 2 ^ (E.bits - 1) := Nat.pow_le_pow_right (by decide) (by have := v.bits.low; omega)
  unfold sieved
  refine WP.seq (WP.mono (sieve_ok v L (by omega)) fun a ⟨La, flag, Wa, Ta, Ka⟩ => ?_)
  refine WP.seq (WP.mono (Candidate.cmp_bool flag) fun b ⟨B, _, cond⟩ => ?_)
  obtain ⟨Lb, Wb, Tb⟩ := La.keepStack v (by rw [B.mem]; exact Frame.refl _ _) (B.keeps []) (by decide) (by decide)
    (by rw [B.syms])
  have Kb : Keeps WitnessStep.clob s b := (Ka.mono (by unfold WitnessStep.clob; decide)).widen (B.keeps [])
  have Mb : MutableFrame E s.mem b.mem := (Wa.trans Wb).mutable
  have Tsb : Tail E s.mem b.mem := Ta.trans Tb
  have same : Spec.RsaKeyGen.obviouslyComposite (64 * E.width) c = Spec.RsaKeyGen.obviouslyComposite E.bits c :=
    obviouslyComposite_eq v.bits c
  rw [same] at cond
  cases composite : Spec.RsaKeyGen.obviouslyComposite E.bits c
  · refine WP.ite false (by rw [cond, composite]) (fun bad => nomatch bad) (fun _ => ?_)
    refine WP.mono (test_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Lb odd length)
      fun t ⟨out, Mt, Tt, Kt⟩ => ?_
    rw [← probablePrime_eq v entropy odd length composite] at out
    exact ⟨out, Mb.trans Mt, Tsb.trans Tt, Kb.trans Kt⟩
  · refine WP.ite true (by rw [cond, composite]) (fun _ => ?_) (fun bad => nomatch bad)
    have result : Spec.Dsa.probablePrime c entropy = some (false, entropy) := by
      have three : (c == 3) = false := by rw [beq_eq_false_iff_ne]; omega
      unfold Spec.Dsa.probablePrime
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by rw [three]; decide), length,
        composite]
      rfl
    refine WP.mono (CandidateFinish.used_ok (status := 2) Lb.input.scratch (by have := v.header; omega)
      Lb.input.memory.usedWrite Lb.input.usedPtr rfl) fun t ⟨eax, mem, O, Kt⟩ => ?_
    have F := used_frame O
    refine ⟨⟨?_, ?_⟩, Mb.trans (MutableFrame.of_used F), Tsb.trans (used_tail v F),
      Kb.trans (Kt.mono (by decide))⟩
    · rw [eax, result]; rfl
    · rw [mem]
      refine used_outputs (fun _ rest same => ?_)
      rw [result] at same
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      rw [L.input.memory.entropyLength, Nat.sub_self]
      change w32 b.mem E.base 152 = 0
      exact Lb.count

def bodyClob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi]

theorem body_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (I : EntryInput E c entropy s) (odd : c % 2 = 1) (length : Spec.Dsa.bitLength c = E.bits) :
    WP isa (body E.bits montName mont roundName round) s fun t =>
      Outputs E (Spec.Dsa.probablePrime c entropy) t ∧ MutableFrame E s.mem t.mem ∧ Tail E s.mem t.mem ∧
      Keeps bodyClob s t := by
  unfold body
  refine WP.seq (WP.mono (enter_ok v I) fun a ⟨Ia, count, O, Ka⟩ => ?_)
  have Wa := v.work_of_outside O (by have := v.header; omega)
  have Ta := v.tail_of_outside O (by have := v.scratchLow; omega)
  refine WP.seq (WP.mono (load_ok v Ia count odd) fun b ⟨Lb, Wb, Tb, Kb⟩ => ?_)
  refine WP.mono (sieved_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Lb odd length)
    fun t ⟨out, Mt, Tt, Kt⟩ => ?_
  exact ⟨out, (Wa.trans Wb).mutable.trans Mt, (Ta.trans Tb).trans Tt,
    ((Ka.mono (by unfold bodyClob; decide)).trans (Kb.mono (by unfold bodyClob; decide))).trans
      (Kt.mono (by unfold WitnessStep.clob bodyClob; decide))⟩

end VG.Proof.Dsa.X86.ProbablePrime
