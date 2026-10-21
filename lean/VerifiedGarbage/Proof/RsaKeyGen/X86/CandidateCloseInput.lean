module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateClose
public import VerifiedGarbage.Proof.RsaKeyGen.X86.NearScalar
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateClose
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateArrays
import VerifiedGarbage.Proof.MillerRabin.X86.Caller
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.X86.Syms

/-! # Optional-prime distance filtering retains the drawn candidate and input snapshots -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

theorem MemoryFacts.other_choice {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (M : MemoryFacts E eBytes pBytes entropy s) :
    (if BitVec.ofNat 32 E.otherLength = 0#32 then none else
      some (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (E.other.setWidth 64) (8 * E.width)))) = Spec.RsaKeyGen.otherPrime pBytes := by
  have pLength : pBytes.length = E.otherLength := by rw [← M.otherBytes]; exact VG.Proof.Bignum.bytesAt_length _ _ _
  have lengthBound : E.otherLength < 2 ^ 32 := by
    have prime := v.length; unfold Spec.RsaKeyGen.primeLenValid at prime
    have := v.otherLength; omega
  by_cases empty : E.otherLength = 0
  · have pEmpty : pBytes = [] := List.length_eq_zero_iff.mp (by rw [pLength, empty])
    rw [empty, pEmpty]
    rfl
  · have lengthEq : E.otherLength = E.length := v.otherLength.resolve_left empty
    have pNonempty : pBytes ≠ [] := by intro nil; rw [nil] at pLength; exact empty pLength.symm
    have nativeNonzero : BitVec.ofNat 32 E.otherLength ≠ 0#32 := by
      intro zero
      have H := congrArg BitVec.toNat zero
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthBound] at H
      exact empty H
    simp only [nativeNonzero, ↓reduceIte, Spec.RsaKeyGen.otherPrime, pNonempty]
    rw [v.length_eq, ← lengthEq, M.otherBytes]

theorem close_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateClose.code E.width) s fun t =>
      Drawn E eBytes pBytes entropy t ∧
      t.gpr .eax = Near.bit (Spec.RsaKeyGen.tooClose (8 * E.length)
        (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E entropy)) ∧
      WorkFrame E s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  have length := v.length_eq
  have otherLength : E.otherLength < 2 ^ 32 := by
    have prime := v.length; unfold Spec.RsaKeyGen.primeLenValid at prime
    have := v.otherLength; omega
  refine WP.mono_syms (CandidateClose.code_ok D.input.scratch v.width_bounds.1 (by omega)
    (v.slotFit (by decide : 4 < 28)) D.candidate D.input.other_eq (D.input.header 6 (by decide)) ?_)
    fun t ⟨result, O, K⟩ syms => ?_
  · intro nonzero
    have positive : E.otherLength ≠ 0 := by intro zero; apply nonzero; change BitVec.ofNat 32 E.otherLength = 0#32; rw [zero]
    have eqLength := v.otherLength.resolve_left positive
    refine ⟨by have := v.otherFit; omega, ?_, ?_⟩
    · have read := D.input.memory.otherRead
      rw [eqLength, ← length] at read
      exact read
    · have far := v.readWorkspace (r := E.otherRegion) (List.mem_cons_of_mem _ List.mem_cons_self)
      change (⟨E.other.setWidth 64, E.otherLength⟩ : Region).Disjoint E.workspaceRegion at far
      rw [eqLength, ← length] at far
      exact far
  · change t.gpr .eax = Near.bit (Spec.RsaKeyGen.tooClose (64 * E.width)
      (if BitVec.ofNat 32 E.otherLength = 0#32 then none else
        some (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (E.other.setWidth 64) (8 * E.width))))
      (candidateValue E entropy)) at result
    rw [D.input.memory.other_choice v, show 64 * E.width = 8 * E.length by omega] at result
    have W : WorkspaceFrame E.geometry [(slot E.width 4, 8 * E.width), (slot E.width 2, 8 * E.width), (slot E.width 3, 8 * E.width)] s.mem t.mem :=
      WorkspaceFrame.of_outs D.input.scratch.nowrap O
    have workspace : Frame [E.workspaceRegion] s.mem t.mem := workspaceGlobalFrame (g := E.geometry) O (by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · exact v.slotFit (by decide : 4 < 28)
      · exact v.slotFit (by decide : 2 < 28)
      · exact v.slotFit (by decide : 3 < 28))
    have frame : WorkFrame E s.mem t.mem := workspace.mono (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact List.mem_cons_self)
    have headerFar : ∀ r ∈ [(slot E.width 4, 8 * E.width), (slot E.width 2, 8 * E.width), (slot E.width 3, 8 * E.width)], 256 ≤ r.1 := by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · exact E.slotHeader 4
      · exact E.slotHeader 2
      · exact E.slotHeader 3
    have I := D.input.keepWorkspace v K (by decide) (by decide) frame W
      (fun r mem => Nat.le_trans (by decide) (headerFar r mem)) (by rw [syms])
    refine ⟨⟨I, ?_, ?_, (frame.output v).trans D.zeros⟩, result, frame, K⟩
    · have same := W.val32 (d := slot E.width 0) (n := 2 * E.width) (by change slot E.width 0 + 4 * (2 * E.width) ≤ E.size; have := v.slotFit (j := 0) (by decide); omega) (by
        intro r mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl
        · exact Or.inl (by have := E.slotBefore (i := 0) (j := 4) (by decide); omega)
        · exact Or.inl (by have := E.slotBefore (i := 0) (j := 2) (by decide); omega)
        · exact Or.inl (by have := E.slotBefore (i := 0) (j := 3) (by decide); omega))
      exact same.trans D.candidate
    · have same := W.read32 (d := 152) (by change 152 + 4 ≤ E.size; omega)
        (fun r mem => Or.inl (by have := headerFar r mem; omega))
      exact (congrArg BitVec.toNat same).trans D.used

end VG.Proof.RsaKeyGen.X86.Candidate
