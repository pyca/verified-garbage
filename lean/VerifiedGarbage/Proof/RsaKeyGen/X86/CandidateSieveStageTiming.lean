module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentStageTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveLeak
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateScheduleContinue
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFilterTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishReady
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingBranch
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSchedule
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveGeometry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoopTiming

/-! # The shared leak controls sieve rejection and the complete remaining candidate path -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen

theorem sieve_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (pattern : Sieve.SamePattern E.sieveGeometry (candidateValue E rBytes) (candidateValue E sBytes))
    (same : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) =
      Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes)) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.CandidateSieve.code E.width)
      (WithFlag (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
        (Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes))) := by
  intro s t tr ur u z P A B
  have trace := (sieve_trace v pattern _ _ _ _ _ _ P A B).1
  obtain ⟨DU, flagU, _, _⟩ := wp_result (sieve_ok v P.left) A
  obtain ⟨DZ, flagZ, _, _⟩ := wp_result (sieve_ok v P.right) B
  exact ⟨trace, ⟨DU, DZ⟩, flagU, by rw [same]; exact flagZ⟩

/-- After the code for the width: both runs wrote the same status, or both go
on with `eax = 4`, the drawn candidates neither too close nor divisible. -/
def FrontPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop :=
  (s.gpr .eax = t.gpr .eax ∧ s.gpr .eax ≠ 4) ∨
  (s.gpr .eax = 4 ∧ t.gpr .eax = 4 ∧ DrawnPair E eBytes pBytes qBytes rBytes sBytes s t ∧
    Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) = false ∧
    Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) = false ∧
    Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) = false ∧
    Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes) = false)

/-- A status written by both runs. -/
theorem drawn_done_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (status : Nat) (small : status < 4) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.CandidateFinish.used status) (FrontPair E eBytes pBytes qBytes rBytes sBytes) := by
  refine ((drawn_used_trace v status).wp (F₁ := fun (u : State) => u.gpr .eax = BitVec.ofNat 32 status)
    (F₂ := fun (u : State) => u.gpr .eax = BitVec.ofNat 32 status) fun s t P =>
    ⟨WP.mono (finish_used_ok (status := status) v (P.left.finishReady v)) fun _ H => H.1.1,
      WP.mono (finish_used_ok (status := status) v (P.right.finishReady v)) fun _ H => H.1.1⟩).mono
    (fun _ _ P => P) ?_
  rintro u z ⟨_, U, Z⟩
  refine Or.inl ⟨U.trans Z.symm, ?_⟩
  rw [U]
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega)] at this
  change status = 4 at this
  omega

theorem sieve_front_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (rEnough : E.length ≤ rBytes.length)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes)
    (rClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) = false)
    (sClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) = false) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      (.seq (VG.Impl.RsaKeyGen.X86.CandidateSieve.code E.width) (.seq (.block [.alu .cmp .eax (.imm 0)])
        (.ite .ne (VG.Impl.RsaKeyGen.X86.CandidateFinish.used 3) (.block [.mov .eax (.imm 4)]))))
      (FrontPair E eBytes pBytes qBytes rBytes sBytes) := by
  have schedules := schedule_eq v length rEnough leak
  have same : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) =
      Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes) := by
    have H := congrArg Sched.comp schedules
    rw [schedule_composite rClose, schedule_composite sClose] at H
    exact H
  have pattern := sieve_pattern v rEnough (by rw [← length]; exact rEnough) leak rClose sClose same
  have initialTrace := sieve_pair_trace (eBytes := eBytes) (pBytes := pBytes) (qBytes := qBytes) v pattern same
  cases composite : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes)
  · have right := same.symm.trans composite
    rw [composite] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace false (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.2)) (branch_false ?_))
    have raw : RelCT isa (VG.X86.Taint.Agree (τr [])) (.block [.mov .eax (.imm 4)]) (VG.X86.Taint.Agree (τr [])) :=
      checkedBlockInvariant rfl rfl
    have four {e p r : List Byte} {x : State} (D : Drawn E e p r x) :
        WP isa (.block [.mov .eax (.imm 4)]) x fun u => u.gpr .eax = 4 ∧ Drawn E e p r u :=
      wp_movS rfl fun u U _ => WP.block_nil ⟨U.gpr, D.keepMem v U.mem U.keeps (by decide) (by decide) U.syms⟩
    refine ((raw.mono (fun _ _ _ => agree_regs (by intro r mem; cases mem)) (fun _ _ _ => trivial)).wp
      (fun _ _ P => ⟨four P.left, four P.right⟩)).mono (fun _ _ P => P) ?_
    rintro u z ⟨_, ⟨U, DU⟩, ⟨Z, DZ⟩⟩
    exact Or.inr ⟨U, Z, ⟨DU, DZ⟩, rClose, sClose, composite, right⟩
  · rw [composite] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace true (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.2)) ?_)
    exact branch_true (drawn_done_trace v 3 (by decide))

end VG.Proof.RsaKeyGen.X86.Candidate
