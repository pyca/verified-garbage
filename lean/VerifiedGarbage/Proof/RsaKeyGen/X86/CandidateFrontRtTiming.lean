module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveStageTiming
public import VerifiedGarbage.Impl.RsaKeyGen.X86.FrontRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSchedule
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFrontRt
import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.LoadTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.CloseTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.SieveTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveLeak
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateArrays
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDispatchTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoopTiming

/-! # The candidate drawn and filtered at its run-time width hides the filtered values -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen

structure ClearedPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop
    extends InputPair E eBytes pBytes qBytes rBytes sBytes s t where
  zerosLeft : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0
  zerosRight : Spec.Rsa.bytesAt t.mem (E.out.setWidth 64) E.length = List.replicate E.length 0

theorem load_rt_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (enough : E.length ≤ E.randLength) :
    RelCT isa (ClearedPair E eBytes pBytes qBytes rBytes sBytes) VG.Impl.RsaKeyGen.X86.FrontRt.load
      (DrawnPair E eBytes pBytes qBytes rBytes sBytes) := by
  intro s t tr ur u z P A B
  have five := v.slotFit (j := 5) (by decide)
  have trace := (FrontRt.load_trace v.width_bounds.1 (by omega) _ _ _ _ _ _
    ⟨P.left.loadIn v enough, P.right.loadIn v enough⟩ A B).1
  obtain ⟨DU, _, _⟩ := wp_result (load_rt_ok v P.left P.zerosLeft enough) A
  obtain ⟨DZ, _, _⟩ := wp_result (load_rt_ok v P.right P.zerosRight enough) B
  exact ⟨trace, DU, DZ⟩

theorem close_rt_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (same : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) =
      Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes)) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes) VG.Impl.RsaKeyGen.X86.FrontRt.close
      (WithFlag (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
        (Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes))) := by
  intro s t tr ur u z P A B
  have five := v.slotFit (j := 5) (by decide)
  have trace := (FrontRt.close_trace v.width_bounds.1 v.width_bounds.2 (by omega) (by have := v.low; omega)
    v.stackApart _ _ _ _ _ _ ⟨P.left.closeIn v, P.right.closeIn v⟩ A B).1
  obtain ⟨DU, flagU, _, _⟩ := wp_result (close_rt_ok v P.left) A
  obtain ⟨DZ, flagZ, _, _⟩ := wp_result (close_rt_ok v P.right) B
  exact ⟨trace, ⟨DU, DZ⟩, flagU, by rw [same]; exact flagZ⟩

theorem sieve_rt_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (pattern : Sieve.SamePattern E.sieveGeometry (candidateValue E rBytes) (candidateValue E sBytes))
    (same : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) =
      Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes)) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes) VG.Impl.RsaKeyGen.X86.FrontRt.sieve
      (WithFlag (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
        (Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes))) := by
  have privateSub : (below E.sieveGeometry.sp 4).Sub (below E.p 136) := below_inner (by decide) v.low
  have workspaceFar : E.workspaceRegion.Disjoint (below E.p 136) := v.stackFar E.workspaceRegion
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have tableFar : E.tableRegion.Disjoint (below E.p 136) := v.stackFar E.tableRegion
    (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  intro s t tr ur u z P A B
  have trace := (FrontRt.sieve_trace v.sieve_valid pattern rfl
    (by change 4 ≤ (E.p - 20#32).toNat; rw [sub_toNat (by have := v.low; omega)]; have := v.low; omega)
    ((workspaceFar.sub_left v.sieveCandidateSub).sub_right privateSub) (tableFar.sub_right privateSub)
    _ _ _ _ _ _ ⟨P.left.sieveIn v, P.right.sieveIn v⟩ A B).1
  obtain ⟨DU, flagU, _, _⟩ := wp_result (sieve_rt_ok v P.left) A
  obtain ⟨DZ, flagZ, _, _⟩ := wp_result (sieve_rt_ok v P.right) B
  exact ⟨trace, ⟨DU, DZ⟩, flagU, by rw [same]; exact flagZ⟩

theorem sieve_front_rt_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (rEnough : E.length ≤ rBytes.length)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes)
    (rClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) = false)
    (sClose : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) = false) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      (.seq VG.Impl.RsaKeyGen.X86.FrontRt.sieve (.seq (.block [.alu .cmp .eax (.imm 0)])
        (.ite .ne (VG.Impl.RsaKeyGen.X86.CandidateFinish.used 3) (.block [.mov .eax (.imm 4)]))))
      (FrontPair E eBytes pBytes qBytes rBytes sBytes) := by
  have schedules := schedule_eq v length rEnough leak
  have same : Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E rBytes) =
      Spec.RsaKeyGen.obviouslyComposite (8 * E.length) (candidateValue E sBytes) := by
    have H := congrArg Sched.comp schedules
    rw [schedule_composite rClose, schedule_composite sClose] at H
    exact H
  have pattern := sieve_pattern v rEnough (by rw [← length]; exact rEnough) leak rClose sClose same
  have initialTrace := sieve_rt_pair_trace (eBytes := eBytes) (pBytes := pBytes) (qBytes := qBytes) v pattern same
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

theorem front_rt_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (rEnough : E.length ≤ rBytes.length) (enough : E.length ≤ E.randLength)
    (leak : SameLeak E eBytes pBytes qBytes rBytes sBytes) :
    RelCT isa (ClearedPair E eBytes pBytes qBytes rBytes sBytes)
      VG.Impl.RsaKeyGen.X86.FrontRt.code (FrontPair E eBytes pBytes qBytes rBytes sBytes) := by
  have schedules := schedule_eq v length rEnough leak
  have same : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes) =
      Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime qBytes) (candidateValue E sBytes) := by
    have H := congrArg Sched.close schedules
    rw [schedule_close, schedule_close] at H
    exact H
  have initialTrace := close_rt_pair_trace (eBytes := eBytes) v same
  unfold VG.Impl.RsaKeyGen.X86.FrontRt.code
  refine RelCT.seq (load_rt_pair_trace v enough) ?_
  cases close : Spec.RsaKeyGen.tooClose (8 * E.length) (Spec.RsaKeyGen.otherPrime pBytes) (candidateValue E rBytes)
  · rw [close] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace false (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.2)) ?_)
    exact branch_false (sieve_front_rt_trace v length rEnough leak close (same.symm.trans close))
  · rw [close] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace true (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.2)) ?_)
    exact branch_true (drawn_done_trace v 2 (by decide))

end VG.Proof.RsaKeyGen.X86.Candidate
