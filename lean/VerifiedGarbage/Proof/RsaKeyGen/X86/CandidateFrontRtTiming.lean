module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.FrontRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSchedule
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveGeometry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDispatchTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoopTiming
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateFinish
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.TCB.X86.Isa

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFrontRt
import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.LoadTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.CloseTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveLeak
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateArrays
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentStageTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishReady
import VerifiedGarbage.Proof.RsaKeyGen.X86.FrontRt.Sieve
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.TimingSeg
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
/-! # The candidate drawn and filtered at its run-time width hides the filtered values -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateSieveStageTiming.lean`, which only this module imported.
section

/-! # The shared leak controls sieve rejection and the complete remaining candidate path -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen

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

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/FrontRt/SieveTiming.lean`, which only this module imported.
section

/-! # Trial division at the run-time width releases only the trial divisors' pattern -/

section
namespace VG.Proof.RsaKeyGen.X86.FrontRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen.X86.Sieve
open VG.Impl.RsaKeyGen.X86.FrontRt
open VG.Impl.RsaKeyGen.X86.Sieve (tableCount tableAddress stackSlots)

theorem enter_ok {g : Geometry} {c : Nat} {s : State} (S : SieveIn g c s) :
    WP isa (.block [.mov .edx (.mem (VG.Impl.Mont.X86.sc 4)), .alu .add .edi (.imm 256)]) s (BodyIn g c) := by
  obtain ⟨C, pointer, symbol, lenRead⟩ := S
  refine wp_movS lenRead fun a A _ => wp_addS rfl fun b B _ => WP.block_nil ?_
  have Kb : Keeps [.edx, .edi] s b := (A.keeps.mono (by decide)).widen B.keeps
  have Mb : b.mem = s.mem := B.mem.trans A.mem
  refine ⟨⟨C.stack.keep Kb (by decide), ?_, ?_, ?_, ?_⟩, by rw [B.gpr, A.other .edi (by decide)]; exact pointer,
    by rw [B.other .edx (by decide), A.gpr], by rw [B.syms, A.syms]; exact symbol⟩
  · intro i index; rw [Kb.2.1, Kb.2.2]; exact C.candidateRead i index
  · intro i index d mem; rw [Kb.2.1, Kb.2.2]; exact C.tableRead i index d mem
  · intro i index; rw [Mb]; exact C.tableWords i index
  · rw [Mb]; exact C.candidateValue

theorem enter_trace {g : Geometry} {c d : Nat} :
    RelCT isa (fun s t => SieveIn g c s ∧ SieveIn g d t)
      (.block [.mov .edx (.mem (VG.Impl.Mont.X86.sc 4)), .alu .add .edi (.imm 256)])
      (fun u z => BodyIn g c u ∧ BodyIn g d z) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have A : VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
    apply agree_regs
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact S.1.stack.sp.trans T.1.stack.sp.symm
    · have H := congrArg (fun x : BitVec 32 => x - 256#32) (S.2.1.trans T.2.1.symm)
      simpa only [BitVec.add_sub_cancel] using H
  exact ⟨((rawBlock (rs := [.esp, .edi]) (by decide +kernel)) _ _ _ _ _ _ A E G).1,
    wp_result (enter_ok S) E, wp_result (enter_ok T) G⟩

theorem setup_trace {g : Geometry} (v : g.Valid) {c d : Nat} (low : 4 ≤ g.sp.toNat)
    (length : g.limit = tableCount g.w) (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    RelCT isa (fun s t => BodyIn g c s ∧ BodyIn g d t)
      (.seq (.block candidateSlots) (.seq tableAddress (.block tableSlots)))
      (fun s t => StateAt g c 0 g.limit s ∧ StateAt g d 0 g.limit t) := by
  have first : RelCT isa (fun s t => BodyIn g c s ∧ BodyIn g d t) (.block candidateSlots)
      (fun s t => s.gpr .esp = g.sp ∧ t.gpr .esp = g.sp) := by
    intro s t tr ur u z ⟨S, T⟩ E G
    have A : VG.X86.Taint.Agree (τr [.esp]) s t :=
      agree_regs (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact S.1.stack.sp.trans T.1.stack.sp.symm)
    have trace := ((rawBlock (rs := [.esp]) (code := candidateSlots) (by decide +kernel)) _ _ _ _ _ _ A E G).1
    have U := wp_result (candidateSlots_ok v S.1 S.2.1 S.2.2.1) E
    have Z := wp_result (candidateSlots_ok v T.1 T.2.1 T.2.2.1) G
    exact ⟨trace, U.1.context.stack.sp, Z.1.context.stack.sp⟩
  have middle : RelCT isa (fun s t => s.gpr .esp = g.sp ∧ t.gpr .esp = g.sp)
      tableAddress (VG.X86.Taint.Agree (τr [.esp])) := by
    intro s t tr ur u z ⟨S, T⟩ E G
    have Ls : 4 ≤ (s.gpr .esp).toNat := by rw [S]; exact low
    have Lt : 4 ≤ (t.gpr .esp).toNat := by rw [T]; exact low
    have U := wp_result (symFrame_ok VG.Impl.RsaKeyGen.TrialTable32.symbol s Ls) E
    have Z := wp_result (symFrame_ok VG.Impl.RsaKeyGen.TrialTable32.symbol t Lt) G
    refine ⟨?_, agree_regs (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact
      (U.gpr .esp (by decide)).trans (S.trans (T.symm.trans (Z.gpr .esp (by decide)).symm)))⟩
    rw [symFrame_trace Ls E, symFrame_trace Lt G, S, T]
  have raw : RelCT isa (fun s t => BodyIn g c s ∧ BodyIn g d t)
      (.seq (.block candidateSlots) (.seq tableAddress (.block tableSlots))) (fun _ _ => True) :=
    RelCT.seq first (RelCT.seq middle (rawBlock (by decide +kernel)))
  intro s t tr ur u z ⟨S, T⟩ E G
  exact ⟨(raw _ _ _ _ _ _ ⟨S, T⟩ E G).1,
    (wp_result (setup_ok v S.1 S.2.1 S.2.2.1 length S.2.2.2 low candidateFar tableFar) E).1,
    (wp_result (setup_ok v T.1 T.2.1 T.2.2.1 length T.2.2.2 low candidateFar tableFar) G).1⟩

theorem body_trace {g : Geometry} (v : g.Valid) {c d : Nat} (pattern : SamePattern g c d)
    (length : g.limit = tableCount g.w) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    RelCT isa (fun s t => BodyIn g c s ∧ BodyIn g d t) sieveBody (VG.X86.Taint.Agree (τr [.esp])) := by
  have setup := setup_trace (c := c) (d := d) v low length candidateFar tableFar
  intro s t tr ur u z H E G
  cases E with
  | seq A E =>
    cases E with
    | seq B E =>
      cases E with
      | seq C L =>
        cases G with
        | seq D G =>
          cases G with
          | seq F G =>
            cases G with
            | seq K N =>
              have R := RelCT.seq setup (loop_trace v pattern) _ _ _ _ _ _ H
                (.seq (.seq A (.seq B C)) L) (.seq (.seq D (.seq F K)) N)
              simpa only [List.append_assoc] using R

theorem sieve_trace {g : Geometry} (v : g.Valid) {c d : Nat} (pattern : SamePattern g c d)
    (length : g.limit = tableCount g.w) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    RelCT isa (fun s t => SieveIn g c (allocFrame 20 s) ∧ SieveIn g d (allocFrame 20 t)) sieve (fun _ _ => True) := by
  unfold sieve
  apply RelCT.frameAlloc
  refine (RelCT.seq enter_trace (RelCT.seq (body_trace v pattern length low candidateFar tableFar)
    (rawBlock (by decide +kernel)))).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, H, rfl, rfl⟩
  exact H

end VG.Proof.RsaKeyGen.X86.FrontRt
end

end

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
