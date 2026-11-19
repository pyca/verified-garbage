module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Impl.Ffdh.AArch64.ParameterCandidate
public import VerifiedGarbage.Impl.Ffdh.AArch64.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Writes
public import VerifiedGarbage.Spec.Ffdh.SievedContract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTCode
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Loop
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Loop
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Ffdh.Contract
meta import VerifiedGarbage.Proof.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Writes
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
import VerifiedGarbage.Proof.Ffdh.SievedBounds
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
meta import VerifiedGarbage.Proof.Ffdh.SievedBounds
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Generation.Search
meta import VerifiedGarbage.Proof.Ffdh.ControlMemory

/-! ### `Ffdh.AArch64.Generation.Search.CTCode`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Generation.Search.Correct`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Generation.Search.Entry`, which this module and modules that import it used -/

section

/-! # The parameter search's entry (AArch64)

The stack arguments are loaded, the caller's `x19` saved in word 4 and the
arguments stored in the controller's words; then, in the frame saving
`x30`, the controller is at the tape's start with its attempts
(`search_start`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Spec.Ffdh
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.Control (writeController writeController_frame writeController_word
  controllerValue)
open VG.Impl.Ffdh.AArch64.Generation.Search

def entryValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .x19), (5, s.gpr .x0), (6, s.gpr .x1), (7, s.gpr .x2), (8, s.gpr .x3),
    (9, BitVec.ofNat 64 (genGen s)), (10, s.gpr .x5), (11, s.gpr .x6), (12, 0), (13, s.gpr .x7),
    (15, stackArg s 0)]

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 16 := by
  simp only [entryValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem input_args {p : SPub} {s : State} (h : SInput p s) (j : Nat) (hj : j < 2) :
    InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * j)) 8 := by
  refine ⟨inArgs s, ?_, ?_⟩
  · rw [h.1.2.2.1]
    exact List.mem_append_left _ (by simp [inReads])
  · simp only [inArgs, stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-- The stack arguments and the generator, before the stores. -/
abbrev entryRegs : List Reg := [.x4, .x8, .x9, .x13, .x14, .x19]

theorem entry_ok {p : SPub} {s : State} (h : SInput p s) :
    WP isa (.block entry) s fun t =>
      (t.gpr .x19 = p.control ∧ t.mem = writeController s.mem p.control (entryValues s)) ∧
      Keep entryRegs s t := by
  have scr := h.control_scr (t := s) rfl
  have hd : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = p.control :=
    congrArg SPub.control h.2
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have ha0 : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa only [Nat.mul_zero, BitVec.add_zero] using input_args h 0 (by decide)
  have ha1 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 := input_args h 1 (by decide)
  refine WP.keep entryRegs ?_ (by decide) (by decide) (by decide +kernel)
  unfold entry writeController entryValues
  simp only [List.foldl_cons, List.foldl_nil]
  brun [ldf, stf, exec_addSp (show 0 < 4096 by decide), imm64 (show 0 < 65536 by decide),
    VG.Proof.RsaKeyGen.AArch64.exec_addImm_w (show 0 < 4096 by decide), zext32, hd, ha0, ha1,
    hs 32 (by decide), hs 40 (by decide), hs 48 (by decide), hs 56 (by decide), hs 64 (by decide),
    hs 72 (by decide), hs 80 (by decide), hs 88 (by decide), hs 96 (by decide), hs 104 (by decide),
    hs 120 (by decide)]
  simp only [stackArg, stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  rfl

/-- The state the body of the frame saving `x30` starts in (`WP.frameReg`). -/
abbrev pushedX30 (t : State) : State :=
  { t with sp := t.sp - 16, mem := t.mem.write (t.sp - 16) 8 (t.gpr .x30) }

private theorem word_zero (m : Mem) (B : Addr) : word m B 0 = m.readW B 64 := by
  simp only [Bignum.word, off, BitVec.add_zero]

theorem entry_headers {p : SPub} {s : State} (h : SInput p s) :
    Slots (writeController s.mem p.control (entryValues s)) p.control (p.headers 0 p.attempts) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hw1, hw2, -⟩ := h.1
  cases h.2
  intro e he
  simp only [SPub.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [writeController_word _ _ _ (entryValues_bound s) _ (by dsimp only; decide)] <;>
    simp only [sOfState, controllerValue, entryValues,
      List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ite_true, ite_false,
      Nat.sub_zero, Nat.mul_zero, BitVec.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      Nat.mul_div_cancel _ (by decide : 0 < 8), word_zero]
  · simp only [Bignum.word, off, Nat.reduceMul]
    exact hw1.trans (by simp only [genLen, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  · simp only [Bignum.word, off, Nat.reduceMul]
    exact hw2
  all_goals rfl

/-- The push of `x30` writes only below the stack pointer. -/
theorem push_frame {p : SPub} {s : State} (h : SInput p s) (m : Mem) (v : BitVec 64) :
    Frame (SInput.callChanges s) m (m.write (s.sp - 16) 8 v) := by
  refine Frame.write (Frame.refl _ _) (r := below s.sp stackUse)
    (by simp [SInput.callChanges]) _ ?_
  have := h.1.2.1
  exact Offset.contains_below s.sp (a := 16) (b := 32) (by decide) (by decide) (by decide)

theorem search_start {p : SPub} {s t : State} (h : SInput p s)
    (hx : t.gpr .x19 = p.control) (hm : t.mem = writeController s.mem p.control (entryValues s))
    (k : Keep entryRegs s t) :
    SLive p s 0 p.attempts (pushedX30 t) := by
  have hf := writeController_frame s.mem p.control (entryValues s) (entryValues_bound s)
  have hf₁ : Frame (SInput.changes s) s.mem t.mem := by
    rw [hm]
    exact hf.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨inCtl s, by simp [SInput.changes, inWrites], by rw [h.ctl_eq]; exact fun _ hi => hi⟩
  have hp := push_frame h t.mem (t.gpr .x30)
  rw [← k.sp] at hp
  have hf₂ : Frame (SInput.changes s) s.mem (pushedX30 t).mem :=
    hf₁.trans (frame_of_callChanges s hp)
  have hc (j : Nat) (hj : j < 16) : word (pushedX30 t).mem p.control (8 * j) = word t.mem p.control (8 * j) :=
    h.control_frame hp j hj
  refine ⟨h, Nat.zero_le _, Nat.le_refl _, k.rd, k.wr, ?_, hx, ?_, k.vcs, ?_, ?_, ?_⟩
  · show t.sp - 16 = p.sp - 16
    rw [k.sp, h.sp_eq]
  · intro r hr h19 _
    exact k.gpr r (by revert r hr h19; decide)
  · rw [show (32 : Nat) = 8 * 4 from rfl, hc 4 (by decide), hm,
      writeController_word _ _ _ (entryValues_bound s) 4 (by decide)]
    rfl
  · rw [h.random_frame hf₂]
    cases h.2
    rfl
  · intro e he
    rw [hc e.1 (SPub.headers_index he), hm]
    exact entry_headers h e he

end VG.Proof.Ffdh.AArch64.Generation

end

end

/-! # The parameter search's correctness (AArch64)

The loop runs in the frame saving `x30` (`WP.frameReg`); `finish` then
stores the octets consumed, returns the status and restores `x19`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Spec.Ffdh
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Ffdh.AArch64.Generation.Search

/-! ## Returning -/

theorem SInput.used_scr {p : SPub} {s : State} (h : SInput p s) {t : State}
    (hw : t.wr = s.wr) : Scr t p.up 8 := by
  refine Scr.of_mem (by rw [hw, h.1.2.2.2.1, ← h.used_eq]; simp [inWrites]) ?_
  rw [← h.2]
  exact h.nowrap (r := inUsed s) (by simp [inWrites])

/-- The word for the octets consumed is apart from `out` and the
controller's words. -/
theorem SInput.used_disjoint {p : SPub} {s : State} (h : SInput p s) :
    (⟨p.op, p.len⟩ : Region).Disjoint ⟨p.up, 8⟩ ∧ (⟨p.control, 128⟩ : Region).Disjoint ⟨p.up, 8⟩ := by
  have hpw := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  refine ⟨?_, ?_⟩
  · rw [← h.out_eq, ← h.used_eq]; exact hpw.1.1
  · rw [← h.ctl_eq, ← h.used_eq]; exact hpw.2.1.2.symm

theorem search_finish_values {p : SPub} {original s : State} {result : ParameterSearchResult}
    (h : SDone p original result s) :
    WP isa (.block finish) s fun t =>
      (t.gpr .x0 = BitVec.ofNat 64 result.status ∧ t.gpr .x19 = original.gpr .x19 ∧
        t.mem = s.mem.writeW p.up (BitVec.ofNat 64 result.used)) ∧
      Keep [.x0, .x1, .x2, .x19] s t := by
  have scr := h.input.control_scr (t := s) h.wr
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hup : InRegions s.wr p.up 8 := by
    simpa only [off, BitVec.add_zero] using (h.input.used_scr h.wr).st (d := 0) (by decide)
  have hu := h.usedPtr
  have hd := h.used
  have hs := h.status
  have hx := h.savedX19
  simp only [Bignum.word, off] at hu hd hs hx
  refine WP.keep [.x0, .x1, .x2, .x19] ?_ (by decide) (by decide) (by decide +kernel)
  unfold finish
  brun [ldf, h.x19, hu, hd, hs, hx, hup, hl 56 (by decide), hl 96 (by decide), hl 112 (by decide),
    hl 32 (by decide)]

/-- What the search returns, for its result. -/
def SReturned (p : SPub) (result : ParameterSearchResult) (t : State) : Prop :=
  ((t.gpr .x0).setWidth 32).toNat = result.status ∧ SOutput p result t.mem ∧
    Spec.Rsa.wordsAt t.mem p.control 4 = p.policy result ∧
    Spec.Rsa.wordsAt t.mem p.up 1 = [BitVec.ofNat 64 result.used]

theorem search_finish {p : SPub} {original s : State} {result : ParameterSearchResult}
    (h : SDone p original result s) :
    WP isa (.block finish) s fun t => SReturned p result t ∧
      (∀ reg ∈ preserved, reg ≠ .x30 → t.gpr reg = original.gpr reg) ∧ t.sp = s.sp ∧ t.gpr .x30 = s.gpr .x30 ∧
      (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (original.v r).extractLsb' 0 64) := by
  refine WP.mono (search_finish_values h) fun t ⟨⟨ha, hr19, hm⟩, k⟩ => ?_
  have hd := h.input.used_disjoint
  have hk := h.input.len_bounds
  have hf : Frame [⟨p.up, 8⟩] s.mem t.mem := by
    rw [hm]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hb : Spec.Rsa.bytesAt t.mem p.op p.len = Spec.Rsa.bytesAt s.mem p.op p.len := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hd.1)
      (show p.len ≤ 2 ^ 64 by omega_using [hk]) (List.mem_range.mp hi)
  have hc (j : Nat) (hj : j < 4) : word t.mem p.control (8 * j) = word s.mem p.control (8 * j) :=
    hf.readW (r := ⟨p.control, 128⟩)
      (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hd.2) (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, k.sp, k.gpr .x30 (by decide), fun r hr => (k.vcs r hr).trans (h.vcs r hr)⟩
  · rw [ha]
    have := result_status_lt result
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [this]
  · have ho := h.output
    unfold SOutput at ho ⊢
    rw [hb]
    exact ho
  · have he : Spec.Rsa.wordsAt t.mem p.control 4 = Spec.Rsa.wordsAt s.mem p.control 4 := by
      change [word t.mem p.control (8 * 0), word t.mem p.control (8 * 1), word t.mem p.control (8 * 2),
        word t.mem p.control (8 * 3)] = [word s.mem p.control (8 * 0), word s.mem p.control (8 * 1),
        word s.mem p.control (8 * 2), word s.mem p.control (8 * 3)]
      rw [hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide)]
    exact he.trans h.policy
  · change [word t.mem p.up 0] = [_]
    rw [hm]
    congr 1
    simpa only [Bignum.word, off, BitVec.add_zero] using
      Mem.readW_writeW_self64 s.mem p.up (BitVec.ofNat 64 result.used)
  · intro reg hreg h30
    by_cases he : reg = .x19
    · subst he; exact hr19
    · exact (k.gpr reg (by revert reg hreg he; decide)).trans (h.saved reg hreg he h30)

/-! ## The search's frame -/

theorem depth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

theorem iteration_depth (c : Cand) : (iteration c.call).aarch64Depth = 1 := by
  simp only [iteration, candidateRun, exhausted, zeroOut, classify, short, Impl.Bignum.AArch64.countLoop,
    Code.aarch64Depth, Cand.call, depth_of_noFrames c.noFrames, Instr.frameUnits]
  rfl

/-- After the frame: a finished search, with `x30` and the stack pointer back. -/
theorem SDone.popped {p : SPub} {original s : State} {r : ParameterSearchResult}
    (h : SDone p original r s) (v sp : BitVec 64) :
    SDone p original r { s.write .x .x30 v with sp := sp } := by
  refine ⟨h.input, h.rd, h.wr, ?_, fun reg hr h19 h30 => ?_, h.vcs, h.savedX19, h.usedPtr, h.used,
    h.status, h.policy, h.output⟩
  · show (s.write .x .x30 v).gpr .x19 = _
    rw [RegUpd.gpr_write]; exact h.x19
  · show (s.write .x .x30 v).gpr reg = _
    rw [RegUpd.gpr_write, ite_eq_right h30]; exact h.saved reg hr h19 h30

/-- After the frame, whose slot is lost: a finished search, with `x30` and the
stack pointer back. -/
theorem SDone.released {p : SPub} {original s : State} {r : ParameterSearchResult}
    (h : SDone p original r s) (v sp : BitVec 64) {m : Mem} (u : Nat → BitVec 64)
    (hf : Frame [below original.sp stackUse] s.mem m) :
    SDone p original r { s.write .x .x30 v with sp := sp, mem := m, unknowns := u } := by
  have h' := h.popped v sp
  have hc := h.input.control_frame (hf.sub fun R hR => ⟨R, by
    obtain rfl := List.mem_singleton.mp hR; simp [SInput.callChanges], fun _ hi => hi⟩)
  rw [← h.input.sp_eq] at hf
  have ho := fun {i} (hi : i < p.len) => lost_byte (i := i) hf h.input.outStack.1 hi
  refine ⟨h'.input, h'.rd, h'.wr, h'.x19, h'.saved, h'.vcs, (hc 4 (by decide)).trans h.savedX19,
    (hc 7 (by decide)).trans h.usedPtr, (hc 12 (by decide)).trans h.used,
    (hc 14 (by decide)).trans h.status,
    (List.map_congr_left fun i hi => hc i (by have := List.mem_range.mp hi; omega_using [this])).trans
      h.policy, ?_⟩
  exact (List.map_congr_left fun i hi => ho (List.mem_range.mp hi)).trans h.output

theorem SInput.tail_eq {p : SPub} {s : State} (h : SInput p s) : searchResult s = p.tail 0 p.attempts := by
  cases h.2
  simp only [searchResult, SPub.tail, sOfState, List.drop_zero, Proof.Ffdh.Generation.consume_zero]

theorem search_body {p : SPub} {s t : State} (c : Cand) (h : SInput p s)
    (hx : t.gpr .x19 = p.control)
    (hm : t.mem = Proof.Ffdh.Control.writeController s.mem p.control (entryValues s))
    (k : Keep entryRegs s t) :
    WP isa (search c.call) t fun u =>
      SDone p s (searchResult s) u ∧ u.gpr .x30 = s.gpr .x30 ∧ u.sp = s.sp := by
  have hl := search_start h hx hm k
  have hsp : 16 ≤ t.sp.toNat := by rw [k.sp, ← h.sp_eq]; have := h.sp_room; omega_using [this]
  unfold search
  refine WP.frameReg hsp ?_ ?_ ?_
  · intro R hR
    rw [k.wr, h.1.2.2.2.1] at hR
    have hd := h.stack_disjoint (r := R) (List.mem_append_left _ hR)
    refine hd.sub_left ?_
    rw [k.sp]
    exact Offset.sub_below s.sp (a := 16) (b := 32) (by decide) (by decide)
  · refine WP.mono (search_loop c (expected := searchResult s) (n := p.attempts + 1)
      ⟨0, p.attempts, rfl, hl, h.tail_eq⟩) fun u hu m uu f => ?_
    refine ⟨hu.released _ _ uu (f.sub fun R hR => ⟨_, List.mem_singleton_self _, ?_⟩), ?_, k.sp⟩
    · obtain rfl := List.mem_singleton.mp hR
      rw [k.sp]
      exact Offset.sub_below s.sp (a := 16) (b := 32) (by decide) (by decide)
    show (u.write .x .x30 (t.gpr .x30)).gpr .x30 = _
    rw [RegUpd.gpr_write, ite_eq_left rfl]
    exact k.gpr .x30 (by decide)
  · show 16 * (iteration c.call).aarch64Depth + 16 < 2 ^ 64
    rw [iteration_depth c]; decide

theorem SReturned.post {s t : State} (h : SReturned (sOfState s) (searchResult s) t) : searchPost s t :=
  ⟨h.1, h.2.1, h.2.2.2, _, h.2.2.1, SievedGeneration.search_requests _ _ _ _⟩

theorem search_correct_ok (c : Cand) {s : State} (h : searchPre s) :
    WP isa (code c.call) s fun t => searchPost s t ∧ abiPreserved s t := by
  let p := sOfState s
  have hp : SInput p s := ⟨h, rfl⟩
  unfold code
  refine WP.seq (WP.mono (entry_ok hp) fun t ⟨⟨hx, hm⟩, k⟩ => ?_)
  refine WP.seq (WP.mono (search_body c hp hx hm k) fun u ⟨hd, h30, hsp⟩ => ?_)
  refine WP.mono (search_finish hd) fun q ⟨hr, hg, hqsp, hq30, hv⟩ => ?_
  refine ⟨hr.post, fun reg hreg => ?_, hqsp.trans hsp, hv⟩
  by_cases h30 : reg = .x30
  · subst h30; exact hq30.trans h30
  · exact hg reg hreg h30

theorem search_correct (c : Cand) (s : State) (h : searchContract.pre s) :
    ∃ tr t, Exec isa (code c.call) s tr t ∧ abiPreserved s t ∧ searchContract.post s t := by
  obtain ⟨tr, t, he, hp, ha⟩ := search_correct_ok c h
  exact ⟨tr, t, he, ha, hp⟩

end VG.Proof.Ffdh.AArch64.Generation

end

end

/-! ### `Ffdh.AArch64.Generation.Search.CT`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Generation.Search.LeafCT`, which only this module used -/

section

/-! # Public positions in the parameter search, its exits and its candidate (AArch64)

Two runs agree on the public descriptor (the tape included), the octets
consumed and the attempts left, which fix everything the search does from
there. The exits, the rejection and the request use only public addresses;
the candidate leaks only its public arguments and tape.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Spec.Ffdh
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.Control (writeController)
open VG.Proof.Ffdh.AArch64.ParameterCandidate (pcPre pcPub pcRand)
open VG.Impl.Ffdh.AArch64.Generation.Search

/-- Some loop state of the search with the public descriptor `p`. -/
def SAny (p : SPub) (s : State) : Prop := ∃ original used k, SLive p original used k s

structure SPoint where
  inputs : SPub
  used : Nat
  k : Nat

def SCTL (q : SPoint) (s : State) : Prop := ∃ original, SLive q.inputs original q.used q.k s

theorem SCTL.any {q : SPoint} {s : State} (h : SCTL q s) : SAny q.inputs s :=
  let ⟨original, h⟩ := h; ⟨original, _, _, h⟩

theorem s_any_pins : Pins SAny [.x19] := by
  intro p s t ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.x19.trans h₂.x19.symm

theorem s_ctl_pins : Pins SCTL [.x19] :=
  fun _ _ _ h₁ h₂ => s_any_pins _ _ _ h₁.any h₂.any

theorem no_pins {α : Type} {Φ : α → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ h => by cases h

/-! ## Zeros at `out` and the exits -/

/-- Before the zeroing's loop: its pointer and count. -/
def SZeroCT (p : SPub) (s : State) : Prop :=
  SAny p s ∧ s.gpr .x1 = p.op + BitVec.ofNat 64 0 ∧ s.gpr .x2 = BitVec.ofNat 64 p.len

private theorem zero_header (p : SPub) (s : State) (h : SAny p s) :
    WP isa (.block [ldf .x1 5, ldf .x2 6, Impl.Bignum.AArch64.movi .x3 0]) s (SZeroCT p) := by
  obtain ⟨original, used, k, h⟩ := h
  have a := h.access
  have hk : word s.mem p.control 48 = BitVec.ofNat 64 p.len :=
    h.header (j := 6) (by simp [SPub.headers])
  have hp : word s.mem p.control 40 = p.op := h.header (j := 5) (by simp [SPub.headers])
  simp only [Bignum.word, off] at hk hp
  refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => (t.gpr .x1 = p.op + BitVec.ofNat 64 0 ∧
    t.gpr .x2 = BitVec.ofNat 64 p.len) ∧ t.mem = s.mem) ?_ (by decide) (by decide) (by decide +kernel))
    fun _ ⟨⟨hr, hm⟩, k⟩ => ⟨⟨original, used, _, h.keep k hm⟩, hr⟩
  brun [ldf, h.x19, hp, hk, a.ld 40 (by decide), a.ld 48 (by decide), imm64 (show 0 < 65536 by decide)]

theorem s_zero_ct : RelCT isa (Two SAny) zeroOut (fun _ _ => True) := by
  unfold zeroOut
  refine RelCT.seq (two_piece [.x19] s_any_pins (by taint_decide) zero_header) ?_
  exact two_taint [.x1, .x2] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.trans h₂.2.2.symm]) (by taint_decide)

private theorem terminal_ready (p : SPub) (s : State) (h : SAny p s) :
    WP isa (.block (terminal 3)) s (SAny p) := by
  obtain ⟨original, used, k, h⟩ := h
  exact WP.mono (terminal_live h (.inr rfl)) fun _ ⟨ht, _⟩ => ⟨original, used, 0, ht⟩

theorem s_exhausted_ct : RelCT isa (Two SAny) exhausted (fun _ _ => True) := by
  unfold exhausted
  exact RelCT.seq (two_piece [.x19] s_any_pins (by taint_decide) terminal_ready) s_zero_ct

theorem s_accept_ct : RelCT isa (Two SAny) (.block accept) (fun _ _ => True) :=
  two_taint [.x19] s_any_pins (by taint_decide)

theorem s_reject_ct : RelCT isa (Two SAny) (.block reject) (fun _ _ => True) :=
  two_taint [.x19] s_any_pins (by taint_decide)

theorem s_request_ct : RelCT isa (Two SAny) (.block request) (fun _ _ => True) :=
  two_taint [.x19] s_any_pins (by taint_decide)

/-! ## The candidate -/

/-- A loop state at which the controller runs a candidate. -/
def SReady (q : SPoint) (s : State) : Prop := SCTL q s ∧ q.k ≠ 0

/-- The candidate's entry, before the call. -/
def SCallCT (q : SPoint) (u : State) : Prop :=
  ∃ original s, SLive q.inputs original q.used q.k s ∧ q.k ≠ 0 ∧
    SArgs q.inputs q.used u ∧ u.mem = writeController s.mem (callSp q.inputs) (callValues q.inputs) ∧
    Keep argRegsW (allocated 16 s) u

def SAllocated (q : SPoint) (u : State) : Prop := ∃ s, SReady q s ∧ u = allocated 16 s

theorem s_allocated_pins : Pins SAllocated [.x19] := by
  rintro q _ _ ⟨a, ⟨⟨_, h₁⟩, _⟩, rfl⟩ ⟨b, ⟨⟨_, h₂⟩, _⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.x19.trans h₂.x19.symm

private theorem arguments_ready (q : SPoint) (u : State) (h : SAllocated q u) :
    WP isa (.block arguments) u (SCallCT q) := by
  obtain ⟨s, ⟨⟨original, h⟩, hk⟩, rfl⟩ := h
  exact WP.mono (search_arguments_ok h) fun _ ⟨⟨ha, hm⟩, k⟩ => ⟨original, s, h, hk, ha, hm, k⟩

/-- What the candidate sees at its entry, in terms of the point alone. -/
private theorem call_view {q : SPoint} {u : State} (h : SCallCT q u) :
    (callState q.inputs q.used u).sp = callSp q.inputs ∧
    pcRand (callState q.inputs q.used u) = q.inputs.rand.drop q.used ∧
    SArgs q.inputs q.used (callState q.inputs q.used u) ∧
    stackArg (callState q.inputs q.used u) 0 = BitVec.ofNat 64 (q.inputs.Z / 8) := by
  obtain ⟨original, s, h, _, ha, hm, k⟩ := h
  have hu : u.sp = callSp q.inputs := by rw [k.sp]; show s.sp - BitVec.ofNat 64 16 = _; rw [h.sp]
  refine ⟨by simp only [State.withRegions_sp, State.callEntry_sp, hu], call_rand h hm ha, ?_,
    by rw [call_stackArg]; exact call_arg hu hm⟩
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := ha
  exact ⟨(call_gpr (by decide)).trans r0, (call_gpr (by decide)).trans r1, (call_gpr (by decide)).trans r2,
    (call_gpr (by decide)).trans r3, (call_gpr (by decide)).trans r4, (call_gpr (by decide)).trans r5,
    (call_gpr (by decide)).trans r6, (call_gpr (by decide)).trans r7⟩

private theorem call_pub {q : SPoint} {u₁ u₂ : State} (h₁ : SCallCT q u₁) (h₂ : SCallCT q u₂) :
    pcPub (callState q.inputs q.used u₁) (callState q.inputs q.used u₂) := by
  obtain ⟨a₁, b₁, ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩, d₁⟩ := call_view h₁
  obtain ⟨a₂, b₂, ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩, d₂⟩ := call_view h₂
  exact ⟨a₁.trans a₂.symm, by rw [b₁, b₂], c0.trans e0.symm, c1.trans e1.symm, c2.trans e2.symm,
    c3.trans e3.symm, by rw [c4, e4], c5.trans e5.symm, c6.trans e6.symm, c7.trans e7.symm,
    d₁.trans d₂.symm⟩

private theorem call_ready {q : SPoint} {u : State} (h : SCallCT q u) :
    pcPre (callState q.inputs q.used u) ∧
      Covers (callRd q.inputs q.used ++ callWr q.inputs) (u.rd ++ u.wr) ∧
      Covers (callWr q.inputs) u.wr := by
  obtain ⟨original, s, h, _, ha, hm, k⟩ := h
  have hu : u.sp = callSp q.inputs := by rw [k.sp]; show s.sp - BitVec.ofNat 64 16 = _; rw [h.sp]
  exact ⟨call_candidate_pre h.callFacts hu ha hm, call_covers_reads h k.rd k.wr,
    call_covers_writes h k.wr⟩

theorem s_candidate_call_ct (c : Cand) :
    RelCT isa (Two SCallCT) c.call (fun _ _ => True) := by
  refine RelCT.callEx c.correct c.ct fun u₁ u₂ ⟨q, h₁, h₂, _⟩ => ?_
  obtain ⟨p₁, c₁, w₁⟩ := call_ready h₁
  obtain ⟨p₂, c₂, w₂⟩ := call_ready h₂
  exact ⟨_, _, _, _, p₁, p₂, call_pub h₁ h₂, c₁, w₁, c₂, w₂⟩

theorem s_candidate_run_ct (c : Cand) :
    RelCT isa (Two SReady) (candidateRun c.call) (fun _ _ => True) := by
  unfold candidateRun
  apply RelCT.alloc
  refine (RelCT.seq (two_piece [.x19] s_allocated_pins (by taint_decide) arguments_ready)
    (s_candidate_call_ct c)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocated, hsp]⟩

/-- After the candidate. -/
def SCandidated (q : SPoint) (t : State) : Prop :=
  ∃ original, SLive q.inputs original q.used q.k t ∧ q.k ≠ 0 ∧ CandPost q.inputs q.used t

theorem s_candidate_ready (c : Cand) (q : SPoint) (s : State) (h : SReady q s) :
    WP isa (candidateRun c.call) s (SCandidated q) := by
  obtain ⟨⟨original, h⟩, hk⟩ := h
  exact WP.mono (search_candidate_run c h) fun _ ⟨ht, hp⟩ => ⟨original, ht, hk, hp⟩

end VG.Proof.Ffdh.AArch64.Generation

end

end

/-! # The parameter search's timing depends on its public data alone (AArch64)

Every branch is on the attempts left, the candidate's status and the
tape's length, which the point (the public descriptor, the octets consumed
and the attempts left) fixes.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Spec.Ffdh
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.Control (writeController)
open VG.Impl.Ffdh.AArch64.Generation.Search

/-! ## The classification -/

theorem s_candidated_pins : Pins SCandidated [.x19] := by
  intro q s t ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.x19.trans h₂.x19.symm

/-- The candidate's status. -/
abbrev SPoint.status (q : SPoint) : Nat := candidateStatus (q.inputs.cand q.used)

/-- The status in `x9`, compared with `j` in `x12`. -/
def SGuard (j : Nat) (q : SPoint) (t : State) : Prop :=
  SCTL q t ∧ q.k ≠ 0 ∧ t.gpr .x9 = BitVec.ofNat 64 q.status ∧
    isa.eval (.zero .x .x12) t = some (decide (q.status = j))

/-- After the status and the pointer to `used` are loaded. -/
def SHead (q : SPoint) (t : State) : Prop :=
  SCandidated q t ∧ t.gpr .x11 = q.inputs.up ∧ t.gpr .x9 = BitVec.ofNat 64 q.status

private theorem head_first (q : SPoint) (s : State) (h : SCandidated q s) :
    WP isa (.block [.addImm .w .x9 .x0 0, ldf .x11 7]) s (SHead q) := by
  obtain ⟨original, h, hk, hp⟩ := h
  have a := h.access
  have hv7 := h.header (j := 7) (v := q.inputs.up) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv7
  have hst : q.status < 3 := status_lt (q.inputs.cand q.used)
  have h0 : (s.gpr .x0).setWidth 32 = BitVec.ofNat 32 q.status := by
    apply BitVec.eq_of_toNat_eq
    rw [hp.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hst])]
  refine WP.mono (WP.keep [.x9, .x11] (Q := fun t =>
    (t.gpr .x11 = q.inputs.up ∧ t.gpr .x9 = BitVec.ofNat 64 q.status) ∧ t.mem = s.mem) ?_
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨⟨h11, h9⟩, hm⟩, k⟩ => ?_
  · brun [ldf, h.x19, hv7, a.ld 56 (by decide),
      VG.Proof.RsaKeyGen.AArch64.exec_addImm_w (show 0 < 4096 by decide), h0]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [hst]
  · refine ⟨⟨original, h.keep k hm, hk, ?_⟩, h11, h9⟩
    unfold CandPost at hp ⊢
    rw [hm, k.gpr .x0 (by decide)]
    exact hp

theorem s_head_pins : Pins SHead [.x11] := by
  intro q s t h₁ h₂ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.2.1.trans h₂.2.1.symm

private theorem head_second (q : SPoint) (s : State) (h : SHead q s) :
    WP isa (.block [Impl.Bignum.AArch64.ld .x10 .x11, .subImm .x .x12 .x9 1]) s (SGuard 1 q) := by
  obtain ⟨⟨original, h, hk, _⟩, h11, h9⟩ := h
  have hu : InRegions (s.rd ++ s.wr) q.inputs.up 8 := by
    refine ⟨⟨q.inputs.up, 8⟩, List.mem_append_right _ ?_, ?_⟩
    · rw [h.wr, h.input.1.2.2.2.1, ← h.input.used_eq]; simp [inWrites]
    · simpa only [BitVec.add_zero] using Offset.contains_base q.inputs.up (d := 0) (n := 8) (k := 8)
        (by decide) (by decide)
  have hst : q.status < 3 := status_lt (q.inputs.cand q.used)
  refine WP.mono (WP.keep [.x10, .x12] (Q := fun t =>
    isa.eval (.zero .x .x12) t = some (decide (q.status = 1)) ∧ t.mem = s.mem) ?_
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨he, hm⟩, k⟩ =>
      ⟨⟨original, h.keep k hm⟩, hk, (k.gpr .x9 (by decide)).trans h9, he⟩
  brun [h11, h9, hu]
  have : ∀ st < 3, ((BitVec.ofNat 64 st - BitVec.ofNat 64 1) == 0) = decide (st = 1) := by decide
  simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq, this _ hst]

private theorem second_ready (q : SPoint) (s : State)
    (h : SGuard 1 q s ∧ isa.eval (.zero .x .x12) s = some false) :
    WP isa (.block [.subImm .x .x12 .x9 2]) s (SGuard 2 q) := by
  obtain ⟨⟨⟨o, hl⟩, hk, h9, _⟩, _⟩ := h
  refine WP.mono (test_two h9 (status_lt _)) fun t ⟨⟨he, hm⟩, kt⟩ => ?_
  exact ⟨⟨o, hl.keep kt hm⟩, hk, (kt.gpr .x9 (by decide)).trans h9, he⟩

private theorem guard_eq (j : Nat) (q : SPoint) (s₁ s₂ : State) (h₁ : SGuard j q s₁)
    (h₂ : SGuard j q s₂) : isa.eval (.zero .x .x12) s₁ = isa.eval (.zero .x .x12) s₂ :=
  h₁.2.2.2.trans h₂.2.2.2.symm

private theorem leafB {α : Type} {Φ : α → State → Prop} {c : Prog isa} (f : α → SPub)
    (hΦ : ∀ q s, Φ q s → SAny (f q) s) (hc : RelCT isa (Two SAny) c fun _ _ => True) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨f q, hΦ q _ h₁, hΦ q _ h₂, hsp⟩) fun _ _ h => h

/-- Whether the tape holds the entropy cap, after a short tape. -/
def SShort (q : SPoint) (t : State) : Prop :=
  SCTL q t ∧ isa.eval (.zero .x .x12) t =
    some (decide (q.inputs.randLen - q.used < parameterEntropy q.inputs.bits))

private theorem short_ready (q : SPoint) (s : State)
    (h : SGuard 2 q s ∧ isa.eval (.zero .x .x12) s = some false) :
    WP isa (.block [ldf .x10 11, ldf .x11 2, .subs .x .x12 .x10 .x11, Impl.Bignum.AArch64.movi .x13 0,
      Impl.Bignum.AArch64.movi .x14 1, .csel .x .x12 .x14 .x13]) s (SShort q) := by
  obtain ⟨⟨⟨o, hl⟩, _⟩, _⟩ := h
  exact WP.mono (short_guard hl) fun t ⟨⟨ht, _⟩, he⟩ => ⟨⟨o, ht⟩, he⟩

theorem s_short_ct : RelCT isa (Two fun q s => SGuard 2 q s ∧ isa.eval (.zero .x .x12) s = some false)
    short (fun _ _ => True) := by
  unfold short
  refine RelCT.seq (two_piece [.x19] (fun q _ _ h₁ h₂ => s_ctl_pins q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide) short_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact leafB SPoint.inputs (fun _ _ h => h.1.1.any) s_request_ct
  · exact leafB SPoint.inputs (fun _ _ h => h.1.1.any) s_exhausted_ct

theorem s_classify_ct : RelCT isa (Two SCandidated) classify (fun _ _ => True) := by
  unfold classify
  change RelCT isa (Two SCandidated) (.seq (.block ([.addImm .w .x9 .x0 0, ldf .x11 7] ++
    [Impl.Bignum.AArch64.ld .x10 .x11, .subImm .x .x12 .x9 1])) _) _
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (two_piece [.x19] s_candidated_pins (by taint_decide) head_first)
    (two_piece [.x11] s_head_pins (by taint_decide) head_second))) ?_
  refine two_ite (guard_eq 1) (leafB SPoint.inputs (fun _ _ h => h.1.1.any) s_accept_ct) ?_
  refine RelCT.seq (two_post (two_taint [] no_pins (by taint_decide)) second_ready) ?_
  exact two_ite (guard_eq 2) (leafB SPoint.inputs (fun _ _ h => h.1.1.any) s_reject_ct) s_short_ct

/-! ## An iteration -/

/-- Whether the search goes on after an iteration from `q`: a candidate is
rejected. -/
def sContinues (q : SPoint) : Prop := q.k ≠ 0 ∧ q.status = 2

instance (q : SPoint) : Decidable (sContinues q) :=
  inferInstanceAs (Decidable (q.k ≠ 0 ∧ q.status = 2))

/-- The point after a rejected candidate. -/
def nextPoint (q : SPoint) : SPoint := ⟨q.inputs, q.used + q.inputs.read q.used, q.k - 1⟩

/-- After the test of the attempts, the candidate and its classification. -/
def SBranchResult (q : SPoint) (t : State) : Prop :=
  if sContinues q then SCTL (nextPoint q) t ∧ word t.mem q.inputs.control 112 = 4
  else ∃ original r, SDone q.inputs original r t

theorem branch_x19 {q : SPoint} {t : State} (h : SBranchResult q t) :
    t.gpr .x19 = q.inputs.control := by
  by_cases hc : sContinues q
  · simp only [SBranchResult, hc, ite_true] at h
    obtain ⟨⟨_, hl⟩, _⟩ := h
    exact hl.x19
  · simp only [SBranchResult, hc, ite_false] at h
    obtain ⟨_, _, hd⟩ := h
    exact hd.x19

def KGuard (q : SPoint) (s : State) : Prop :=
  SCTL q s ∧ isa.eval (.zero .x .x9) s = some (decide (q.k = 0))

theorem k_ready (q : SPoint) (s : State) (h : SCTL q s) :
    WP isa (.block [ldf .x9 0]) s (KGuard q) := by
  obtain ⟨original, h⟩ := h
  exact WP.mono (attempts_guard h) fun _ ⟨ht, he⟩ => ⟨⟨original, ht⟩, he⟩

/-- The branch of an iteration. -/
abbrev sBranch (c : Cand) : Prog isa := .ite (.zero .x .x9) exhausted (.seq (candidateRun c.call) classify)

theorem s_branch_ready (c : Cand) (q : SPoint) (s : State) (h : KGuard q s) :
    WP isa (sBranch c) s (SBranchResult q) := by
  obtain ⟨⟨original, hl⟩, he⟩ := h
  refine WP.ite (decide (q.k = 0)) he ?_ ?_
  · intro hz
    have hz' := of_decide_eq_true hz
    refine WP.mono (search_exhausted hl) fun t ht => ?_
    simp only [SBranchResult, sContinues, hz', ne_eq, not_true_eq_false, false_and, ite_false]
    exact ⟨original, _, ht⟩
  intro hnz
  have hk : q.k ≠ 0 := of_decide_eq_false hnz
  refine WP.seq (WP.mono (search_candidate_run c hl) fun t ⟨ht, hp⟩ => ?_)
  refine WP.mono (search_classify ht hk hp) fun r hr => ?_
  unfold SClassified at hr
  by_cases h2 : q.status = 2
  · simp only [SPoint.status] at h2
    simp only [h2, ite_true] at hr
    have hc : sContinues q := ⟨hk, h2⟩
    simp only [SBranchResult, hc, ite_true]
    exact ⟨⟨original, hr.1⟩, hr.2⟩
  · simp only [SPoint.status] at h2
    simp only [h2, ite_false] at hr
    have hc : ¬sContinues q := fun hc => h2 hc.2
    simp only [SBranchResult, hc, ite_false]
    exact ⟨original, _, hr⟩

theorem s_branch_ct (c : Cand) : RelCT isa (Two KGuard) (sBranch c) (fun _ _ => True) := by
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (leafB SPoint.inputs (fun _ _ h => h.1.1.any) s_exhausted_ct) ?_
  have hr : ∀ q s, KGuard q s ∧ isa.eval (.zero .x .x9) s = some false → SReady q s :=
    fun q s ⟨⟨hl, he⟩, hf⟩ => ⟨hl, of_decide_eq_false (Option.some.inj (he.symm.trans hf))⟩
  exact RelCT.seq (two_post ((s_candidate_run_ct c).mono
      (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, hr q _ h₁, hr q _ h₂, hsp⟩) fun _ _ h => h)
    fun q s h => s_candidate_ready c q s (hr q s h)) s_classify_ct

theorem s_iteration_ct (c : Cand) :
    RelCT isa (Two SCTL) (iteration c.call) (fun _ _ => True) := by
  unfold iteration
  refine RelCT.seq (two_piece [.x19] s_ctl_pins (by taint_decide) k_ready) ?_
  exact RelCT.seq (two_post (s_branch_ct c) (s_branch_ready c))
    (two_taint [.x19] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact (branch_x19 h₁).trans (branch_x19 h₂).symm) (by taint_decide))

def SCTStep (q : SPoint) (s : State) : Prop :=
  if sContinues q then isa.eval (.zero .x .x9) s = some true ∧ SCTL (nextPoint q) s
  else isa.eval (.zero .x .x9) s = some false

theorem s_ct_step (c : Cand) (q : SPoint) (s : State) (h : SCTL q s) :
    WP isa (iteration c.call) s (SCTStep q) := by
  unfold iteration
  refine WP.seq (WP.mono (k_ready q s h) fun u hu => ?_)
  refine WP.seq (WP.mono (s_branch_ready c q u hu) fun t ht => ?_)
  by_cases hc : sContinues q
  · simp only [SBranchResult, hc, ite_true] at ht
    obtain ⟨⟨original, hl⟩, hw⟩ := ht
    refine WP.mono (live_loop_guard hl hw) fun z ⟨hz, hzl⟩ => ?_
    simp only [SCTStep, hc, ite_true]
    exact ⟨hz, original, hzl⟩
  · simp only [SBranchResult, hc, ite_false] at ht
    obtain ⟨_, _, hd⟩ := ht
    refine WP.mono (done_loop_guard hd) fun z ⟨hz, _⟩ => ?_
    simp only [SCTStep, hc, ite_false]
    exact hz

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q, n = q.k + 1 ∧ SCTL q s ∧ SCTL q t ∧ s.sp = t.sp

private theorem iteration_pair (c : Cand) (n : Nat) :
    RelCT isa (LoopPair n) (iteration c.call) fun s t =>
      isa.eval (.zero .x .x9) s = isa.eval (.zero .x .x9) t ∧
      (isa.eval (.zero .x .x9) s = some false → True) ∧
      (isa.eval (.zero .x .x9) s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (q : SPoint) (s : State) (h : n = q.k + 1 ∧ SCTL q s) :
      WP isa (iteration c.call) s fun t => n = q.k + 1 ∧ SCTStep q t :=
    WP.mono (s_ct_step c q s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((s_iteration_ct c).mono
    (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.2, h₂.2, hsp⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂, hsp⟩ => ⟨q, ⟨hn, h₁⟩, ⟨hn, h₂⟩, hsp⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, ⟨_, h₂⟩, hsp⟩
  by_cases hb : sContinues q
  · simp only [SCTStep, hb, ite_true] at h₁ h₂
    refine ⟨h₁.1.trans h₂.1.symm, fun _ => trivial, fun _ => ?_⟩
    refine ⟨(nextPoint q).k + 1, ?_, nextPoint q, rfl, h₁.2, h₂.2, hsp⟩
    have := hb.1
    simp only [nextPoint]
    omega_using [hn, this]
  · simp only [SCTStep, hb, ite_false] at h₁ h₂
    exact ⟨h₁.trans h₂.symm, fun _ => trivial, fun ht => absurd (ht.symm.trans h₁) (by decide)⟩

theorem s_loop_ct (c : Cand) :
    RelCT isa (Two SCTL) (.loop (iteration c.call) (.zero .x .x9)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht, hsp⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration c.call) (c := .zero .x .x9)
    (Q := fun _ _ => True) LoopPair (iteration_pair c) (q.k + 1)
    _ _ _ _ _ _ ⟨q, rfl, hs, ht, hsp⟩ he₁ he₂

end VG.Proof.Ffdh.AArch64.Generation

end

end

/-! # The parameter search is constant time for its public data (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Spec.Ffdh
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.Control (writeController)
open VG.Impl.Ffdh.AArch64.Generation.Search

/-! ## The frame saving `x30` -/

/-- A frame saving `x30` around a body proven with the permissions outside
it (as `WP.frameReg` runs it) leaks what the body does there: the body's
run in the frame is that run, with more permissions (`Exec.widen`). -/
theorem relCT_pushX30 {body : Prog isa} {P : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp)
    (hwp : ∀ a b, P a b → (∃ t s', Exec isa body (pushedX30 a) t s') ∧
      (∃ t s', Exec isa body (pushedX30 b) t s'))
    (hct : RelCT isa (fun x y => ∃ a b, P a b ∧ x = pushedX30 a ∧ y = pushedX30 b) body
      fun _ _ => True) :
    RelCT isa P (.frame (.push .x30) body (.pop .x30)) fun _ _ => True := by
  refine RelCT.pushFrame (R := fun _ _ => True) hsp ?_
  have widen : ∀ a, ∀ {t s'}, Exec isa body (pushedX30 a) t s' →
      Exec isa body (pushed .x30 a) t (s'.withRegions a.rd (⟨a.sp - 16, 16⟩ :: a.wr)) := by
    intro a t s' e
    have := Exec.widen e (rd := a.rd) (wr := ⟨a.sp - 16, 16⟩ :: a.wr)
      (Covers.of_mem fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact List.mem_append_left _ hr
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr))
      (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr)
    exact this
  rintro x y tx ty x' y' ⟨a, b, hab, rfl, rfl⟩ ex ey
  obtain ⟨⟨ta, sa, ea⟩, ⟨tb, sb, eb⟩⟩ := hwp a b hab
  obtain ⟨rfl, -⟩ := Exec.det ex (widen a ea)
  obtain ⟨rfl, -⟩ := Exec.det ey (widen b eb)
  exact ⟨(hct _ _ _ _ _ _ ⟨a, b, hab, rfl, rfl⟩ ea eb).1, trivial⟩

/-! ## Entry and return -/

private theorem entry_pointer (p : SPub) (s : State) (h : SInput p s) :
    WP isa (.block (entry.take 4)) s fun t => t.gpr .x8 = p.control := by
  have hd : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = p.control :=
    congrArg SPub.control h.2
  have ha0 : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa only [Nat.mul_zero, BitVec.add_zero] using input_args h 0 (by decide)
  have ha1 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 := input_args h 1 (by decide)
  unfold entry
  simp only [List.take_succ_cons, List.take_zero]
  brun [exec_addSp (show 0 < 4096 by decide), hd, ha0, ha1,
    VG.Proof.RsaKeyGen.AArch64.exec_addImm_w (show 0 < 4096 by decide)]

private theorem entry_ct : RelCT isa (Two SInput) (.block entry) (fun _ _ => True) := by
  change RelCT isa (Two SInput) (.block (entry.take 4 ++ entry.drop 4)) _
  refine RelCT.block_append (RelCT.seq (two_piece [] no_pins (by taint_decide) entry_pointer) ?_)
  exact two_taint [.x8] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.trans h₂.symm) (by taint_decide)

/-- After the entry: the controller's words written. -/
def SEntered (p : SPub) (t : State) : Prop :=
  ∃ s, SInput p s ∧ t.gpr .x19 = p.control ∧
    t.mem = writeController s.mem p.control (entryValues s) ∧ Keep entryRegs s t

private theorem entry_ready (p : SPub) (s : State) (h : SInput p s) :
    WP isa (.block entry) s (SEntered p) :=
  WP.mono (entry_ok h) fun _ ⟨⟨hx, hm⟩, k⟩ => ⟨s, h, hx, hm, k⟩

private theorem entered_ctl {p : SPub} {t : State} (h : SEntered p t) :
    SCTL ⟨p, 0, p.attempts⟩ (pushedX30 t) := by
  obtain ⟨s, hi, hx, hm, k⟩ := h
  exact ⟨s, search_start hi hx hm k⟩

def SCTDone (p : SPub) (s : State) : Prop := ∃ original r, SDone p original r s

private theorem search_ct (c : Cand) : RelCT isa (Two SEntered) (search c.call) (fun _ _ => True) := by
  unfold search
  refine relCT_pushX30 (fun _ _ ⟨_, _, _, hsp⟩ => hsp) (fun x y ⟨q, h₁, h₂, _⟩ => ?_) ?_
  · obtain ⟨original, hl⟩ := entered_ctl h₁
    obtain ⟨original', hl'⟩ := entered_ctl h₂
    obtain ⟨t, s', e, -⟩ := search_loop c (n := q.attempts + 1) (expected := q.tail 0 q.attempts)
      ⟨0, _, rfl, hl, rfl⟩
    obtain ⟨t', s'', e', -⟩ := search_loop c (n := q.attempts + 1) (expected := q.tail 0 q.attempts)
      ⟨0, _, rfl, hl', rfl⟩
    exact ⟨⟨t, s', e⟩, ⟨t', s'', e'⟩⟩
  · refine (s_loop_ct c).mono ?_ fun _ _ h => h
    rintro _ _ ⟨x, y, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
    exact ⟨⟨q, 0, q.attempts⟩, entered_ctl h₁, entered_ctl h₂, by simp only [hsp]⟩

private theorem search_ready (c : Cand) (p : SPub) (t : State) (h : SEntered p t) :
    WP isa (search c.call) t (SCTDone p) := by
  obtain ⟨s, hi, hx, hm, k⟩ := h
  exact WP.mono (search_body c hi hx hm k) fun _ ⟨hd, _, _⟩ => ⟨s, _, hd⟩

private theorem finish_pointer (p : SPub) (s : State) (h : SCTDone p s) :
    WP isa (.block (finish.take 4)) s fun t => t.gpr .x1 = p.up := by
  obtain ⟨original, r, h⟩ := h
  have scr := h.input.control_scr (t := s) h.wr
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hu := h.usedPtr
  simp only [Bignum.word, off] at hu
  unfold finish
  simp only [List.take_succ_cons, List.take_zero]
  brun [ldf, h.x19, hu, hl 56 (by decide), hl 96 (by decide), hl 112 (by decide), hl 32 (by decide)]

private theorem finish_ct : RelCT isa (Two SCTDone) (.block finish) (fun _ _ => True) := by
  change RelCT isa (Two SCTDone) (.block (finish.take 4 ++ finish.drop 4)) _
  refine RelCT.block_append (RelCT.seq (two_piece [.x19] ?_ (by taint_decide) finish_pointer) ?_)
  · intro p s t ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.x19.trans h₂.x19.symm
  · exact two_taint [.x1] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact h₁.trans h₂.symm) (by taint_decide)

theorem search_code_ct (c : Cand) : RelCT isa (Two SInput) (code c.call) (fun _ _ => True) := by
  unfold code
  exact RelCT.seq (two_post entry_ct entry_ready)
    (RelCT.seq (two_post (search_ct c) (search_ready c)) finish_ct)

private theorem s_public_descriptor {s t : State} (h : searchPub s t) : sOfState s = sOfState t := by
  obtain ⟨hsp, hr, hw, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1⟩ := h
  have h0 : s.mem.readW (stackArg s 1) 64 = t.mem.readW (stackArg t 1) 64 := by
    change [word s.mem (stackArg s 1) 0, word s.mem (stackArg s 1) 8, word s.mem (stackArg s 1) 16,
      word s.mem (stackArg s 1) 24] = [word t.mem (stackArg t 1) 0, word t.mem (stackArg t 1) 8,
        word t.mem (stackArg t 1) 16, word t.mem (stackArg t 1) 24] at hw
    simpa only [Bignum.word, off, BitVec.add_zero] using (List.cons.inj hw).1
  have hrand : genRand s = genRand t := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hr
  unfold sOfState
  rw [genAttempts, genAttempts, h0, hrand, hsp, r0, r2, r5, r7, genLen, genLen, r1, genBits, genBits, r3,
    genGen, genGen, r4, r6, a0, a1]

theorem search_constantTime (c : Cand) :
    ConstantTime isa searchContract.pre searchContract.pub (code c.call) := by
  refine RelCT.constantTime ((search_code_ct c).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨sOfState s, ⟨hs, rfl⟩, ⟨ht, (s_public_descriptor hp).symm⟩, hp.1⟩

end VG.Proof.Ffdh.AArch64.Generation

end

end

/-! ### `Ffdh.AArch64.Generation.Search.Implies`, which only this module used -/

section

/-! # The parameter search's contract is its shared callable contract (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Spec.Ffdh

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

private theorem args_nowrap {s : State} (h : s.sp.toNat + 16 ≤ 2 ^ 64) :
    (stackArgAddr s 0).toNat + 16 ≤ 2 ^ 64 := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  exact h

theorem search_implies_pre (s : State) (h : (sievedParameterSearchContract abi 32).pre s) : searchContract.pre s := by
  sig_pre [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow, searchContract, searchPre,
    inReads, inWrites, inOut, inUsed, inRand, inScr, inCtl, inArgs, stackArgs_two, List.append_eq] at h
  sig_pre [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow, searchContract, searchPre,
    inReads, inWrites, inOut, inUsed, inRand, inScr, inCtl, inArgs, stackArgs_two, List.append_eq] at h
  sig_split h
  sig_reduce [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow, searchContract, searchPre,
    inReads, inWrites, inOut, inUsed, inRand, inScr, inCtl, inArgs, stackArgs_two, List.append_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.pairwise_cons, List.Pairwise.nil, and_true, false_implies,
    implies_true]
  sig_and_intros
  sig_close
  all_goals first
    | (intro x hx; cases hx)
    | exact True.intro
    | with_reducible assumption
    | with_reducible rfl
    | omega
    | with_reducible exact Region.Disjoint.symm ‹_›
    | exact args_nowrap ‹_›

theorem search_implies_post : ∀ s t, (sievedParameterSearchContract abi 32).pre s →
    searchContract.post s t → (sievedParameterSearchContract abi 32).post s t := by
  sig_implies_post [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, searchContract, searchPost,
    searchResult, genRand, genLen, genBits, genGen, genAttempts, stackArgs_two, List.append_eq,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem search_implies_pub (s t : State) (_hs : (sievedParameterSearchContract abi 32).pre s)
    (_ht : (sievedParameterSearchContract abi 32).pre t) (h : (sievedParameterSearchContract abi 32).pub s t) :
    searchContract.pub s t := by
  sig_pub [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackArgs_two, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1⟩ := h
  have hl1 : (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)).length =
      (List.map (fun x => BitVec.toNat x) (Spec.Rsa.bytesAt t.mem (t.gpr .x5) (t.gpr .x6).toNat)).length := by
    simp only [List.length_map, Spec.Rsa.bytesAt, List.length_range, r6]
  obtain ⟨hr, hw⟩ := List.append_inj hleak hl1
  exact ⟨hsp, hr, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hw, r0, r1, r2, r3, r4, r5, r6, r7,
    a0, a1⟩

/-- A 512-bit search with an empty tape and disjoint buffers. -/
private def searchSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 512 | .x4 => 2 | .x5 => 0x3000
    | .x7 => 0x8000 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6000 then 0x20 else if a = 0x6001 then 0x04 else if a = 0x6009 then 0x40
    else if a = 0x4008 then 0x40 else if a = 0x4010 then 0x40 else if a = 0x4012 then 0x20 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x6000, 16⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 8⟩, ⟨0x8000, 1056 * 8⟩, ⟨0x4000, 128⟩]

theorem search_implies : searchContract.Implies (sievedParameterSearchContract abi 32) where
  pre := search_implies_pre
  post := search_implies_post
  pub := search_implies_pub
  sat := by
    refine ⟨searchSat, ?_⟩
    sig_iff
    sig_reduce [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow, searchContract, searchPre,
      stackArgs_two, List.append_eq, parameterAttempts, parameterEntropy]
    sig_and_intros
    all_goals first
      | exact Region.disjoint_of_sep (by decide +kernel)
      | decide +kernel

end VG.Proof.Ffdh.AArch64.Generation

end

end


/-! # The verified parameter search (AArch64)

For any candidate with no frames (`search_verified_of`), and for the
candidate calling each shared Miller–Rabin round (`search_verified`), as
`Generic/MillerRabin/AArch64/Ffdh.lean` registers it.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.MillerRabin.AArch64 (RoundImpl)

theorem search_verified_of (c : Cand) :
    Verified target (Impl.Ffdh.AArch64.Generation.Search.code c.call)
      (Spec.Ffdh.sievedParameterSearchContract abi stackUse) :=
  Verified.of_correct (search_correct c) (search_constantTime c) search_implies

theorem candidate_noFrames (v : RoundImpl) : (code v.mont.mm v.kernel.run).noFrames = true := by
  simp only [code, main, mainQ, mainP, tests, testQ, testRest, test, firstCheck, restChecks, phase, shapeP, residue, sieve, halveQ,
    montPrep, millerRabin, draw, round, pResult, qResult, Impl.Rsa.AArch64.Keys.loadA, Impl.RsaKeyGen.AArch64.Candidate.trialEntry,
    Impl.RsaKeyGen.AArch64.Candidate.halfPass, Impl.RsaKeyGen.AArch64.Candidate.subA,
    Impl.RsaKeyGen.AArch64.Candidate.expSetup, Impl.Rsa.AArch64.r2Steps, Impl.Rsa.AArch64.r2StepsOld, Impl.Rsa.AArch64.sqs,
    Impl.Bignum.AArch64.R2Div.choice,
    Impl.RsaKeyGen.AArch64.Candidate.lowWord, Impl.RsaKeyGen.AArch64.Candidate.halfCond,
    RoundImpl.kernel, MillerRabin.AArch64.Kernel.called, Impl.MillerRabin.AArch64.Caller.call,
    List.cons_append, List.nil_append, List.append_nil, ite_true, ite_false, Bool.false_eq_true,
    Impl.Bignum.AArch64.seqs, Code.noFrames, Bool.and_eq_true, v.mmNoFrames, true_and, and_true]
  and_intros
  all_goals first | rfl | exact v.noFrames

/-- `vg_ffdh_parameter_candidate_sieved` calling the shared round `v`, as the
search calls it. -/
def Cand.ofRound (v : RoundImpl) : Cand where
  name := "vg_ffdh_parameter_candidate_sieved" ++ v.suffix
  code := Impl.Ffdh.AArch64.ParameterCandidate.code v.mont.mm v.kernel.run
  noFrames := candidate_noFrames v
  correct := ParameterCandidate.code_correct v.mont v.kernel
  ct := ParameterCandidate.code_constantTime v.mont v.kernel

/-- The search calling it. -/
abbrev searchCode (v : RoundImpl) : Prog isa := Impl.Ffdh.AArch64.Generation.Search.code (Cand.ofRound v).call

theorem search_verified (v : RoundImpl) :
    Verified target (searchCode v) (Spec.Ffdh.sievedParameterSearchContract abi stackUse) :=
  search_verified_of (Cand.ofRound v)
end VG.Proof.Ffdh.AArch64.Generation
