module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Loop
public import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Loop
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTBase
public import VerifiedGarbage.Proof.Ffdh.Contract
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTBase
meta import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Call
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Writes
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Call
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Writes
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Ffdh.SievedBounds
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Data
public import VerifiedGarbage.Proof.Ffdh.ControlMemory
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Ffdh.SievedBounds
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Impl.Ffdh.PPC64LE.Generation.Search
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Data
meta import VerifiedGarbage.Proof.Ffdh.ControlMemory
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call

/-! ### `Ffdh.PPC64LE.Generation.Search.Correct`, which this module and modules that import it used -/

section

/-! ### `Ffdh.PPC64LE.Generation.Search.Entry`, which this module and modules that import it used -/

section

/-! # The parameter search's entry (PPC64LE)

The stack arguments are loaded, the caller's `r31` saved in word 4 and the
arguments stored in the controller's words; then, in the frame saving the
link register, the controller is at the tape's start with its attempts
(`search_start`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Spec.Ffdh
open VG.Proof.Ffdh.Control (writeController writeController_frame writeController_word
  controllerValue)
open VG.Impl.Ffdh.PPC64LE.Generation.Search

def entryValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .r31), (5, s.gpr .r3), (6, s.gpr .r4), (7, s.gpr .r5), (8, s.gpr .r6),
    (9, BitVec.ofNat 64 (genGen s)), (10, s.gpr .r8), (11, s.gpr .r9), (12, 0), (13, s.gpr .r10),
    (15, stackArg s 0)]

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 16 := by
  simp only [entryValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem input_args {p : SPub} {s : State} (h : SInput p s) (j : Nat) (hj : j < 2) :
    InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 (8 * j)) 8 := by
  refine ⟨inArgs s, ?_, ?_⟩
  · rw [h.1.2.2.1]
    exact List.mem_append_left _ (by simp [inReads])
  · simp only [inArgs, stackArgAddr, Nat.reduceMul, Nat.reduceAdd]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-- The registers the entry writes. -/
abbrev entryRegs : List Reg := [.r0, .r7, .r11, .r12, .r31]

theorem gen_zext (x : BitVec 64) : (x.setWidth 32).setWidth 64 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq; simp

theorem entry_ok {p : SPub} {s : State} (h : SInput p s) :
    WP isa (.block entry) s fun t =>
      (t.gpr .r31 = p.control ∧ t.mem = writeController s.mem p.control (entryValues s)) ∧
      Keep entryRegs s t := by
  have scr := h.control_scr (t := s) rfl
  have hd : s.mem.readW (s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) 64 = p.control := by
    rw [← congrArg SPub.control h.2]
    simp only [sOfState, stackArg, stackArgAddr, Nat.reduceMul, Nat.reduceAdd]
    rw [VG.Offset.add_add]
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have ha0 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 96) 8 := by
    simpa only [Nat.mul_zero, BitVec.add_zero] using input_args h 0 (by decide)
  have ha1 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) 8 :=
    input_args h 1 (by decide)
  have e104 : s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 = s.sp + BitVec.ofNat 64 104 := VG.Offset.add_add _ _ _
  have hd' : s.mem.readW (s.sp + BitVec.ofNat 64 104) 64 = p.control := by rw [← e104]; exact hd
  have ha1' : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 104) 8 := by rw [← e104]; exact ha1
  have ea : exec (.addSp .r11 96) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 96)) := by
    simp [exec]
  refine WP.keep entryRegs ?_ (by decide)
  unfold entry writeController entryValues
  simp only [List.foldl_cons, List.foldl_nil]
  prun [ldf, stf, ea, hd, ha0, ha1, hd', ha1', hs 32 (by decide), hs 40 (by decide), hs 48 (by decide),
    hs 56 (by decide), hs 64 (by decide), hs 72 (by decide), hs 80 (by decide), hs 88 (by decide),
    hs 96 (by decide), hs 104 (by decide), hs 120 (by decide), BitVec.ushiftRight_zero]
  refine ⟨BitVec.add_zero _, ?_⟩
  rw [gen_zext]
  rfl

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

/-- The push of the frame saving the link register writes only below the
stack pointer. -/
theorem push_frame (s : State) (m : Mem) (v : BitVec 64) :
    Frame (SInput.callChanges s) m ((m.write (s.sp - 48) 8 s.sp).write (s.sp - 48 + 32) 8 v) := by
  have e : s.sp - 48 + 32 = s.sp - BitVec.ofNat 64 16 := by bv_omega
  have hr : below s.sp stackUse ∈ SInput.callChanges s := by simp [SInput.callChanges]
  refine Frame.write (Frame.write (Frame.refl _ _) hr _ ?_) hr _ ?_
  · exact Offset.contains_below s.sp (a := 48) (b := 336) (by decide) (by decide) (by decide)
  · rw [e]; exact Offset.contains_below s.sp (a := 16) (b := 336) (by decide) (by decide) (by decide)

theorem search_start {p : SPub} {s t : State} (h : SInput p s)
    (hx : t.gpr .r31 = p.control) (hm : t.mem = writeController s.mem p.control (entryValues s))
    (k : Keep entryRegs s t) (hy : t.syms = s.syms) :
    SLive p s 0 p.attempts (framed .r0 t) := by
  have hf := writeController_frame s.mem p.control (entryValues s) (entryValues_bound s)
  have hf₁ : Frame (SInput.changes s) s.mem t.mem := by
    rw [hm]
    exact hf.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨inCtl s, by simp [SInput.changes, inWrites], by rw [h.ctl_eq]; exact fun _ hi => hi⟩
  have hp := push_frame s t.mem (t.gpr .r0)
  rw [← k.sp] at hp
  have hf₂ : Frame (SInput.changes s) s.mem (framed .r0 t).mem :=
    hf₁.trans (frame_of_callChanges s hp)
  have hc (j : Nat) (hj : j < 16) : word (framed .r0 t).mem p.control (8 * j) = word t.mem p.control (8 * j) :=
    h.control_frame hp j hj
  refine ⟨h, Nat.zero_le _, Nat.le_refl _, k.rd, k.wr, ?_, hx, ?_, ?_, ?_, ?_, hy,
    h.table_frame hf₂ h.table⟩
  · show t.sp - 48 = p.sp - 48
    rw [k.sp, h.sp_eq]
  · intro r hr h31
    exact k.gpr r (by revert r hr h31; decide)
  · rw [show (32 : Nat) = 8 * 4 from rfl, hc 4 (by decide), hm,
      writeController_word _ _ _ (entryValues_bound s) 4 (by decide)]
    rfl
  · rw [h.random_frame hf₂]
    cases h.2
    rfl
  · intro e he
    rw [hc e.1 (SPub.headers_index he), hm]
    exact entry_headers h e he

end VG.Proof.Ffdh.PPC64LE.Generation

end

end

/-! # The parameter search's correctness (PPC64LE)

The link register is moved to `r0`, which the frame around the loop saves
(`WP.frameRegAny`), and back; `finish` then stores the octets consumed,
returns the status and restores `r31`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Spec.Ffdh
open VG.Impl.Ffdh.PPC64LE.Generation.Search

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
      (t.gpr .r3 = BitVec.ofNat 64 result.status ∧ t.gpr .r31 = original.gpr .r31 ∧
        t.mem = s.mem.writeW p.up (BitVec.ofNat 64 result.used)) ∧
      Keep [.r3, .r4, .r5, .r31] s t := by
  have scr := h.input.control_scr (t := s) h.wr
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hup : InRegions s.wr p.up 8 := by
    simpa only [off, BitVec.add_zero] using (h.input.used_scr h.wr).st (d := 0) (by decide)
  have hu := h.usedPtr
  have hd := h.used
  have hs := h.status
  have hx := h.savedR31
  simp only [Bignum.word, off] at hu hd hs hx
  have hf : Frame [⟨p.up, 8⟩] s.mem (s.mem.writeW p.up (BitVec.ofNat 64 result.used)) :=
    Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hx' : (s.mem.writeW p.up (BitVec.ofNat 64 result.used)).readW (p.control + BitVec.ofNat 64 32) 64 =
      original.gpr .r31 :=
    (hf.readW (r := ⟨p.control, 128⟩) (Offset.contains_base _ (by decide) (by decide))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact h.input.used_disjoint.2) (by decide)).trans hx
  refine WP.keep [.r3, .r4, .r5, .r31] ?_ (by decide)
  unfold finish
  prun [ldf, h.r31, hu, hd, hs, hx', hup, hl 56 (by decide), hl 96 (by decide), hl 112 (by decide),
    hl 32 (by decide), BitVec.add_zero]

/-- What the search returns, for its result. -/
def SReturned (p : SPub) (result : ParameterSearchResult) (t : State) : Prop :=
  ((t.gpr .r3).setWidth 32).toNat = result.status ∧ SOutput p result t.mem ∧
    Spec.Rsa.wordsAt t.mem p.control 4 = p.policy result ∧
    Spec.Rsa.wordsAt t.mem p.up 1 = [BitVec.ofNat 64 result.used]

theorem search_finish {p : SPub} {original s : State} {result : ParameterSearchResult}
    (h : SDone p original result s) :
    WP isa (.block finish) s fun t => SReturned p result t ∧
      (∀ reg ∈ preserved, t.gpr reg = original.gpr reg) ∧ t.sp = s.sp ∧ t.lr = s.lr := by
  refine WP.mono (search_finish_values h) fun t ⟨⟨ha, hr31, hm⟩, k⟩ => ?_
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
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, k.sp, k.lr⟩
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
  · intro reg hreg
    by_cases he : reg = .r31
    · subst he; exact hr31
    · exact (k.gpr reg (by revert reg hreg he; decide)).trans (h.saved reg hreg he)

/-! ## The search's frame -/

theorem iteration_depth (c : Cand) : sdepth (iteration c.call) ≤ 288 := by
  have := c.stack
  simp only [iteration, candidateRun, exhausted, zeroOut, classify, short, Impl.Bignum.PPC64LE.countLoop,
    sdepth, Cand.call, Instr.frameBytes]
  omega_using [this]

/-- After the frame: a finished search, with `r0` and the stack pointer
back. -/
theorem SDone.popped {p : SPub} {original s : State} {r : ParameterSearchResult}
    (h : SDone p original r s) (v sp : BitVec 64) :
    SDone p original r { s.write .r0 v with sp := sp } := by
  refine ⟨h.input, h.rd, h.wr, ?_, fun reg hr h31 => ?_, h.savedR31, h.usedPtr, h.used,
    h.status, h.policy, h.output⟩
  · show (s.write .r0 v).gpr .r31 = _
    rw [RegUpd.gpr_write_of_ne _ _ (by decide)]; exact h.r31
  · show (s.write .r0 v).gpr reg = _
    rw [RegUpd.gpr_write_of_ne _ _ (fun e => by subst e; exact absurd hr (by decide))]
    exact h.saved reg hr h31

/-- A finished search, whatever a region of the stack holds: the control
block and `out` lie apart from the stack. -/
theorem SDone.lost {p : SPub} {original s : State} {r : ParameterSearchResult}
    (h : SDone p original r s) {L : Region} {m : Mem} (u : Nat → BitVec 64) (fl : Frame [L] s.mem m)
    (hL : Region.Sub L (below original.sp stackUse)) :
    SDone p original r { s with mem := m, unknowns := u } := by
  have hi := h.input
  obtain hf : Frame (SInput.callChanges original) s.mem m :=
    fl.sub fun q hq => by rw [List.mem_singleton.mp hq]; exact ⟨_, by simp [SInput.callChanges], hL⟩
  obtain hc : ∀ j < 16, word m p.control (8 * j) = word s.mem p.control (8 * j) :=
    fun j hj => hi.control_frame hf j hj
  obtain hbo : Spec.Rsa.bytesAt m p.op p.len = Spec.Rsa.bytesAt s.mem p.op p.len :=
    List.map_congr_left fun i hi' => lost_byte fl (R := ⟨p.op, p.len⟩)
      (by rw [← hi.out_eq]; exact ((hi.stack_disjoint (r := inOut original) (by simp [inWrites])).sub_left hL).symm)
      (List.mem_range.mp hi')
  obtain he : Spec.Rsa.wordsAt m p.control 4 = Spec.Rsa.wordsAt s.mem p.control 4 := by
    change [word m p.control (8 * 0), word m p.control (8 * 1), word m p.control (8 * 2),
      word m p.control (8 * 3)] = [word s.mem p.control (8 * 0), word s.mem p.control (8 * 1),
      word s.mem p.control (8 * 2), word s.mem p.control (8 * 3)]
    rw [hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide)]
  refine ⟨hi, h.rd, h.wr, h.r31, h.saved, (hc 4 (by decide)).trans h.savedR31,
    (hc 7 (by decide)).trans h.usedPtr, (hc 12 (by decide)).trans h.used, (hc 14 (by decide)).trans h.status,
    he.trans h.policy, ?_⟩
  show SOutput p r m
  unfold SOutput
  rw [hbo]
  exact h.output

theorem SInput.tail_eq {p : SPub} {s : State} (h : SInput p s) : searchResult s = p.tail 0 p.attempts := by
  cases h.2
  simp only [searchResult, SPub.tail, sOfState, List.drop_zero, Proof.Ffdh.Generation.consume_zero]

theorem search_body {p : SPub} {s t : State} (c : Cand) (h : SInput p s)
    (hx : t.gpr .r31 = p.control)
    (hm : t.mem = Proof.Ffdh.Control.writeController s.mem p.control (entryValues s))
    (k : Keep entryRegs s t) (hy : t.syms = s.syms) :
    WP isa (search c.call) t fun u =>
      SDone p s (searchResult s) u ∧ u.lr = s.lr ∧ u.sp = s.sp := by
  unfold search
  refine WP.seq (WP.mono_syms (WP.keep [.r0] (Q := fun t₁ => t₁.gpr .r0 = t.lr ∧ t₁.mem = t.mem) (by
    prun [exec_mflr]) (by decide)) fun t₁ ⟨⟨h0, hm₁⟩, k₁⟩ hy₁ => ?_)
  have k' : Keep entryRegs s t₁ := k.trans' (k₁.mono (by decide))
  have hl := search_start h (by rw [k₁.gpr _ (by decide)]; exact hx) (hm₁.trans hm) k' (hy₁.trans hy)
  have hsp : 48 ≤ t₁.sp.toNat := by rw [k'.sp, ← h.sp_eq]; have := h.sp_room; omega_using [this]
  refine WP.seq (WP.mono (WP.frameRegAny (r := .r0)
    (Q := fun u => SDone p s (searchResult s) u ∧ u.gpr .r0 = s.lr ∧ u.sp = s.sp) hsp ?_ ?_ ?_)
    fun u ⟨hd, h0', hsp'⟩ => ?_)
  · intro R hR
    rw [k'.wr, h.1.2.2.2.1] at hR
    have hd := h.stack_disjoint (r := R) (List.mem_append_left _ hR)
    refine hd.sub_left ?_
    rw [k'.sp, show s.sp - 48 + 32 = s.sp - BitVec.ofNat 64 16 by bv_omega]
    exact Offset.sub_below s.sp (a := 16) (b := 336) (by decide) (by decide)
  · refine WP.mono (search_loop c (expected := searchResult s) (n := p.attempts + 1)
      ⟨0, p.attempts, rfl, hl, h.tail_eq⟩) fun u hu m uu fl => ⟨(hu.lost uu fl (by
        rw [k'.sp]; exact Offset.sub_below s.sp (a := 48) (b := 336) (by decide) (by decide))).popped _ _, ?_, k'.sp⟩
    show (u.write .r0 (t₁.gpr .r0)).gpr .r0 = _
    rw [RegUpd.gpr_write_self, h0, k.lr]
  · have := iteration_depth c
    simp only [sdepth]
    omega_using [this]
  · prun [exec_mtlr]
    exact ⟨⟨hd.input, hd.rd, hd.wr, hd.r31, hd.saved, hd.savedR31, hd.usedPtr, hd.used, hd.status, hd.policy,
      hd.output⟩, h0', hsp'⟩

theorem SReturned.post {s t : State} (h : SReturned (sOfState s) (searchResult s) t) : searchPost s t :=
  ⟨h.1, h.2.1, h.2.2.2, _, h.2.2.1, SievedGeneration.search_requests _ _ _ _⟩

theorem search_correct_ok (c : Cand) {s : State} (h : searchPre s) :
    WP isa (code c.call) s fun t => searchPost s t ∧ abiPreserved s t := by
  let p := sOfState s
  have hp : SInput p s := ⟨h, rfl⟩
  unfold code
  refine WP.seq (WP.mono_syms (entry_ok hp) fun t ⟨⟨hx, hm⟩, k⟩ hy => ?_)
  refine WP.seq (WP.mono (search_body c hp hx hm k hy) fun u ⟨hd, hlr, hsp⟩ => ?_)
  refine WP.mono (search_finish hd) fun q ⟨hr, hg, hqsp, hqlr⟩ => ?_
  exact ⟨hr.post, hg, hqsp.trans hsp, hqlr.trans hlr⟩

theorem search_correct (c : Cand) (s : State) (h : searchContract.pre s) :
    ∃ tr t, Exec isa (code c.call) s tr t ∧ abiPreserved s t ∧ searchContract.post s t := by
  obtain ⟨tr, t, he, hp, ha⟩ := search_correct_ok c h
  exact ⟨tr, t, he, ha, hp⟩

end VG.Proof.Ffdh.PPC64LE.Generation

end

end

/-! ### `Ffdh.PPC64LE.Generation.Search.CT`, which only this module used -/

section

/-! ### `Ffdh.PPC64LE.Generation.Search.LeafCT`, which only this module used -/

section

/-! # Public positions in the parameter search, its exits and its candidate (PPC64LE)

Two runs agree on the public descriptor (the tape included), the octets
consumed and the attempts left, which fix everything the search does from
there. The exits, the rejection and the request use only public addresses;
the candidate leaks only its public arguments and tape.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Spec.Ffdh
open VG.PPC64LE.Taint
open VG.Proof.Ffdh.Control (writeController)
open VG.Proof.Ffdh.PPC64LE.ParameterCandidate (pcPre pcPub pcRand)
open VG.Impl.Ffdh.PPC64LE.Generation.Search

/-- Some loop state of the search with the public descriptor `p`. -/
def SAny (p : SPub) (s : State) : Prop := ∃ original used k, SLive p original used k s

structure SPoint where
  inputs : SPub
  used : Nat
  k : Nat

def SCTL (q : SPoint) (s : State) : Prop := ∃ original, SLive q.inputs original q.used q.k s

theorem SCTL.any {q : SPoint} {s : State} (h : SCTL q s) : SAny q.inputs s :=
  let ⟨original, h⟩ := h; ⟨original, _, _, h⟩

theorem s_any_pins : Pins SAny [.r31] := by
  intro p s t ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.r31.trans h₂.r31.symm

theorem s_ctl_pins : Pins SCTL [.r31] :=
  fun _ _ _ h₁ h₂ => s_any_pins _ _ _ h₁.any h₂.any

theorem no_pins {α : Type} {Φ : α → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ h => by cases h

/-! ## Zeros at `out` and the exits -/

/-- Before the zeroing's loop: its pointer and count. -/
def SZeroCT (p : SPub) (s : State) : Prop :=
  SAny p s ∧ s.gpr .r3 = p.op ∧ s.gpr .r4 = BitVec.ofNat 64 p.len

private theorem zero_header (p : SPub) (s : State) (h : SAny p s) :
    WP isa (.block [ldf .r3 5, ldf .r4 6, .li .r5 0]) s (SZeroCT p) := by
  obtain ⟨original, used, k, h⟩ := h
  have a := h.access
  have hk : word s.mem p.control 48 = BitVec.ofNat 64 p.len :=
    h.header (j := 6) (by simp [SPub.headers])
  have hp : word s.mem p.control 40 = p.op := h.header (j := 5) (by simp [SPub.headers])
  simp only [Bignum.word, off] at hk hp
  refine WP.mono_syms (WP.keep [.r3, .r4, .r5] (Q := fun t => (t.gpr .r3 = p.op ∧
    t.gpr .r4 = BitVec.ofNat 64 p.len) ∧ t.mem = s.mem) ?_ (by decide))
    fun _ ⟨⟨hr, hm⟩, k⟩ hy => ⟨⟨original, used, _, h.keep k hm hy⟩, hr⟩
  prun [ldf, h.r31, hp, hk, a.ld 40 (by decide), a.ld 48 (by decide)]

theorem s_zero_ct : RelCT isa (Two SAny) zeroOut (fun _ _ => True) := by
  unfold zeroOut
  refine RelCT.seq (two_post (two_taint [.r31] s_any_pins (by taint_decide)) zero_header) ?_
  exact two_taint [.r3, .r4] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.trans h₂.2.2.symm]) (by taint_decide)

private theorem terminal_ready (p : SPub) (s : State) (h : SAny p s) :
    WP isa (.block (terminal 3)) s (SAny p) := by
  obtain ⟨original, used, k, h⟩ := h
  exact WP.mono (terminal_live h (.inr rfl)) fun _ ⟨ht, _⟩ => ⟨original, used, 0, ht⟩

theorem s_exhausted_ct : RelCT isa (Two SAny) exhausted (fun _ _ => True) := by
  unfold exhausted
  exact RelCT.seq (two_post (two_taint [.r31] s_any_pins (by taint_decide)) terminal_ready) s_zero_ct

theorem s_accept_ct : RelCT isa (Two SAny) (.block accept) (fun _ _ => True) :=
  two_taint [.r31] s_any_pins (by taint_decide)

theorem s_reject_ct : RelCT isa (Two SAny) (.block reject) (fun _ _ => True) :=
  two_taint [.r31] s_any_pins (by taint_decide)

theorem s_request_ct : RelCT isa (Two SAny) (.block request) (fun _ _ => True) :=
  two_taint [.r31] s_any_pins (by taint_decide)

/-! ## The candidate -/

/-- A loop state at which the controller runs a candidate. -/
def SReady (q : SPoint) (s : State) : Prop := SCTL q s ∧ q.k ≠ 0

/-- The candidate's entry, before the call. -/
def SCallCT (q : SPoint) (u : State) : Prop :=
  ∃ original s, SLive q.inputs original q.used q.k s ∧ q.k ≠ 0 ∧
    SArgs q.inputs q.used u ∧
    u.mem = writeController (allocated 112 s).mem (callSp q.inputs) (callValues q.inputs) ∧
    Keep argRegsW (allocated 112 s) u ∧ u.syms = s.syms

def SAllocated (q : SPoint) (u : State) : Prop := ∃ s, SReady q s ∧ u = allocated 112 s

theorem s_allocated_pins : Pins SAllocated [.r31] := by
  rintro q _ _ ⟨a, ⟨⟨_, h₁⟩, _⟩, rfl⟩ ⟨b, ⟨⟨_, h₂⟩, _⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.r31.trans h₂.r31.symm

private theorem arguments_ready (q : SPoint) (u : State) (h : SAllocated q u) :
    WP isa (.block arguments) u (SCallCT q) := by
  obtain ⟨s, ⟨⟨original, h⟩, hk⟩, rfl⟩ := h
  exact WP.mono_syms (search_arguments_ok h) fun _ ⟨⟨ha, hm⟩, k⟩ hy => ⟨original, s, h, hk, ha, hm, k, hy⟩

/-- What the candidate sees at its entry, in terms of the point alone. -/
private theorem call_view {q : SPoint} {u : State} (h : SCallCT q u) :
    (callState q.inputs q.used u).sp = callSp q.inputs ∧
    pcRand (callState q.inputs q.used u) = q.inputs.rand.drop q.used ∧
    SArgs q.inputs q.used (callState q.inputs q.used u) ∧
    stackArg (callState q.inputs q.used u) 0 = BitVec.ofNat 64 (q.inputs.Z / 8) ∧
    (callState q.inputs q.used u).syms VG.Impl.RsaKeyGen.TrialTable32.symbol = q.inputs.T := by
  obtain ⟨original, s, h, _, ha, hm, k, hy⟩ := h
  have hT : original.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = q.inputs.T := by rw [← h.input.2]; rfl
  have hu : u.sp = callSp q.inputs := by
    rw [k.sp]; show s.sp - BitVec.ofNat 64 112 = _; rw [h.sp]; exact callSp_eq _
  refine ⟨by simp only [State.withRegions_sp, State.callEntry_sp, hu], call_rand h hm ha, ?_,
    call_arg hu hm, by show u.syms _ = _; rw [hy]; show s.syms _ = _; rw [h.syms]; exact hT⟩
  obtain ⟨r3, r4, r5, r6, r7, r8, r9, r10⟩ := ha
  exact ⟨(call_gpr (by decide)).trans r3, (call_gpr (by decide)).trans r4, (call_gpr (by decide)).trans r5,
    (call_gpr (by decide)).trans r6, (call_gpr (by decide)).trans r7, (call_gpr (by decide)).trans r8,
    (call_gpr (by decide)).trans r9, (call_gpr (by decide)).trans r10⟩

private theorem call_pub {q : SPoint} {u₁ u₂ : State} (h₁ : SCallCT q u₁) (h₂ : SCallCT q u₂) :
    pcPub (callState q.inputs q.used u₁) (callState q.inputs q.used u₂) := by
  obtain ⟨a₁, b₁, ⟨c3, c4, c5, c6, c7, c8, c9, c10⟩, d₁, y₁⟩ := call_view h₁
  obtain ⟨a₂, b₂, ⟨e3, e4, e5, e6, e7, e8, e9, e10⟩, d₂, y₂⟩ := call_view h₂
  exact ⟨a₁.trans a₂.symm, by rw [b₁, b₂], c3.trans e3.symm, c4.trans e4.symm, c5.trans e5.symm,
    c6.trans e6.symm, by rw [c7, e7], c8.trans e8.symm, c9.trans e9.symm, c10.trans e10.symm,
    d₁.trans d₂.symm, y₁.trans y₂.symm⟩

private theorem call_ready {q : SPoint} {u : State} (h : SCallCT q u) :
    pcPre (callState q.inputs q.used u) ∧
      Covers (callRd q.inputs q.used ++ callWr q.inputs) (u.rd ++ u.wr) ∧
      Covers (callWr q.inputs) u.wr := by
  have hv := (call_view h).2.2.2.2
  obtain ⟨original, s, h, _, ha, hm, k, -⟩ := h
  have hu : u.sp = callSp q.inputs := by
    rw [k.sp]; show s.sp - BitVec.ofNat 64 112 = _; rw [h.sp]; exact callSp_eq _
  have htu : VG.Proof.Ffdh.PPC64LE.ParameterCandidate.TabAt q.inputs.T u.mem :=
    h.input.table_frame (frame_of_callChanges original (candidate_frame (t := u) h hm (fun _ _ => rfl))) h.table
  exact ⟨call_candidate_pre h.callFacts hu ha hm hv htu, call_covers_reads h k.rd k.wr,
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
  · rintro _ _ ⟨_, _, _, hsp⟩; exact hsp
  refine (RelCT.seq (two_post (two_taint [.r31] s_allocated_pins (by taint_decide)) arguments_ready)
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

end VG.Proof.Ffdh.PPC64LE.Generation

end

end

/-! # The parameter search's timing depends on its public data alone (PPC64LE)

Every branch is on the attempts left, the candidate's status and the
tape's length, which the point (the public descriptor, the octets consumed
and the attempts left) fixes.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Spec.Ffdh
open VG.PPC64LE.Taint
open VG.Proof.Ffdh.PPC64LE.ParameterCandidate (two_ite)
open VG.Proof.Ffdh.Control (writeController)
open VG.Impl.Ffdh.PPC64LE.Generation.Search

/-! ## The classification -/

theorem s_candidated_pins : Pins SCandidated [.r31] := by
  intro q s t ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.r31.trans h₂.r31.symm

/-- The candidate's status. -/
abbrev SPoint.status (q : SPoint) : Nat := candidateStatus (q.inputs.cand q.used)

/-- The status in `r9`, compared with `j` in `r12`. -/
def SGuard (j : Nat) (q : SPoint) (t : State) : Prop :=
  SCTL q t ∧ q.k ≠ 0 ∧ t.gpr .r9 = BitVec.ofNat 64 q.status ∧
    isa.eval (.zero .d .r12) t = some (decide (q.status = j))

/-- After the status and the pointer to `used` are loaded. -/
def SHead (q : SPoint) (t : State) : Prop :=
  SCandidated q t ∧ t.gpr .r11 = q.inputs.up ∧ t.gpr .r9 = BitVec.ofNat 64 q.status

private theorem head_first (q : SPoint) (s : State) (h : SCandidated q s) :
    WP isa (.block [.lsl .r9 .r3 32, .lsr .d .r9 .r9 32, ldf .r11 7]) s (SHead q) := by
  obtain ⟨original, h, hk, hp⟩ := h
  have a := h.access
  have hv7 := h.header (j := 7) (v := q.inputs.up) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv7
  have h9 := low32 hp.1
  refine WP.mono_syms (WP.keep [.r9, .r11] (Q := fun t =>
    (t.gpr .r11 = q.inputs.up ∧ t.gpr .r9 = BitVec.ofNat 64 q.status) ∧ t.mem = s.mem) ?_
    (by decide)) fun t ⟨⟨⟨h11, h9⟩, hm⟩, k⟩ hy => ?_
  · prun [ldf, h.r31, hv7, a.ld 56 (by decide), h9]
  · refine ⟨⟨original, h.keep k hm hy, hk, ?_⟩, h11, h9⟩
    unfold CandPost at hp ⊢
    rw [hm, k.gpr .r3 (by decide)]
    exact hp

theorem s_head_pins : Pins SHead [.r11] := by
  intro q s t h₁ h₂ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.2.1.trans h₂.2.1.symm

private theorem head_second (q : SPoint) (s : State) (h : SHead q s) :
    WP isa (.block [.load .d .r10 .r11 0, .subi .r12 .r9 1]) s (SGuard 1 q) := by
  obtain ⟨⟨original, h, hk, _⟩, h11, h9⟩ := h
  have hu : InRegions (s.rd ++ s.wr) (q.inputs.up + BitVec.ofNat 64 0) 8 := by
    refine ⟨⟨q.inputs.up, 8⟩, List.mem_append_right _ ?_, ?_⟩
    · rw [h.wr, h.input.1.2.2.2.1, ← h.input.used_eq]; simp [inWrites]
    · exact Offset.contains_base q.inputs.up (d := 0) (n := 8) (k := 8) (by decide) (by decide)
  have hst : q.status < 3 := status_lt (q.inputs.cand q.used)
  refine WP.mono_syms (WP.keep [.r10, .r12] (Q := fun t =>
    isa.eval (.zero .d .r12) t = some (decide (q.status = 1)) ∧ t.mem = s.mem) ?_
    (by decide)) fun t ⟨⟨he, hm⟩, k⟩ hy =>
      ⟨⟨original, h.keep k hm hy⟩, hk, (k.gpr .r9 (by decide)).trans h9, he⟩
  prun [h11, h9, hu]
  have : ∀ st < 3, ((BitVec.ofNat 64 st - BitVec.ofNat 64 1) == 0) = decide (st = 1) := by decide
  refine (eval_zero _ _).trans ?_
  rw [RegUpd.gpr_write_self, this _ hst]

private theorem second_ready (q : SPoint) (s : State)
    (h : SGuard 1 q s ∧ isa.eval (.zero .d .r12) s = some false) :
    WP isa (.block [.subi .r12 .r9 2]) s (SGuard 2 q) := by
  obtain ⟨⟨⟨o, hl⟩, hk, h9, _⟩, _⟩ := h
  refine WP.mono_syms (test_two h9 (status_lt _)) fun t ⟨⟨he, hm⟩, kt⟩ hy => ?_
  exact ⟨⟨o, hl.keep kt hm hy⟩, hk, (kt.gpr .r9 (by decide)).trans h9, he⟩

private theorem guard_eq (j : Nat) (q : SPoint) (s₁ s₂ : State) (h₁ : SGuard j q s₁)
    (h₂ : SGuard j q s₂) : isa.eval (.zero .d .r12) s₁ = isa.eval (.zero .d .r12) s₂ :=
  h₁.2.2.2.trans h₂.2.2.2.symm

private theorem leafB {α : Type} {Φ : α → State → Prop} {c : Prog isa} (f : α → SPub)
    (hΦ : ∀ q s, Φ q s → SAny (f q) s) (hc : RelCT isa (Two SAny) c fun _ _ => True) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨f q, hΦ q _ h₁, hΦ q _ h₂, hsp⟩) fun _ _ h => h

/-- Whether the tape holds the entropy cap, after a short tape. -/
def SShort (q : SPoint) (t : State) : Prop :=
  SCTL q t ∧ isa.eval (.zero .d .r5) t =
    some (decide (parameterEntropy q.inputs.bits ≤ q.inputs.randLen - q.used))

private theorem short_ready (q : SPoint) (s : State)
    (h : SGuard 2 q s ∧ isa.eval (.zero .d .r12) s = some false) :
    WP isa (.block [ldf .r3 11, ldf .r4 2, .sub .r5 .r3 .r4, .lsr .d .r5 .r5 63]) s (SShort q) := by
  obtain ⟨⟨⟨o, hl⟩, _⟩, _⟩ := h
  exact WP.mono (short_guard hl) fun t ⟨⟨ht, _⟩, he⟩ => ⟨⟨o, ht⟩, he⟩

theorem s_short_ct : RelCT isa (Two fun q s => SGuard 2 q s ∧ isa.eval (.zero .d .r12) s = some false)
    short (fun _ _ => True) := by
  unfold short
  refine RelCT.seq (two_post (two_taint [.r31] (fun q _ _ h₁ h₂ => s_ctl_pins q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide)) short_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact leafB SPoint.inputs (fun _ _ h => h.1.1.any) s_exhausted_ct
  · exact leafB SPoint.inputs (fun _ _ h => h.1.1.any) s_request_ct

theorem s_classify_ct : RelCT isa (Two SCandidated) classify (fun _ _ => True) := by
  unfold classify
  change RelCT isa (Two SCandidated) (.seq (.block ([.lsl .r9 .r3 32, .lsr .d .r9 .r9 32, ldf .r11 7] ++
    [.load .d .r10 .r11 0, .subi .r12 .r9 1])) _) _
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (two_post (two_taint [.r31] s_candidated_pins (by taint_decide)) head_first)
    (two_post (two_taint [.r11] s_head_pins (by taint_decide)) head_second))) ?_
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

theorem branch_r31 {q : SPoint} {t : State} (h : SBranchResult q t) :
    t.gpr .r31 = q.inputs.control := by
  by_cases hc : sContinues q
  · simp only [SBranchResult, hc, ite_true] at h
    obtain ⟨⟨_, hl⟩, _⟩ := h
    exact hl.r31
  · simp only [SBranchResult, hc, ite_false] at h
    obtain ⟨_, _, hd⟩ := h
    exact hd.r31

def KGuard (q : SPoint) (s : State) : Prop :=
  SCTL q s ∧ isa.eval (.zero .d .r9) s = some (decide (q.k = 0))

theorem k_ready (q : SPoint) (s : State) (h : SCTL q s) :
    WP isa (.block [ldf .r9 0]) s (KGuard q) := by
  obtain ⟨original, h⟩ := h
  exact WP.mono (attempts_guard h) fun _ ⟨ht, he⟩ => ⟨⟨original, ht⟩, he⟩

/-- The branch of an iteration. -/
abbrev sBranch (c : Cand) : Prog isa := .ite (.zero .d .r9) exhausted (.seq (candidateRun c.call) classify)

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
  have hr : ∀ q s, KGuard q s ∧ isa.eval (.zero .d .r9) s = some false → SReady q s :=
    fun q s ⟨⟨hl, he⟩, hf⟩ => ⟨hl, of_decide_eq_false (Option.some.inj (he.symm.trans hf))⟩
  exact RelCT.seq (two_post ((s_candidate_run_ct c).mono
      (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, hr q _ h₁, hr q _ h₂, hsp⟩) fun _ _ h => h)
    fun q s h => s_candidate_ready c q s (hr q s h)) s_classify_ct

theorem s_iteration_ct (c : Cand) :
    RelCT isa (Two SCTL) (iteration c.call) (fun _ _ => True) := by
  unfold iteration
  refine RelCT.seq (two_post (two_taint [.r31] s_ctl_pins (by taint_decide)) k_ready) ?_
  exact RelCT.seq (two_post (s_branch_ct c) (s_branch_ready c))
    (two_taint [.r31] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact (branch_r31 h₁).trans (branch_r31 h₂).symm) (by taint_decide))

def SCTStep (q : SPoint) (s : State) : Prop :=
  if sContinues q then isa.eval (.zero .d .r9) s = some true ∧ SCTL (nextPoint q) s
  else isa.eval (.zero .d .r9) s = some false

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
      isa.eval (.zero .d .r9) s = isa.eval (.zero .d .r9) t ∧
      (isa.eval (.zero .d .r9) s = some false → True) ∧
      (isa.eval (.zero .d .r9) s = some true → ∃ m < n, LoopPair m s t) := by
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
    RelCT isa (Two SCTL) (.loop (iteration c.call) (.zero .d .r9)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht, hsp⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration c.call) (c := .zero .d .r9)
    (Q := fun _ _ => True) LoopPair (iteration_pair c) (q.k + 1)
    _ _ _ _ _ _ ⟨q, rfl, hs, ht, hsp⟩ he₁ he₂

end VG.Proof.Ffdh.PPC64LE.Generation

end

end

/-! # The parameter search is constant time for its public data (PPC64LE) -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Spec.Ffdh
open VG.Proof.Ffdh.Control (writeController)
open VG.Impl.Ffdh.PPC64LE.Generation.Search

/-! ## The frame saving `r0` -/

/-- A frame saving `r0` around a body proven with the permissions outside
it (as `WP.frameRegAny` runs it) leaks what the body does there: the body's
run in the frame is that run, with more permissions (`Exec.widen`). -/
theorem relCT_pushR0 {body : Prog isa} {P : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp)
    (hwp : ∀ a b, P a b → (∃ t s', Exec isa body (framed .r0 a) t s') ∧
      (∃ t s', Exec isa body (framed .r0 b) t s'))
    (hct : RelCT isa (fun x y => ∃ a b, P a b ∧ x = framed .r0 a ∧ y = framed .r0 b) body
      fun _ _ => True) :
    RelCT isa P (.frame (.push .r0) body (.pop .r0)) fun a b => a.sp = b.sp := by
  refine RelCT.frame (R := fun _ _ => True) hsp ?_
  have widen : ∀ a, ∀ {t s'}, Exec isa body (framed .r0 a) t s' →
      Exec isa body (pushed .r0 a) t (s'.withRegions a.rd (⟨a.sp - 48 + 32, 16⟩ :: a.wr)) := by
    intro a t s' e
    have := Exec.widen e (rd := a.rd) (wr := ⟨a.sp - 48 + 32, 16⟩ :: a.wr)
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
    WP isa (.block (entry.take 2)) s fun t =>
      t.gpr .r12 = p.control ∧ t.gpr .r11 = p.sp + BitVec.ofNat 64 96 := by
  have hd : s.mem.readW (s.sp + BitVec.ofNat 64 104) 64 = p.control := by
    rw [← congrArg SPub.control h.2]
    simp only [sOfState, stackArg, stackArgAddr, Nat.reduceMul, Nat.reduceAdd]
  have ha1 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 104) 8 := by
    rw [← VG.Offset.add_add_eq s.sp (show 96 + 8 = 104 by rfl)]; exact input_args h 1 (by decide)
  have ea : exec (.addSp .r11 96) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 96)) := by
    simp [exec]
  unfold entry
  simp only [List.take_succ_cons, List.take_zero]
  prun [ea, hd, ha1, h.sp_eq]

theorem pins_E2 : Pins (fun (p : SPub) (t : State) => t.gpr .r12 = p.control ∧ t.gpr .r11 = p.sp + BitVec.ofNat 64 96)
    [.r11, .r12] := by
  rintro p s t ⟨a12, a11⟩ ⟨b12, b11⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a11, b11]
  · rw [a12, b12]

private theorem entry_ct : RelCT isa (Two SInput) (.block entry) (fun _ _ => True) := by
  change RelCT isa (Two SInput) (.block (entry.take 2 ++ entry.drop 2)) _
  exact RelCT.block_append (RelCT.seq (two_post (two_taint [] no_pins (by taint_decide)) entry_pointer)
    (two_taint _ pins_E2 (by taint_decide)))

/-- After the entry: the controller's words written. -/
def SEntered (p : SPub) (t : State) : Prop :=
  ∃ s, SInput p s ∧ t.gpr .r31 = p.control ∧
    t.mem = writeController s.mem p.control (entryValues s) ∧ Keep entryRegs s t ∧ t.syms = s.syms

private theorem entry_ready (p : SPub) (s : State) (h : SInput p s) :
    WP isa (.block entry) s (SEntered p) :=
  WP.mono_syms (entry_ok h) fun _ ⟨⟨hx, hm⟩, k⟩ hy => ⟨s, h, hx, hm, k, hy⟩

private theorem entered_ctl {p : SPub} {t : State} (h : SEntered p t) :
    SCTL ⟨p, 0, p.attempts⟩ (framed .r0 t) := by
  obtain ⟨s, hi, hx, hm, k, hy⟩ := h
  exact ⟨s, search_start hi hx hm k hy⟩

/-- `mflr r0` keeps the state after the entry. -/
private theorem mflr_ready (p : SPub) (t : State) (h : SEntered p t) :
    WP isa (.block [.mflr .r0]) t (SEntered p) := by
  obtain ⟨s, hi, hx, hm, k, hy⟩ := h
  refine WP.mono_syms (WP.keep [.r0] (Q := fun u => u.mem = t.mem) (by prun [exec_mflr]) (by decide))
    fun u ⟨hu, ku⟩ hyu => ⟨s, hi, (ku.gpr _ (by decide)).trans hx, hu.trans hm, k.trans' (ku.mono (by decide)),
      hyu.trans hy⟩

def SCTDone (p : SPub) (s : State) : Prop := ∃ original r, SDone p original r s

private theorem frame_ct (c : Cand) : RelCT isa (Two SEntered)
    (.frame (.push .r0) (.loop (iteration c.call) (.zero .d .r9)) (.pop .r0)) fun a b => a.sp = b.sp := by
  refine relCT_pushR0 (fun _ _ ⟨_, _, _, hsp⟩ => hsp) (fun x y ⟨q, h₁, h₂, _⟩ => ?_) ?_
  · obtain ⟨original, hl⟩ := entered_ctl h₁
    obtain ⟨original', hl'⟩ := entered_ctl h₂
    obtain ⟨t, s', e, -⟩ := search_loop c (n := q.attempts + 1) (expected := q.tail 0 q.attempts)
      ⟨0, _, rfl, hl, rfl⟩
    obtain ⟨t', s'', e', -⟩ := search_loop c (n := q.attempts + 1) (expected := q.tail 0 q.attempts)
      ⟨0, _, rfl, hl', rfl⟩
    exact ⟨⟨t, s', e⟩, ⟨t', s'', e'⟩⟩
  · refine (s_loop_ct c).mono ?_ fun _ _ h => h
    rintro _ _ ⟨x, y, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
    exact ⟨⟨q, 0, q.attempts⟩, entered_ctl h₁, entered_ctl h₂, by simp only [framed, hsp]⟩

private theorem search_ct (c : Cand) : RelCT isa (Two SEntered) (search c.call) (fun _ _ => True) := by
  unfold search
  refine RelCT.seq (two_post (two_taint [] no_pins (by taint_decide)) mflr_ready) (RelCT.seq (frame_ct c) ?_)
  exact (two_taint (Φ := fun (_ : Unit) (_ : State) => True) [] no_pins (by taint_decide)).mono
    (fun _ _ hsp => ⟨(), trivial, trivial, hsp⟩) fun _ _ h => h

private theorem search_ready (c : Cand) (p : SPub) (t : State) (h : SEntered p t) :
    WP isa (search c.call) t (SCTDone p) := by
  obtain ⟨s, hi, hx, hm, k, hy⟩ := h
  exact WP.mono (search_body c hi hx hm k hy) fun _ ⟨hd, _, _⟩ => ⟨s, _, hd⟩

private theorem finish_pointer (p : SPub) (s : State) (h : SCTDone p s) :
    WP isa (.block (finish.take 3)) s fun t => t.gpr .r4 = p.up ∧ t.gpr .r31 = p.control := by
  obtain ⟨original, r, h⟩ := h
  have scr := h.input.control_scr (t := s) h.wr
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hu := h.usedPtr
  simp only [Bignum.word, off] at hu
  unfold finish
  simp only [List.take_succ_cons, List.take_zero]
  prun [ldf, h.r31, hu, hl 56 (by decide), hl 96 (by decide), hl 112 (by decide)]

private theorem finish_ct : RelCT isa (Two SCTDone) (.block finish) (fun _ _ => True) := by
  change RelCT isa (Two SCTDone) (.block (finish.take 3 ++ finish.drop 3)) _
  refine RelCT.block_append (RelCT.seq (two_post (two_taint [.r31] ?_ (by taint_decide)) finish_pointer) ?_)
  · intro p s t ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.r31.trans h₂.r31.symm
  · exact two_taint [.r4, .r31] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

theorem search_code_ct (c : Cand) : RelCT isa (Two SInput) (code c.call) (fun _ _ => True) := by
  unfold code
  exact RelCT.seq (two_post entry_ct entry_ready)
    (RelCT.seq (two_post (search_ct c) (search_ready c)) finish_ct)

private theorem s_public_descriptor {s t : State} (h : searchPub s t) : sOfState s = sOfState t := by
  obtain ⟨hsp, hr, hw, r3, r4, r5, r6, r7, r8, r9, r10, a0, a1, hy⟩ := h
  have h0 : s.mem.readW (stackArg s 1) 64 = t.mem.readW (stackArg t 1) 64 := by
    change [word s.mem (stackArg s 1) 0, word s.mem (stackArg s 1) 8, word s.mem (stackArg s 1) 16,
      word s.mem (stackArg s 1) 24] = [word t.mem (stackArg t 1) 0, word t.mem (stackArg t 1) 8,
        word t.mem (stackArg t 1) 16, word t.mem (stackArg t 1) 24] at hw
    simpa only [Bignum.word, off, BitVec.add_zero] using (List.cons.inj hw).1
  have hrand : genRand s = genRand t := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hr
  unfold sOfState
  rw [genAttempts, genAttempts, h0, hrand, hsp, r3, r5, r8, r10, genLen, genLen, r4, genBits, genBits, r6,
    genGen, genGen, r7, r9, a0, a1, hy]

theorem search_constantTime (c : Cand) :
    ConstantTime isa searchContract.pre searchContract.pub (code c.call) := by
  refine RelCT.constantTime ((search_code_ct c).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨sOfState s, ⟨hs, rfl⟩, ⟨ht, (s_public_descriptor hp).symm⟩, hp.1⟩

end VG.Proof.Ffdh.PPC64LE.Generation
