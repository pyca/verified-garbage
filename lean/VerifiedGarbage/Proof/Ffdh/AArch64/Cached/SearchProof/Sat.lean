module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Writes
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SatWitness
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import Batteries.Logic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
meta import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Loop
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Loop
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Writes
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.AttemptInput
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.NativeTimingState
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.AttemptInput
meta import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.NativeTimingState
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Search
meta import VerifiedGarbage.Impl.Ffdh.AArch64.KeyGeneration.Search
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Search
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-! ### `Ffdh.AArch64.Cached.SearchProof.CT`, which the modules that import this one used -/

section

/-! ### `Ffdh.AArch64.Cached.SearchProof.Correct`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.SearchProof.Start`, which this module and modules that import it used -/

section

/-! # After its entry, in the frame saving `x30`, the controller is at the tape's start -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.Control (writeController writeController_frame writeController_word
  controllerValue)

/-- The state the body of the frame saving `x30` starts in (`WP.frameReg`). -/
abbrev pushedX30 (t : State) : State :=
  { t with sp := t.sp - 16, mem := t.mem.write (t.sp - 16) 8 (t.gpr .x30) }

private theorem word_zero (m : Mem) (B : Addr) : word m B 0 = m.readW B 64 := by
  simp only [Bignum.word, off, BitVec.add_zero]

theorem KeyInput.width_word {p : KeyPublic} {s : State} (h : KeyInput p s) :
    s.mem.readW (stackArg s 4 + 16) 64 = BitVec.ofNat 64 (keyLen s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hw, -, -⟩ := h.1
  exact hw

theorem entry_headers {p : KeyPublic} {s : State} (h : KeyInput p s) :
    Slots (writeController s.mem p.control (entryValues s)) p.control
      (p.headers 0 p.keys p.scalars) := by
  have hw := h.width_word
  cases h.2
  intro e he
  simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [writeController_word _ _ _ (entryValues_bound s) _ (by dsimp only; decide)] <;>
    simp only [keyOfState, controllerValue, entryValues,
      List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ite_true, ite_false,
      Nat.sub_zero, Nat.mul_zero, BitVec.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      Nat.mul_div_cancel _ (by decide : 0 < 8), word_zero]
  · simp only [Bignum.word, off]
    rfl
  · simp only [Bignum.word, off, Nat.reduceMul]
    exact hw.trans (by simp only [keyLen, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  all_goals rfl

/-- The push of `x30` writes only below the stack pointer. -/
theorem push_frame {p : KeyPublic} {s : State} (h : KeyInput p s) (m : Mem) (v : BitVec 64) :
    Frame (KeyInput.callChanges s) m (m.write (s.sp - 16) 8 v) := by
  refine Frame.write (Frame.refl _ _) (r := below s.sp stackUse)
    (by simp [KeyInput.callChanges]) _ ?_
  have := h.1.2.1
  exact Offset.contains_below s.sp (a := 16) (b := 64) (by decide) (by decide) (by decide)

theorem key_start {p : KeyPublic} {s t : State} (h : KeyInput p s)
    (hx : t.gpr .x19 = p.control) (hm : t.mem = writeController s.mem p.control (entryValues s))
    (k : Keep [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x19] s t) :
    KeyLive p s 0 p.keys p.scalars (pushedX30 t) := by
  have hf := writeController_frame s.mem p.control (entryValues s) (entryValues_bound s)
  have hf₁ : Frame (KeyInput.changes s) s.mem t.mem := by
    rw [hm]
    exact hf.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨inCtl s, by simp [KeyInput.changes, inWrites], by rw [← h.2]; exact fun _ hi => hi⟩
  have hp := push_frame h t.mem (t.gpr .x30)
  rw [← k.sp] at hp
  have hf₂ : Frame (KeyInput.changes s) s.mem (pushedX30 t).mem :=
    hf₁.trans (frame_of_callChanges s hp)
  have hc (j : Nat) (hj : j < 16) : word (pushedX30 t).mem p.control (8 * j) = word t.mem p.control (8 * j) :=
    h.control_frame hp j hj
  refine ⟨h, Nat.zero_le _, h.keys_le, h.scalars_le, k.rd, k.wr, ?_, hx, ?_, k.vcs, ?_, ?_, ?_, ?_,hf₂⟩
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
  · rw [h.domain_frame hf₂]
    cases h.2
    rfl
  · intro e he
    rw [hc e.1 (KeyPublic.headers_index he), hm]
    exact entry_headers h e he

end VG.Proof.Ffdh.AArch64.Cached.SearchProof

end

end

/-! # The key-generation controller's correctness (AArch64)

The loop runs in the frame saving `x30` (`WP.frameReg`); `finish` then
stores the octets consumed, returns the status and restores `x19`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.GenerationSearch
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search (ldf stf terminal zeroOut zeroOutputs exhausted advance rejectedScalar rejectedPublic test classify request room entry arguments finish)
open VG.Impl.Ffdh.AArch64.Cached.Search

/-! ## Returning -/

theorem KeyInput.used_scr {p : KeyPublic} {s : State} (h : KeyInput p s) {t : State}
    (hw : t.wr = s.wr) : Scr t p.up 8 := by
  refine Scr.of_mem (by rw [hw, h.1.2.2.2.1, ← h.2]; simp [inWrites, inUsed, keyOfState]) ?_
  rw [← h.2]
  exact h.nowrap (r := inUsed s) (by simp [inWrites])

/-- The word for the octets consumed is apart from the outputs and the
controller's words. -/
theorem KeyInput.used_disjoint {p : KeyPublic} {s : State} (h : KeyInput p s) :
    (⟨p.xp, p.len⟩ : Region).Disjoint ⟨p.up, 8⟩ ∧ (⟨p.yp, p.len⟩ : Region).Disjoint ⟨p.up, 8⟩ ∧
      (⟨p.control, 128⟩ : Region).Disjoint ⟨p.up, 8⟩ := by
  have hpw := h.writes_pairwise
  simp only [inWrites, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hpw
  have hu : inUsed s = ⟨p.up, 8⟩ := by rw [← h.2]; rfl
  have hc : inCtl s = ⟨p.control, 128⟩ := by rw [← h.2]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← h.x_eq, ← hu]; exact hpw.1.2.1
  · rw [← h.y_eq, ← hu]; exact hpw.2.1.1
  · rw [← hc, ← hu]; exact hpw.2.2.1.2.symm

theorem key_finish_values {p : KeyPublic} {original s : State} {result : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original result s) :
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
  brun [ldf, h.x19, hu, hd, hs, hx, hup, hl 120 (by decide), hl 88 (by decide), hl 112 (by decide),
    hl 32 (by decide)]

/-- What the search returns, for its result. -/
def KeyReturned (p : KeyPublic) (result : Spec.Ffdh.KeySearchResult) (t : State) : Prop :=
  ((t.gpr .x0).setWidth 32).toNat = result.status ∧ KeyOutput p result t.mem ∧
    Spec.Rsa.wordsAt t.mem p.control 4 = p.policy result ∧
    Spec.Rsa.wordsAt t.mem p.up 1 = [BitVec.ofNat 64 result.used]

theorem key_finish {p : KeyPublic} {original s : State} {result : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original result s) :
    WP isa (.block finish) s fun t => KeyReturned p result t ∧
      (∀ reg ∈ preserved, reg ≠ .x30 → t.gpr reg = original.gpr reg) ∧ t.sp = s.sp ∧ t.gpr .x30 = s.gpr .x30 ∧
      (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (original.v r).extractLsb' 0 64) := by
  refine WP.mono (key_finish_values h) fun t ⟨⟨ha, hr19, hm⟩, k⟩ => ?_
  have hd := h.input.used_disjoint
  have hk := h.input.len_lt
  have hf : Frame [⟨p.up, 8⟩] s.mem t.mem := by
    rw [hm]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hb : ∀ q : Addr, (⟨q, p.len⟩ : Region).Disjoint ⟨p.up, 8⟩ →
      Spec.Rsa.bytesAt t.mem q p.len = Spec.Rsa.bytesAt s.mem q p.len := by
    intro q hq
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hq)
      (show p.len ≤ 2 ^ 64 by omega_using [hk]) (List.mem_range.mp hi)
  have hc (j : Nat) (hj : j < 4) : word t.mem p.control (8 * j) = word s.mem p.control (8 * j) :=
    hf.readW (r := ⟨p.control, 128⟩)
      (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hd.2.2) (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, k.sp, k.gpr .x30 (by decide), fun r hr => (k.vcs r hr).trans (h.vcs r hr)⟩
  · rw [ha]
    have : result.status < 4 := by unfold Spec.Ffdh.KeySearchResult.status; split <;> decide
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [this]
  · have ho := h.output
    unfold KeyOutput at ho ⊢
    rw [hb _ hd.1, hb _ hd.2.1]
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

theorem iteration_depth (a : Attempt) : (iteration a.call).aarch64Depth = 3 := by
  simp only [iteration, branch, attemptOrRequest, attemptRun, Code.aarch64Depth, Attempt.call,
    a.depth, Instr.frameUnits]
  rfl

/-- After the frame: a finished search, with `x30` and the stack pointer back. -/
theorem KeyDone.popped {p : KeyPublic} {original s : State} {r : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original r s) (v sp : BitVec 64) :
    KeyDone p original r { s.write .x .x30 v with sp := sp } := by
  refine ⟨h.input, h.rd, h.wr, ?_, fun reg hr h19 h30 => ?_, h.vcs, h.savedX19, h.usedPtr, h.used,
    h.status, h.policy, h.output⟩
  · show (s.write .x .x30 v).gpr .x19 = _
    rw [RegUpd.gpr_write]; exact h.x19
  · show (s.write .x .x30 v).gpr reg = _
    rw [RegUpd.gpr_write, ite_eq_right h30]; exact h.saved reg hr h19 h30

/-- After the frame, whose slot is lost: a finished search, with `x30` and the
stack pointer back. -/
theorem KeyDone.released {p : KeyPublic} {original s : State} {r : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original r s) (v sp : BitVec 64) {m : Mem} (u : Nat → BitVec 64)
    (hf : Frame [below original.sp stackUse] s.mem m) :
    KeyDone p original r { s.write .x .x30 v with sp := sp, mem := m, unknowns := u } := by
  have h' := h.popped v sp
  have hc := h.input.control_frame (hf.sub fun R hR => ⟨R, by
    obtain rfl := List.mem_singleton.mp hR; simp [KeyInput.callChanges], fun _ hi => hi⟩)
  rw [← h.input.sp_eq] at hf
  have hx := fun {i} (hi : i < p.len) => lost_byte (i := i) hf h.input.outStack.1 hi
  have hy := fun {i} (hi : i < p.len) => lost_byte (i := i) hf h.input.outStack.2 hi
  refine ⟨h'.input, h'.rd, h'.wr, h'.x19, h'.saved, h'.vcs, (hc 4 (by decide)).trans h.savedX19,
    (hc 15 (by decide)).trans h.usedPtr, (hc 11 (by decide)).trans h.used,
    (hc 14 (by decide)).trans h.status,
    (List.map_congr_left fun i hi => hc i (by have := List.mem_range.mp hi; omega_using [this])).trans
      h.policy, ?_⟩
  have ex : Spec.Rsa.bytesAt m p.xp p.len = Spec.Rsa.bytesAt s.mem p.xp p.len :=
    List.map_congr_left fun i hi => hx (List.mem_range.mp hi)
  have ey : Spec.Rsa.bytesAt m p.yp p.len = Spec.Rsa.bytesAt s.mem p.yp p.len :=
    List.map_congr_left fun i hi => hy (List.mem_range.mp hi)
  have ho := h.output
  unfold KeyOutput at ho ⊢
  change (match r.outcome with
    | .accepted sx sy => Spec.Rsa.bytesAt m p.xp p.len = _ ∧ Spec.Rsa.bytesAt m p.yp p.len = _
    | _ => Spec.Rsa.bytesAt m p.xp p.len = _ ∧ Spec.Rsa.bytesAt m p.yp p.len = _)
  rw [ex, ey]
  exact ho

theorem key_search {p : KeyPublic} {s t : State} (a : Attempt) (h : KeyInput p s)
    (hx : t.gpr .x19 = p.control)
    (hm : t.mem = Proof.Ffdh.Control.writeController s.mem p.control (entryValues s))
    (k : Keep [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x19] s t) :
    WP isa (search a.call) t fun u => ∃ r, r.outcome = (keyResult s).outcome ∧
      r.used = (keyResult s).used ∧ KeyDone p s r u ∧ u.gpr .x30 = s.gpr .x30 ∧ u.sp = s.sp := by
  have hl := key_start h hx hm k
  have hsp : 16 ≤ t.sp.toNat := by rw [k.sp, ← h.sp_eq]; have := h.sp_room; omega_using [this]
  unfold search
  refine WP.frameReg hsp ?_ ?_ ?_
  · intro R hR
    rw [k.wr, h.1.2.2.2.1] at hR
    have hd := h.stack_disjoint (r := R) (List.mem_append_left _ hR)
    refine hd.sub_left ?_
    rw [k.sp]
    exact Offset.sub_below s.sp (a := 16) (b := 64) (by decide) (by decide)
  · have hinit : keyResult s = p.tail (keyRand s) 0 p.keys p.scalars := by
      cases h.2
      simp only [keyResult, KeyPublic.tail, keyTail, after, keyOfState, KeyPublic.a, List.drop_zero,
        Nat.zero_add,VG.Proof.Ffdh.GenerationPolicy.search]
    refine WP.mono (key_loop a (expected := keyResult s) (n := 128 * p.keys + p.scalars + 1)
      ⟨0, p.keys, p.scalars, rfl, hl, by rw [hinit], by rw [hinit]⟩) fun u hu m uu f => ?_
    refine ⟨keyResult s, rfl, rfl, hu.released _ _ uu (f.sub fun R hR => ⟨_, List.mem_singleton_self _, ?_⟩),
      ?_, k.sp⟩
    · obtain rfl := List.mem_singleton.mp hR
      rw [k.sp]
      exact Offset.sub_below s.sp (a := 16) (b := 64) (by decide) (by decide)
    show (u.write .x .x30 (t.gpr .x30)).gpr .x30 = _
    rw [RegUpd.gpr_write, ite_eq_left rfl]
    exact k.gpr .x30 (by decide)
  · show 16 * (iteration a.call).aarch64Depth + 16 < 2 ^ 64
    rw [iteration_depth a]; decide

theorem key_correct_ok (a : Attempt) {s : State} (h : keyPre s) :
    WP isa (code a.call) s fun t => keyPost s t ∧ abiPreserved s t := by
  let p := keyOfState s
  have hp : KeyInput p s := ⟨h, rfl⟩
  unfold code
  refine WP.seq (WP.mono (entry_ok hp) fun t ⟨⟨hx, hm⟩, k⟩ => ?_)
  refine WP.seq (WP.mono (key_search a hp hx hm k) fun u ⟨r, ho, hu, hd, h30, hsp⟩ => ?_)
  refine WP.mono (key_finish (hd.congr ho hu)) fun q ⟨hr, hg, hqsp, hq30, hv⟩ => ?_
  refine ⟨hr, fun reg hreg => ?_, hqsp.trans hsp, hv⟩
  by_cases h30 : reg = .x30
  · subst h30; exact hq30.trans h30
  · exact hg reg hreg h30

theorem key_correct (a : Attempt) (s : State) (h : keyContract.pre s) :
    ∃ tr t, Exec isa (code a.call) s tr t ∧ abiPreserved s t ∧ keyContract.post s t := by
  obtain ⟨tr, t, he, hp, ha⟩ := key_correct_ok a h
  exact ⟨tr, t, he, ha, hp⟩

end VG.Proof.Ffdh.AArch64.Cached.SearchProof

end

end

/-! ### `Ffdh.AArch64.Cached.SearchProof.BranchCT`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.SearchProof.AttemptCT`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.SearchProof.LeafCT`, which only this module used -/

section

/-! # Public positions in the key search, and its exits and rejections (AArch64)

Two runs agree on the public descriptor, the octets consumed, the budgets
left and the statuses of the attempts still to come, which the search from
there gives for each run's own tape. The exits and rejections use only
public addresses.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search (ldf stf terminal zeroOut zeroOutputs exhausted advance rejectedScalar rejectedPublic test classify request room entry arguments finish)
open VG.Impl.Ffdh.AArch64.Cached.Search

/-- Some loop state of the search with the public descriptor `p`. -/
def KeyAny (p : KeyPublic) (s : State) : Prop :=
  ∃ original used keys scalars, KeyLive p original used keys scalars s

structure KeyPoint where
  inputs : KeyPublic
  used : Nat
  keys : Nat
  scalars : Nat
  statuses : List Nat

def KeyCTL (q : KeyPoint) (s : State) : Prop :=
  ∃ original, KeyLive q.inputs original q.used q.keys q.scalars s ∧
    (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses

theorem KeyCTL.any {q : KeyPoint} {s : State} (h : KeyCTL q s) : KeyAny q.inputs s :=
  let ⟨original, h, _⟩ := h; ⟨original, _, _, _, h⟩

theorem key_any_pins : Pins KeyAny [.x19] := by
  intro p s t ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.x19.trans h₂.x19.symm

theorem key_ctl_pins : Pins KeyCTL [.x19] :=
  fun _ _ _ h₁ h₂ => key_any_pins _ _ _ h₁.any h₂.any

/-! ## Zeros at the outputs -/

/-- Before a zeroing's loop: its pointer and count. -/
def KeyZeroCT (j : Nat) (p : KeyPublic) (s : State) : Prop :=
  KeyAny p s ∧ s.gpr .x1 = (if j = 5 then p.xp else p.yp) + BitVec.ofNat 64 0 ∧
    s.gpr .x2 = BitVec.ofNat 64 p.len

private theorem zero_header (j : Nat) (hj : j = 5 ∨ j = 6) (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block [ldf .x1 j, ldf .x2 2, Impl.Bignum.AArch64.movi .x3 0]) s (KeyZeroCT j p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  have a := h.access
  have hk : word s.mem p.control 16 = BitVec.ofNat 64 p.len :=
    h.header (j := 2) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off] at hk
  refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => (t.gpr .x1 = (if j = 5 then p.xp else p.yp) +
    BitVec.ofNat 64 0 ∧ t.gpr .x2 = BitVec.ofNat 64 p.len) ∧ t.mem = s.mem) ?_ (by rcases hj with rfl | rfl <;> decide)
      (by rcases hj with rfl | rfl <;> decide) (by rcases hj with rfl | rfl <;> decide +kernel))
    fun _ ⟨⟨hr, hm⟩, k⟩ => ⟨⟨original, used, keys, scalars, h.keep k hm⟩, hr⟩
  rcases hj with rfl | rfl
  · have hp : word s.mem p.control 40 = p.xp := h.header (j := 5) (by simp [KeyPublic.headers])
    simp only [Bignum.word, off] at hp
    brun [ldf, h.x19, hp, hk, a.ld 40 (by decide), a.ld 16 (by decide), imm64 (show 0 < 65536 by decide)]
  · have hp : word s.mem p.control 48 = p.yp := h.header (j := 6) (by simp [KeyPublic.headers])
    simp only [Bignum.word, off] at hp
    brun [ldf, h.x19, hp, hk, a.ld 48 (by decide), a.ld 16 (by decide), imm64 (show 0 < 65536 by decide)]

private theorem zero_ct (j : Nat) (hj : j = 5 ∨ j = 6) :
    RelCT isa (Two KeyAny) (zeroOut j) (fun _ _ => True) := by
  rcases hj with rfl | rfl <;> unfold zeroOut <;>
  · refine RelCT.seq (two_piece [.x19] key_any_pins (by taint_decide) (zero_header _ (by decide))) ?_
    exact two_taint [.x1, .x2] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.trans h₂.2.2.symm]) (by taint_decide)

private theorem zero_ready (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (zeroOut 5) s (KeyAny p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  exact WP.mono (key_zero_out h (j := 5) (.inl rfl) (by simp [KeyPublic.headers]) h.input.x_mem
    h.input.x_ne_ctl) fun _ ⟨ht, _⟩ => ⟨original, used, keys, scalars, ht⟩

theorem key_zero_outputs_ct : RelCT isa (Two KeyAny) zeroOutputs (fun _ _ => True) := by
  unfold zeroOutputs
  exact RelCT.seq (two_post (zero_ct 5 (.inl rfl)) zero_ready) (zero_ct 6 (.inr rfl))

private theorem terminal_ready (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block (terminal 3)) s (KeyAny p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  exact WP.mono (key_terminal_live h (.inr rfl)) fun _ ⟨ht, _⟩ => ⟨original, used, 0, 0, ht⟩

theorem key_exhausted_ct : RelCT isa (Two KeyAny) exhausted (fun _ _ => True) := by
  unfold exhausted
  exact RelCT.seq (two_piece [.x19] key_any_pins (by taint_decide) terminal_ready)
    key_zero_outputs_ct

private theorem request_ready (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block [ldf .x10 2, Impl.Bignum.AArch64.movi .x11 0, stf .x10 3, stf .x11 14]) s (KeyAny p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  exact WP.mono (key_request_live h) fun _ ⟨ht, _⟩ => ⟨original, used, keys, scalars, ht⟩

theorem key_request_ct : RelCT isa (Two KeyAny) request (fun _ _ => True) := by
  unfold request
  exact RelCT.seq (two_piece [.x19] key_any_pins (by taint_decide) request_ready)
    key_zero_outputs_ct

theorem key_accepted_ct : RelCT isa (Two KeyAny) (.block (terminal 1)) (fun _ _ => True) :=
  two_taint [.x19] key_any_pins (by taint_decide)

theorem key_rejected_scalar_ct : RelCT isa (Two KeyAny) (.block rejectedScalar) (fun _ _ => True) :=
  two_taint [.x19] key_any_pins (by taint_decide)

theorem key_rejected_public_ct : RelCT isa (Two KeyAny) (.block rejectedPublic) (fun _ _ => True) :=
  two_taint [.x19] key_any_pins (by taint_decide)

end VG.Proof.Ffdh.AArch64.Cached.SearchProof

end

end

/-! ### `Ffdh.AArch64.Cached.AttemptTiming`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.GenerateNativeTiming`, which only this module used -/

section

/-! Complete cached-attempt timing, including its original register and stack arguments. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

def EntryLoaded (q : FrontPublic) (s : State) : Prop :=
 s.gpr .x0=q.body.scalar.p.src ∧ s.gpr .x2=q.body.yp ∧ s.gpr .x4=q.body.scalar.dp ∧
 s.gpr .x5=BitVec.ofNat 64 q.body.scalar.dl ∧ s.gpr .x6=BitVec.ofNat 64 q.body.scalar.p.k ∧
 s.gpr .x7=q.rp ∧ s.gpr .x8=q.body.scalar.p.B ∧ s.gpr .x9=q.body.scalar.p.ctx

theorem generateEntry_ct : RelCT isa (Two NativeReady) (.block Generate.entry) (fun _ _ =>True) := by
 change RelCT isa (Two NativeReady) (.block ((Generate.entry.take 2)++(Generate.entry.drop 2))) _
 apply RelCT.block_append
 refine RelCT.seq (two_piece (Ψ:=EntryLoaded) [] (fun _ _ _ _ _ r hr =>by simp at hr) (by taint_decide) ?_)
  (two_taint [.x0,.x2,.x4,.x5,.x6,.x7,.x8,.x9] ?_ (by taint_decide))
 · rintro q s ⟨rb,h⟩
   change WP isa (.block [.ldrSp .x8 8,.ldrSp .x9 24]) s _
   brun [exec_ldrSp_x' _ (show 8%8=0 ∧ 8<32768 by decide) h.stackB,
    exec_ldrSp_x' (s.write .x .x8 q.body.scalar.p.B) (show 24%8=0 ∧ 24<32768 by decide)
     (by simpa only [RegUpd.rd_write,RegUpd.wr_write,RegUpd.sp_write] using h.stackCtx),
    h.readB,h.readCtx,h.xArg,h.yArg,h.domArg,h.dlArg,h.lenArg,h.randArg]
   simp [EntryLoaded,RegUpd.gpr_write,h.xArg,h.yArg,h.domArg,h.dlArg,h.lenArg,h.randArg]
 · intro q s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.1.trans ht.2.1.symm
   · exact hs.2.2.1.trans ht.2.2.1.symm
   · exact hs.2.2.2.1.trans ht.2.2.2.1.symm
   · exact hs.2.2.2.2.1.trans ht.2.2.2.2.1.symm
   · exact hs.2.2.2.2.2.1.trans ht.2.2.2.2.2.1.symm
   · exact hs.2.2.2.2.2.2.1.trans ht.2.2.2.2.2.2.1.symm
   · exact hs.2.2.2.2.2.2.2.trans ht.2.2.2.2.2.2.2.symm

theorem generateNative_ct (M : Mont) : RelCT isa (Two NativeReady) (Generate.code M.mm) (fun _ _ =>True) := by
 change RelCT isa (Two NativeReady) (.seq (.block Generate.entry) (generatePrepared M.mm)) _
 exact RelCT.seq (two_post generateEntry_ct (fun _ _ h =>native_front_ok h)) (generatePrepared_ct M)

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! The complete attempt satisfies the reviewed native constant-time contract. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/AttemptPublic.lean`, which only this module imported.
section

/-! The reviewed public arguments and leakage determine every native timing parameter. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64

theorem attemptFront_congr {s t : State} (gs : AttemptGeometry s) (gt : AttemptGeometry t)
 (x : s.gpr .x0=t.gpr .x0) (y : s.gpr .x2=t.gpr .x2) (dp : s.gpr .x4=t.gpr .x4)
 (dl : s.gpr .x5=t.gpr .x5) (len : s.gpr .x6=t.gpr .x6) (rp : s.gpr .x7=t.gpr .x7)
 (base : stackArg s 1=stackArg t 1) (size : stackArg s 2=stackArg t 2)
 (ctx : stackArg s 3=stackArg t 3) (count : stackArg s 4=stackArg t 4)
 (dom : attemptDomain s=attemptDomain t)
 (status : Spec.Ffdh.keyStatus (attemptParameters s) (attemptScalar s)=Spec.Ffdh.keyStatus (attemptParameters t) (attemptScalar t)) :
 attemptFront s gs=attemptFront t gt :=by
 unfold attemptFront attemptNativeParameters checkedParameters
 simp only [x,y,dp,dl,len,rp,base,size,ctx,count,dom,status]

theorem attemptPub_front {s t : State} (gs : AttemptGeometry s) (gt : AttemptGeometry t) (h : attemptPub s t) :
 attemptFront s gs=attemptFront t gt ∧ s.sp=t.sp :=by
 obtain ⟨regs,sp,stack,leak⟩:=h
 have raw : ∀ r∈argRegs,s.gpr r=t.gpr r :=regs
 have x:=raw .x0 (by decide)
 have y:=raw .x2 (by decide)
 have dp:=raw .x4 (by decide)
 have dl:=raw .x5 (by decide)
 have len:=raw .x6 (by decide)
 have rp:=raw .x7 (by decide)
 rw [stackArgs_five,stackArgs_five] at stack
 have a0:= (List.cons.inj stack).1
 have st1:=(List.cons.inj stack).2
 have a1:=(List.cons.inj st1).1
 have st2:=(List.cons.inj st1).2
 have a2:=(List.cons.inj st2).1
 have st3:=(List.cons.inj st2).2
 have a3:=(List.cons.inj st3).1
 have a4:=(List.cons.inj (List.cons.inj st3).2).1
 have parts:=List.append_inj leak (by
  simp only [List.length_map,attemptDomain,Spec.Rsa.bytesAt,List.length_range,dl])
 have dom : attemptDomain s=attemptDomain t :=by
  have recover:=congrArg (List.map (BitVec.ofNat 8)) parts.1
  simpa only [List.map_map,Function.comp_def,BitVec.ofNat_toNat,BitVec.setWidth_eq,List.map_id'] using recover
 exact ⟨attemptFront_congr gs gt x y dp dl len rp a1 a2 a3 a4 dom (List.cons.inj parts.2).1,sp⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached

theorem attempt_constantTime (M : Mont) : ConstantTime isa attemptPre attemptPub (Generate.code M.mm) :=by
 intro s t ts tt u v hs ht hp es et
 let gs:=attempt_geometry hs
 let gt:=attempt_geometry ht
 have publicInfo:=attemptPub_front gs gt hp
 have first : NativeReady (attemptFront s gs) s :=⟨attemptRandom s,attempt_native_state gs⟩
 have second : NativeReady (attemptFront s gs) t :=by
  rw [publicInfo.1]
  exact ⟨attemptRandom t,attempt_native_state gt⟩
 exact ((generateNative_ct M) _ _ _ _ _ _ ⟨attemptFront s gs,first,second,publicInfo.2⟩ es et).1

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! # An attempt leaks only the domain and its status (AArch64)

The attempt's timing may depend on the domain and its status (`attemptPub`).
Two runs at the same point agree on both: the status is the first of the
statuses still to come.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Ffdh.Control (writeController)
open VG.Proof.Ffdh.AArch64.Cached (attemptPub attemptLeak attemptDomain attemptRandom attemptParameters attemptScalar attemptContract attempt_callable attempt_constantTime stackArgs_five)

open VG.Impl.Ffdh.AArch64.KeyGeneration.Search (ldf stf terminal zeroOut zeroOutputs exhausted advance rejectedScalar rejectedPublic test classify request room entry arguments finish)
open VG.Impl.Ffdh.AArch64.Cached.Search

/-- A loop state at which the controller attempts a key. -/
def KeyReady (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen

def KeyAllocated (q : KeyPoint) (u : State) : Prop := ∃ s, KeyReady q s ∧ u = allocated 48 s

/-- The attempt's entry, before the call. -/
def KeyCallCT (q : KeyPoint) (u : State) : Prop :=
  ∃ original s, KeyLive q.inputs original q.used q.keys q.scalars s ∧
    (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    KeyArgs q.inputs q.used u ∧ u.mem = writeController s.mem (callSp q.inputs) (callValues q.inputs) ∧
    Keep argRegsW (allocated 48 s) u

/-- After the attempt. -/
def KeyAttempted (q : KeyPoint) (t : State) : Prop :=
  ∃ original, KeyLive q.inputs original q.used q.keys q.scalars t ∧
    (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    AttemptPost q.inputs (keyRand original) q.used t

theorem key_allocated_pins : Pins KeyAllocated [.x19] := by
  rintro q _ _ ⟨a, ⟨⟨_, h₁, _⟩, _⟩, rfl⟩ ⟨b, ⟨⟨_, h₂, _⟩, _⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.x19.trans h₂.x19.symm

private theorem arguments_ready (q : KeyPoint) (u : State) (h : KeyAllocated q u) :
    WP isa (.block cachedArguments) u (KeyCallCT q) := by
  obtain ⟨s, ⟨⟨original, h, hst⟩, hk, hs, hr⟩, rfl⟩ := h
  exact WP.mono (key_arguments_ok h) fun _ ⟨⟨ha, hm⟩, k⟩ => ⟨original, s, h, hst, hk, hs, hr, ha, hm, k⟩

theorem key_attempt_ready (a : Attempt) (q : KeyPoint) (s : State) (h : KeyReady q s) :
    WP isa (attemptRun a.call) s (KeyAttempted q) := by
  obtain ⟨⟨original, h, hst⟩, hk, hs, hr⟩ := h
  exact WP.mono (key_attempt_run a h hr) fun _ ⟨ht, hp⟩ => ⟨original, ht, hst, hk, hs, hr, hp⟩

/-- The status of the attempt at a point: the first still to come. -/
def KeyPoint.status (q : KeyPoint) : Nat := q.statuses.head?.getD 0

/-- The attempt's status at a point, for each run's tape. -/
theorem attempt_status {q : KeyPoint} {original s : State}
    (h : KeyLive q.inputs original q.used q.keys q.scalars s)
    (hst : (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses)
    (hk : q.keys ≠ 0) (hs : q.scalars ≠ 0) (hr : q.used + q.inputs.len ≤ q.inputs.randLen) :
    attemptStatus .cached q.inputs.a q.inputs.len ((keyRand original).drop q.used) = q.status := by
  have hhead := keyTail_statuses_head (policy:=.cached) (a := q.inputs.a) (len := q.inputs.len)
    (rand := keyRand original) (used := q.used) hk hs (by rw [h.rand_length]; omega_using [hr])
  rw [hst] at hhead
  simp only [KeyPoint.status, hhead, Option.getD_some]

/-- What the attempt sees at its entry, in terms of the point alone. -/
private theorem call_view {q : KeyPoint} {u : State} (h : KeyCallCT q u) :
    (callState q.inputs q.used u).sp = callSp q.inputs ∧
    attemptLeak (callState q.inputs q.used u) = q.inputs.dom.map (·.toNat) ++ [q.status] ∧
    (∀ r ∈ argRegs, (callState q.inputs q.used u).gpr r = (match r with
      | .x0 => q.inputs.xp | .x1 => BitVec.ofNat 64 q.inputs.len | .x2 => q.inputs.yp
      | .x3 => BitVec.ofNat 64 q.inputs.len | .x4 => q.inputs.dp | .x5 => BitVec.ofNat 64 q.inputs.dlen
      | .x6 => BitVec.ofNat 64 q.inputs.len | _ => q.inputs.rp + BitVec.ofNat 64 q.used)) ∧
    List.map (stackArg (callState q.inputs q.used u)) (List.range 5) =
      [BitVec.ofNat 64 q.inputs.len, q.inputs.B, BitVec.ofNat 64 (q.inputs.Z / 8),q.inputs.ctx,BitVec.ofNat 64 q.inputs.ctxLen] := by
  obtain ⟨original, s, h, hst, hk, hs, hr, ha, hm, k⟩ := h
  have hu : u.sp = callSp q.inputs := by rw [k.sp]; show s.sp - BitVec.ofNat 64 48 = _; rw [h.sp]
  have hf := h.callFacts hr
  obtain ⟨hdom, hrand, h6⟩ := call_inputs h hr hf hm hu ha
  have he := attempt_status h hst hk hs hr
  obtain ⟨h0, h1, h2,h3,h4⟩ := call_args hu hm
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := ha
  refine ⟨by simp only [State.withRegions_sp, State.callEntry_sp, hu], ?_, ?_, ?_⟩
  · simp only [attemptLeak, attemptParameters, attemptScalar, hdom, hrand, h6]
    rw [← he]
    rfl
  · intro r hr'
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [call_gpr (by decide)] <;> with_reducible assumption
  · rw [stackArgs_five, call_stackArg, call_stackArg, call_stackArg,call_stackArg,call_stackArg, h0, h1, h2,h3,h4]

private theorem call_pub {q : KeyPoint} {u₁ u₂ : State} (h₁ : KeyCallCT q u₁) (h₂ : KeyCallCT q u₂) :
    attemptPub (callState q.inputs q.used u₁) (callState q.inputs q.used u₂) := by
  obtain ⟨a₁, b₁, c₁, d₁⟩ := call_view h₁
  obtain ⟨a₂, b₂, c₂, d₂⟩ := call_view h₂
  exact ⟨fun r hr => (c₁ r hr).trans (c₂ r hr).symm, a₁.trans a₂.symm, d₁.trans d₂.symm,
    b₁.trans b₂.symm⟩

private theorem call_ready {q : KeyPoint} {u : State} (h : KeyCallCT q u) :
    attemptContract.pre (callState q.inputs q.used u) ∧
      Covers (callRd q.inputs q.used ++ callWr q.inputs) (u.rd ++ u.wr) ∧
      Covers (callWr q.inputs) u.wr := by
  obtain ⟨original, s, h, _, _, _, hr, ha, hm, k⟩ := h
  have hu : u.sp = callSp q.inputs := by rw [k.sp]; show s.sp - BitVec.ofNat 64 48 = _; rw [h.sp]
  exact ⟨call_attempt_pre h hr (h.callFacts hr) hu ha hm, call_covers_reads h hr k.rd k.wr,
    call_covers_writes h k.wr⟩

theorem key_attempt_call_ct (a : Attempt) :
    RelCT isa (Two KeyCallCT) a.call (fun _ _ => True) := by
  refine RelCT.callEx (attempt_callable a.M) (attempt_constantTime a.M) fun u₁ u₂ ⟨q, h₁, h₂, _⟩ => ?_
  obtain ⟨p₁, c₁, w₁⟩ := call_ready h₁
  obtain ⟨p₂, c₂, w₂⟩ := call_ready h₂
  exact ⟨_, _, _, _, p₁, p₂, call_pub h₁ h₂, c₁, w₁, c₂, w₂⟩

theorem key_attempt_run_ct (a : Attempt) :
    RelCT isa (Two KeyReady) (attemptRun a.call) (fun _ _ => True) := by
  unfold attemptRun
  apply RelCT.alloc
  refine (RelCT.seq (two_piece [.x19] key_allocated_pins (by taint_decide) arguments_ready)
    (key_attempt_call_ct a)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocated, hsp]⟩

end VG.Proof.Ffdh.AArch64.Cached.SearchProof

end

end

/-! # An iteration of the key search branches on its public point alone (AArch64)

The attempt's classification branches on its status, the first of the
statuses still to come; the guards on the budgets and the tape, which the
point fixes.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.GenerationSearch
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search (ldf stf terminal zeroOut zeroOutputs exhausted advance rejectedScalar rejectedPublic test classify request room entry arguments finish)
open VG.Impl.Ffdh.AArch64.Cached.Search

/-! ## The classification -/

theorem key_attempted_pins : Pins KeyAttempted [.x19] := by
  intro q s t ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.x19.trans h₂.x19.symm

/-- The status in `x9`, compared with `k` in `x10`. -/
def KeyGuard (k : Nat) (q : KeyPoint) (t : State) : Prop :=
  KeyAny q.inputs t ∧ t.gpr .x9 = BitVec.ofNat 64 q.status ∧
    isa.eval (.zero .x .x10) t = some (decide (q.status = k)) ∧ q.status < 4

private theorem first_ready (q : KeyPoint) (s : State) (h : KeyAttempted q s) :
    WP isa (.block (advance ++ test 1)) s (KeyGuard 1 q) := by
  obtain ⟨original, h, hst, hk, hs, hr, hp⟩ := h
  have he := attempt_status h hst hk hs hr
  have h4 : q.status < 4 := by
    rw [← he]
    rcases attemptStatus_cases (policy:=.cached) q.inputs.a q.inputs.len ((keyRand original).drop q.used) with
      h | h | h <;> omega_using [h]
  refine WP.mono (key_classify_head h hr hp) fun t ⟨ht, _, hax, hev⟩ => ?_
  exact ⟨⟨original, _, _, _, ht⟩, by rw [hax, he], by rw [hev, he], h4⟩

private theorem next_ready (j k : Nat) (hk : k = 1 ∨ k = 2 ∨ k = 3) (q : KeyPoint) (s : State)
    (h : KeyGuard j q s ∧ isa.eval (.zero .x .x10) s = some false) :
    WP isa (.block (test k)) s (KeyGuard k q) := by
  obtain ⟨⟨⟨o, u, a, c, hl⟩, ha, _, h4⟩, _⟩ := h
  refine WP.mono (test_ok ha h4 hk) fun t ⟨⟨he, hm⟩, kt⟩ => ?_
  exact ⟨⟨o, u, a, c, hl.keep kt hm⟩, (kt.gpr .x9 (by decide)).trans ha, he, h4⟩

private theorem leaf {k : Nat} {b : Bool} {c : Prog isa} (hc : RelCT isa (Two KeyAny) c fun _ _ => True) :
    RelCT isa (Two fun q s => KeyGuard k q s ∧ isa.eval (.zero .x .x10) s = some b) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q.inputs, h₁.1.1, h₂.1.1, hsp⟩) fun _ _ h => h

private theorem guard_eq (k : Nat) (q : KeyPoint) (s₁ s₂ : State) (h₁ : KeyGuard k q s₁)
    (h₂ : KeyGuard k q s₂) : isa.eval (.zero .x .x10) s₁ = isa.eval (.zero .x .x10) s₂ :=
  h₁.2.2.1.trans h₂.2.2.1.symm

private theorem no_pins {Φ : KeyPoint → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ h => by cases h

theorem key_classify_ct : RelCT isa (Two KeyAttempted) classify (fun _ _ => True) := by
  unfold classify
  refine RelCT.seq (two_piece [.x19] key_attempted_pins (by taint_decide) first_ready) ?_
  refine two_ite (guard_eq 1) (leaf key_accepted_ct) ?_
  refine RelCT.seq (two_post (two_taint [] no_pins (by taint_decide))
    (next_ready 1 2 (.inr (.inl rfl)))) ?_
  refine two_ite (guard_eq 2) (leaf key_rejected_scalar_ct) ?_
  refine RelCT.seq (two_post (two_taint [] no_pins (by taint_decide))
    (next_ready 2 3 (.inr (.inr rfl)))) ?_
  exact two_ite (guard_eq 3) (leaf key_rejected_public_ct) (leaf key_exhausted_ct)

/-! ## The guards -/

/-- Whether the search goes on after an iteration from `q`: it attempts, and
the attempt is rejected. -/
def keyContinues (q : KeyPoint) : Prop :=
  q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.inputs.len ≤ q.inputs.randLen - q.used ∧ q.status ≠ 1

instance (q : KeyPoint) : Decidable (keyContinues q) := inferInstanceAs
  (Decidable (q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.inputs.len ≤ q.inputs.randLen - q.used ∧ q.status ≠ 1))

/-- The point after a rejected attempt. -/
def nextKeyPoint (q : KeyPoint) : KeyPoint :=
  if q.status = 2 then ⟨q.inputs, q.used + q.inputs.len, q.keys, q.scalars - 1, q.statuses.tail⟩
  else ⟨q.inputs, q.used + q.inputs.len, q.keys - 1, 128, q.statuses.tail⟩

theorem nextKeyPoint_inputs (q : KeyPoint) : (nextKeyPoint q).inputs = q.inputs := by
  unfold nextKeyPoint; split <;> rfl

theorem nextKeyPoint_measure {q : KeyPoint} (h : keyContinues q) :
    128 * (nextKeyPoint q).keys + (nextKeyPoint q).scalars < 128 * q.keys + q.scalars := by
  obtain ⟨hk, hs, -, -⟩ := h
  unfold nextKeyPoint; split <;> dsimp only <;> omega_arith

/-- After the guards, the attempt and its classification. -/
def KeyBranchResult (q : KeyPoint) (t : State) : Prop :=
  if keyContinues q then KeyCTL (nextKeyPoint q) t ∧ word t.mem q.inputs.control 112 = 4
  else ∃ original r, KeyDone q.inputs original r t

theorem branch_x19 {q : KeyPoint} {t : State} (h : KeyBranchResult q t) :
    t.gpr .x19 = q.inputs.control := by
  by_cases hc : keyContinues q
  · simp only [KeyBranchResult, hc, ite_true] at h
    obtain ⟨⟨_, hl, _⟩, _⟩ := h
    rw [hl.x19, nextKeyPoint_inputs]
  · simp only [KeyBranchResult, hc, ite_false] at h
    obtain ⟨_, _, hd⟩ := h
    exact hd.x19

def KeysGuard (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ isa.eval (.zero .x .x9) s = some (decide (q.keys = 0))

def ScalarsGuard (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ isa.eval (.zero .x .x9) s = some (decide (q.scalars = 0))

def RoomGuard (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧
    isa.eval (.zero .x .x12) s = some (decide (q.inputs.randLen - q.used < q.inputs.len))

theorem keys_ready (q : KeyPoint) (s : State) (h : KeyCTL q s) :
    WP isa (.block [ldf .x9 0]) s (KeysGuard q) := by
  obtain ⟨original, h, hst⟩ := h
  exact WP.mono (keys_guard h) fun _ ⟨ht, he⟩ => ⟨⟨original, ht, hst⟩, he⟩

theorem scalars_ready (q : KeyPoint) (s : State) (h : KeysGuard q s ∧ isa.eval (.zero .x .x9) s = some false) :
    WP isa (.block [ldf .x9 1]) s (ScalarsGuard q) := by
  obtain ⟨⟨⟨original, h, hst⟩, he⟩, hf⟩ := h
  have hk : q.keys ≠ 0 := of_decide_eq_false (Option.some.inj (he.symm.trans hf))
  exact WP.mono (scalars_guard h) fun _ ⟨ht, he⟩ => ⟨⟨original, ht, hst⟩, hk, he⟩

theorem room_ready (q : KeyPoint) (s : State) (h : ScalarsGuard q s ∧ isa.eval (.zero .x .x9) s = some false) :
    WP isa (.block room) s (RoomGuard q) := by
  obtain ⟨⟨⟨original, h, hst⟩, hk, he⟩, hf⟩ := h
  have hs : q.scalars ≠ 0 := of_decide_eq_false (Option.some.inj (he.symm.trans hf))
  exact WP.mono (room_guard h) fun _ ⟨ht, he⟩ => ⟨⟨original, ht, hst⟩, hk, hs, he⟩

theorem attempt_of_room {q : KeyPoint} {s : State}
    (h : RoomGuard q s ∧ isa.eval (.zero .x .x12) s = some false) : KeyReady q s := by
  obtain ⟨⟨⟨original, hl, hst⟩, hk, hs, he⟩, hf⟩ := h
  have hr := of_decide_eq_false (Option.some.inj (he.symm.trans hf))
  exact ⟨⟨original, hl, hst⟩, hk, hs, by have := hl.used_le; omega_using [hr, this]⟩

theorem key_branch_ready (a : Attempt) (q : KeyPoint) (s : State) (h : KeysGuard q s) :
    WP isa (branch a.call) s (KeyBranchResult q) := by
  obtain ⟨⟨original, hl, hst⟩, he⟩ := h
  have done : ∀ (t : State) (r : Spec.Ffdh.KeySearchResult), ¬keyContinues q →
      KeyDone q.inputs original r t → KeyBranchResult q t := fun t r hn hd => by
    simp only [KeyBranchResult, hn, ite_false]; exact ⟨original, r, hd⟩
  unfold branch
  refine WP.ite (decide (q.keys = 0)) he ?_ ?_
  · intro hz
    exact WP.mono (key_exhausted hl) fun t ht => done t _ (fun hc => hc.1 (of_decide_eq_true hz)) ht
  intro hnz
  have hk : q.keys ≠ 0 := of_decide_eq_false hnz
  refine WP.seq (WP.mono (scalars_guard hl) fun u ⟨hu, he2⟩ => ?_)
  refine WP.ite (decide (q.scalars = 0)) he2 ?_ ?_
  · intro hz
    exact WP.mono (key_exhausted hu) fun t ht => done t _ (fun hc => hc.2.1 (of_decide_eq_true hz)) ht
  intro hnz2
  have hs : q.scalars ≠ 0 := of_decide_eq_false hnz2
  unfold attemptOrRequest
  refine WP.seq (WP.mono (room_guard hu) fun u ⟨hu3, hb⟩ => ?_)
  refine WP.ite _ hb ?_ ?_
  · intro hshort
    have := of_decide_eq_true hshort
    exact WP.mono (key_request hu3) fun t ht => done t _ (fun hc => by have := hc.2.2.1; omega_arith) ht
  intro hlong
  have hroom : q.used + q.inputs.len ≤ q.inputs.randLen := by
    have := of_decide_eq_false hlong; have := hl.used_le; omega_arith
  refine WP.seq (WP.mono (key_attempt_run a hu3 hroom) fun t ⟨ht, hp⟩ => ?_)
  refine WP.mono (key_classify ht hroom (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hs) hp)
    fun r hq => ?_
  have hstat := attempt_status hl hst hk hs hroom
  have hr : q.inputs.len ≤ (keyRand original).length - q.used := by rw [hl.rand_length]; omega_using [hroom]
  rcases attemptStatus_cases (policy:=.cached) q.inputs.a q.inputs.len ((keyRand original).drop q.used) with h1 | h2 | h3
  · simp only [KeyClassified, h1, ite_true] at hq
    exact done r _ (fun hc => hc.2.2.2 (by rw [← hstat, h1])) hq
  · simp only [KeyClassified, h2, Nat.reduceEqDiff, ite_true, ite_false] at hq
    have hc : keyContinues q := ⟨hk, hs, by omega_using [hroom], by rw [← hstat, h2]; decide⟩
    have hn : nextKeyPoint q = ⟨q.inputs, q.used + q.inputs.len, q.keys, q.scalars - 1, q.statuses.tail⟩ := by
      simp only [nextKeyPoint, ← hstat, h2, ite_true]
    simp only [KeyBranchResult, hc, ite_true, hn]
    refine ⟨⟨original, hq.1, ?_⟩, hq.2⟩
    rw [← hst]
    simp only [KeyPublic.tail, keyTail_scalar hk hs hr h2, List.tail_cons]
  · simp only [KeyClassified, h3, Nat.reduceEqDiff, ite_false] at hq
    have hc : keyContinues q := ⟨hk, hs, by omega_using [hroom], by rw [← hstat, h3]; decide⟩
    have hn : nextKeyPoint q = ⟨q.inputs, q.used + q.inputs.len, q.keys - 1, 128, q.statuses.tail⟩ := by
      simp only [nextKeyPoint, ← hstat, h3, Nat.reduceEqDiff, ite_false]
    simp only [KeyBranchResult, hc, ite_true, hn]
    refine ⟨⟨original, hq.1, ?_⟩, hq.2⟩
    rw [← hst]
    simp only [KeyPublic.tail, keyTail_public hk hs hr h3, List.tail_cons]

private theorem leafB {Φ : KeyPoint → State → Prop} {c : Prog isa}
    (hΦ : ∀ q s, Φ q s → KeyAny q.inputs s) (hc : RelCT isa (Two KeyAny) c fun _ _ => True) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q.inputs, hΦ q _ h₁, hΦ q _ h₂, hsp⟩) fun _ _ h => h

theorem key_branch_ct (a : Attempt) :
    RelCT isa (Two KeysGuard) (branch a.call) (fun _ _ => True) := by
  unfold branch
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (leafB (fun _ _ h => h.1.1.any) key_exhausted_ct) ?_
  refine RelCT.seq (two_piece [.x19] (fun q _ _ h₁ h₂ => key_ctl_pins q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide) scalars_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm)
    (leafB (fun _ _ h => h.1.1.any) key_exhausted_ct) ?_
  unfold attemptOrRequest
  refine RelCT.seq (two_piece [.x19] (fun q _ _ h₁ h₂ => key_ctl_pins q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide) room_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm)
    (leafB (fun _ _ h => h.1.1.any) key_request_ct) ?_
  exact RelCT.seq (two_post ((key_attempt_run_ct a).mono
      (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, attempt_of_room h₁, attempt_of_room h₂, hsp⟩) fun _ _ h => h)
    fun q s h => key_attempt_ready a q s (attempt_of_room h)) key_classify_ct

end VG.Proof.Ffdh.AArch64.Cached.SearchProof

end

end

/-! # The key search's timing depends on its public descriptor and statuses (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.Control (writeController)
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search (ldf stf terminal zeroOut zeroOutputs exhausted advance rejectedScalar rejectedPublic test classify request room entry arguments finish)
open VG.Impl.Ffdh.AArch64.Cached.Search

/-! ## The loop -/

theorem key_iteration_ct (a : Attempt) :
    RelCT isa (Two KeyCTL) (iteration a.call) (fun _ _ => True) := by
  unfold iteration
  refine RelCT.seq (two_piece [.x19] key_ctl_pins (by taint_decide) keys_ready) ?_
  exact RelCT.seq (two_post (key_branch_ct a) (key_branch_ready a))
    (two_taint [.x19] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact (branch_x19 h₁).trans (branch_x19 h₂).symm) (by taint_decide))

def KeyCTStep (q : KeyPoint) (s : State) : Prop :=
  if keyContinues q then isa.eval (.zero .x .x9) s = some true ∧ KeyCTL (nextKeyPoint q) s
  else isa.eval (.zero .x .x9) s = some false

theorem key_ct_step (a : Attempt) (q : KeyPoint) (s : State) (h : KeyCTL q s) :
    WP isa (iteration a.call) s (KeyCTStep q) := by
  unfold iteration
  refine WP.seq (WP.mono (keys_ready q s h) fun u hu => ?_)
  refine WP.seq (WP.mono (key_branch_ready a q u hu) fun t ht => ?_)
  by_cases hc : keyContinues q
  · simp only [KeyBranchResult, hc, ite_true] at ht
    obtain ⟨⟨original, hl, hst⟩, hw⟩ := ht
    rw [← nextKeyPoint_inputs q] at hw
    refine WP.mono (live_loop_guard hl hw) fun z ⟨hz, hzl⟩ => ?_
    simp only [KeyCTStep, hc, ite_true]
    exact ⟨hz, original, hzl, hst⟩
  · simp only [KeyBranchResult, hc, ite_false] at ht
    obtain ⟨_, _, hd⟩ := ht
    refine WP.mono (done_loop_guard hd) fun z ⟨hz, _⟩ => ?_
    simp only [KeyCTStep, hc, ite_false]
    exact hz

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q, n = 128 * q.keys + q.scalars + 1 ∧ KeyCTL q s ∧ KeyCTL q t ∧ s.sp = t.sp

private theorem iteration_pair (a : Attempt) (n : Nat) :
    RelCT isa (LoopPair n) (iteration a.call) fun s t =>
      isa.eval (.zero .x .x9) s = isa.eval (.zero .x .x9) t ∧
      (isa.eval (.zero .x .x9) s = some false → True) ∧
      (isa.eval (.zero .x .x9) s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (q : KeyPoint) (s : State) (h : n = 128 * q.keys + q.scalars + 1 ∧ KeyCTL q s) :
      WP isa (iteration a.call) s fun t => n = 128 * q.keys + q.scalars + 1 ∧ KeyCTStep q t :=
    WP.mono (key_ct_step a q s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((key_iteration_ct a).mono
    (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.2, h₂.2, hsp⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂, hsp⟩ => ⟨q, ⟨hn, h₁⟩, ⟨hn, h₂⟩, hsp⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, ⟨_, h₂⟩, hsp⟩
  by_cases hb : keyContinues q
  · simp only [KeyCTStep, hb, ite_true] at h₁ h₂
    refine ⟨h₁.1.trans h₂.1.symm, fun _ => trivial, fun _ => ?_⟩
    refine ⟨128 * (nextKeyPoint q).keys + (nextKeyPoint q).scalars + 1, ?_, nextKeyPoint q, rfl,
      h₁.2, h₂.2, hsp⟩
    have := nextKeyPoint_measure hb
    omega_using [hn, this]
  · simp only [KeyCTStep, hb, ite_false] at h₁ h₂
    exact ⟨h₁.trans h₂.symm, fun _ => trivial, fun ht => absurd (ht.symm.trans h₁) (by decide)⟩

theorem key_loop_ct (a : Attempt) :
    RelCT isa (Two KeyCTL) (.loop (iteration a.call) (.zero .x .x9)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht, hsp⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration a.call) (c := .zero .x .x9)
    (Q := fun _ _ => True) LoopPair (iteration_pair a) (128 * q.keys + q.scalars + 1)
    _ _ _ _ _ _ ⟨q, rfl, hs, ht, hsp⟩ he₁ he₂

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

/-- A run's entry, with its public descriptor and its result's statuses. -/
def KeyStart (a : KeyPublic × List Nat) (s : State) : Prop :=
  KeyInput a.1 s ∧ (keyResult s).statuses = a.2

private theorem entry_pointer (p : KeyPublic) (s : State) (h : KeyInput p s) :
    WP isa (.block (entry.take 6)) s fun t => t.gpr .x8 = p.control := by
  have hd : s.mem.readW (s.sp + BitVec.ofNat 64 32) 64 = p.control :=
    congrArg KeyPublic.control h.2
  have ha4 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 32) 8 := input_args h 4 (by decide)
  have ha0 : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa only [Nat.mul_zero, BitVec.add_zero] using input_args h 0 (by decide)
  have ha1 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 := input_args h 1 (by decide)
  have ha2 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 16) 8 := input_args h 2 (by decide)
  have ha3 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 24) 8 := input_args h 3 (by decide)
  unfold entry
  simp only [List.take_succ_cons, List.take_zero]
  brun [exec_addSp (show 0 < 4096 by decide), hd, ha0, ha1, ha2, ha3, ha4]

private theorem entry_ct : RelCT isa (Two KeyInput) (.block entry) (fun _ _ => True) := by
  change RelCT isa (Two KeyInput) (.block (entry.take 6 ++ entry.drop 6)) _
  refine RelCT.block_append (RelCT.seq (two_piece [] (fun _ _ _ _ _ _ h => by cases h)
    (by taint_decide) entry_pointer) ?_)
  exact two_taint [.x8] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.trans h₂.symm) (by taint_decide)

/-- After the entry: the controller's words written. -/
def KeyEntered (a : KeyPublic × List Nat) (t : State) : Prop :=
  ∃ s, KeyStart a s ∧ t.gpr .x19 = a.1.control ∧
    t.mem = writeController s.mem a.1.control (entryValues s) ∧
    Keep [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x19] s t

private theorem entry_ready (a : KeyPublic × List Nat) (s : State) (h : KeyStart a s) :
    WP isa (.block entry) s (KeyEntered a) :=
  WP.mono (entry_ok h.1) fun _ ⟨⟨hx, hm⟩, k⟩ => ⟨s, h, hx, hm, k⟩

private def initialPoint (a : KeyPublic × List Nat) : KeyPoint := ⟨a.1, 0, a.1.keys, a.1.scalars, a.2⟩

private theorem entered_ctl {a : KeyPublic × List Nat} {t : State} (h : KeyEntered a t) :
    KeyCTL (initialPoint a) (pushedX30 t) := by
  rcases a with ⟨p, l⟩
  obtain ⟨s, ⟨hi, hst⟩, hx, hm, k⟩ := h
  refine ⟨s, key_start hi hx hm k, ?_⟩
  show (p.tail (keyRand s) 0 p.keys p.scalars).statuses = l
  change (keyResult s).statuses = l at hst
  change KeyInput p s at hi
  rw [← hst]
  cases hi.2
  simp only [keyResult, KeyPublic.tail, Proof.Ffdh.GenerationSearch.keyTail,
    Proof.Ffdh.GenerationSearch.after,VG.Proof.Ffdh.GenerationPolicy.search, keyOfState, KeyPublic.a, List.drop_zero]

def KeyCTDone (p : KeyPublic) (s : State) : Prop := ∃ original r, KeyDone p original r s

private theorem search_ct (a : Attempt) : RelCT isa (Two KeyEntered) (search a.call) (fun _ _ => True) := by
  unfold search
  refine relCT_pushX30 (fun _ _ ⟨_, _, _, hsp⟩ => hsp) (fun x y ⟨q, h₁, h₂, _⟩ => ?_) ?_
  · obtain ⟨original, hl, -⟩ := entered_ctl h₁
    obtain ⟨original', hl', -⟩ := entered_ctl h₂
    obtain ⟨t, s', e, -⟩ := key_loop a (n := 128 * q.1.keys + q.1.scalars + 1)
      (expected := (initialPoint q).inputs.tail (keyRand original) 0 q.1.keys q.1.scalars)
      ⟨0, _, _, rfl, hl, rfl, rfl⟩
    obtain ⟨t', s'', e', -⟩ := key_loop a (n := 128 * q.1.keys + q.1.scalars + 1)
      (expected := (initialPoint q).inputs.tail (keyRand original') 0 q.1.keys q.1.scalars)
      ⟨0, _, _, rfl, hl', rfl, rfl⟩
    exact ⟨⟨t, s', e⟩, ⟨t', s'', e'⟩⟩
  · refine (key_loop_ct a).mono ?_ fun _ _ h => h
    rintro _ _ ⟨x, y, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
    exact ⟨initialPoint q, entered_ctl h₁, entered_ctl h₂, by simp only [hsp]⟩

private theorem search_ready (a : Attempt) (q : KeyPublic × List Nat) (t : State) (h : KeyEntered q t) :
    WP isa (search a.call) t (KeyCTDone q.1) := by
  obtain ⟨s, ⟨hi, _⟩, hx, hm, k⟩ := h
  exact WP.mono (key_search a hi hx hm k) fun _ ⟨r, _, _, hd, _⟩ => ⟨s, r, hd⟩

private theorem finish_pointer (p : KeyPublic) (s : State) (h : KeyCTDone p s) :
    WP isa (.block (finish.take 4)) s fun t => t.gpr .x1 = p.up := by
  obtain ⟨original, r, h⟩ := h
  have scr := h.input.control_scr (t := s) h.wr
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hu := h.usedPtr
  simp only [Bignum.word, off] at hu
  unfold finish
  simp only [List.take_succ_cons, List.take_zero]
  brun [ldf, h.x19, hu, hl 120 (by decide), hl 88 (by decide), hl 112 (by decide), hl 32 (by decide)]

private theorem finish_ct : RelCT isa (Two KeyCTDone) (.block finish) (fun _ _ => True) := by
  change RelCT isa (Two KeyCTDone) (.block (finish.take 4 ++ finish.drop 4)) _
  refine RelCT.block_append (RelCT.seq (two_piece [.x19] ?_ (by taint_decide) finish_pointer) ?_)
  · intro p s t ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.x19.trans h₂.x19.symm
  · exact two_taint [.x1] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact h₁.trans h₂.symm) (by taint_decide)

theorem key_code_ct (a : Attempt) :
    RelCT isa (Two KeyStart) (code a.call) (fun _ _ => True) := by
  unfold code
  exact RelCT.seq (two_post (two_map Prod.fst (fun _ _ h => h.1) entry_ct) entry_ready)
    (RelCT.seq (two_post (search_ct a) (search_ready a))
      (two_map Prod.fst (fun _ _ h => h) finish_ct))

private theorem key_public_descriptor {s t : State} (h : keyPub s t) : keyOfState s = keyOfState t := by
  obtain ⟨hsp, hr, ha, hdom, hw, -⟩ := h
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨r0, -, r2, -, r4, r5, r6, r7⟩ := hr
  change [word s.mem (stackArg s 4) 0, word s.mem (stackArg s 4) 8, word s.mem (stackArg s 4) 16,
    word s.mem (stackArg s 4) 24] = [word t.mem (stackArg t 4) 0, word t.mem (stackArg t 4) 8,
      word t.mem (stackArg t 4) 16, word t.mem (stackArg t 4) 24] at hw
  have h0 : s.mem.readW (stackArg s 4) 64 = t.mem.readW (stackArg t 4) 64 := by
    simpa only [Bignum.word, off, BitVec.add_zero] using (List.cons.inj hw).1
  have h1 : s.mem.readW (stackArg s 4 + 8) 64 = t.mem.readW (stackArg t 4 + 8) 64 := by
    have := (List.cons.inj (List.cons.inj hw).2).1
    simp only [Bignum.word, off] at this
    exact this
  unfold keyOfState
  rw [keyRetries, keyRetries, h0, h1, hdom, hsp, r0, r2, r4, r5, r6, keyLen, keyLen, r7, ha 0 (by decide),
    ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),ha 5 (by decide),ha 6 (by decide)]

theorem key_constantTime (a : Attempt) :
    ConstantTime isa keyContract.pre keyContract.pub (code a.call) := by
  refine RelCT.constantTime ((key_code_ct a).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨(keyOfState s, (keyResult s).statuses), ⟨⟨hs, rfl⟩, rfl⟩,
    ⟨⟨ht, (key_public_descriptor hp).symm⟩, hp.2.2.2.2.2.symm⟩, hp.1⟩

end VG.Proof.Ffdh.AArch64.Cached.SearchProof

end

end

/-! A canonical context and empty tape witness the complete cached controller ABI. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof
open VG VG.AArch64

private def keyBase : State where
 gpr r:=match r with
  | .x0=>0x1000 | .x1=>64 | .x2=>0x2000 | .x3=>64 | .x4=>0x5000 | .x5=>0x3000 | .x6=>128 | .x7=>64 | _=>0
 sp:=0x6000
 mem a:=if a=0x6001 then 0x70 else if a=0x6011 then 0x80 else if a=0x6018 then 0x20
  else if a=0x6019 then 4 else if a=0x6021 then 0x40 else if a=0x4010 then 0x40
  else if a=0x602a then 0x10 else if a=0x6030 then 0x13 else if a=0x6031 then 1 else Sat.domainMem a
 rd:=[⟨0x3000,128⟩,⟨0x7000,0⟩,⟨0x100000,2200⟩,⟨0x6000,56⟩]
 wr:=[⟨0x1000,64⟩,⟨0x2000,64⟩,⟨0x5000,8⟩,⟨0x8000,8448⟩,⟨0x4000,128⟩]

private def keySat : State :={keyBase with mem:=Sat.withContext keyBase.mem}

private theorem key_arg (i : Nat) (hi : i<7) : stackArg keySat i=stackArg keyBase i :=by
 apply Sat.readW_outside
 have small : ∀i<7,(stackArgAddr keyBase i).toNat+8≤0x100000 :=by decide
 exact small i hi

private theorem key_domain : Spec.Rsa.bytesAt keySat.mem 0x3000 128=Sat.domain :=by
 rw [show keySat.mem=Sat.withContext keyBase.mem from rfl,Sat.domain_unchanged]
 unfold Sat.domain
 decide +kernel

private theorem key_control (i : Nat) (hi : i<3) : keySat.mem.readW (0x4000+BitVec.ofNat 64 (8*i)) 64=
 keyBase.mem.readW (0x4000+BitVec.ofNat 64 (8*i)) 64 :=by
 apply Sat.readW_outside
 have small : ∀i<3,((0x4000 : Addr)+BitVec.ofNat 64 (8*i)).toNat+8≤0x100000 :=by decide
 exact small i hi

theorem key_sat : ∃s,(Spec.Ffdh.cachedKeySearchContract abi 64).pre s :=by
 refine ⟨keySat,?_⟩
 sig_pre [Spec.Ffdh.cachedKeySearchContract,Spec.Ffdh.cachedKeySearchSig,Spec.Ffdh.keySearchSig,
  Spec.Ffdh.pLenValid,Spec.Ffdh.domainLenValid,Spec.Ffdh.generationContextAt,abi,argRegs]
 simp only [key_arg 0 (by decide),key_arg 1 (by decide),key_arg 2 (by decide),key_arg 3 (by decide),key_arg 4 (by decide),key_arg 5 (by decide),key_arg 6 (by decide)]
 have a0 : stackArg keyBase 0=0x7000 :=by decide
 have a1 : stackArg keyBase 1=0 :=by decide
 have a2 : stackArg keyBase 2=0x8000 :=by decide
 have a3 : stackArg keyBase 3=1056 :=by decide
 have a4 : stackArg keyBase 4=0x4000 :=by decide
 have a5 : stackArg keyBase 5=0x100000 :=by decide
 have a6 : stackArg keyBase 6=275 :=by decide
 rw [a0,a1,a2,a3,a4,a5,a6]
 dsimp only [keySat,keyBase]
 repeat' apply And.intro
 all_goals first
  | (change Spec.Ffdh.domainValid 64 (Spec.Rsa.bytesAt keySat.mem 0x3000 128)=true
     rw [key_domain];exact Sat.domain_valid)
  | (change Spec.Ffdh.generationPrecompute 64 (Spec.Rsa.bytesAt keySat.mem 0x3000 128)=some (Spec.Rsa.wordsAt keySat.mem 0x100000 275)
     rw [key_domain];exact (Sat.canonical _).2)
  | (change (keySat.mem.readW 0x4000 64).toNat≤128
     rw [show (0x4000 : Addr)=0x4000+BitVec.ofNat 64 (8*0) from rfl,key_control 0 (by decide)];decide)
  | (change (keySat.mem.readW (0x4000+8) 64).toNat≤128
     rw [show (0x4000+8 : Addr)=0x4000+BitVec.ofNat 64 (8*1) from rfl,key_control 1 (by decide)];decide)
  | (change keySat.mem.readW (0x4000+16) 64=BitVec.ofNat 64 64
     rw [show (0x4000+16 : Addr)=0x4000+BitVec.ofNat 64 (8*2) from rfl,key_control 2 (by decide)];decide)
  | decide +kernel
  | (apply Region.disjoint_of_sep;decide +kernel)

end VG.Proof.Ffdh.AArch64.Cached.SearchProof
