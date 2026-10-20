module
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Entry

import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Loop
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.GenerationBounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore

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
      (show p.len ≤ 2 ^ 64 by omega) (List.mem_range.mp hi)
  have hc (j : Nat) (hj : j < 4) : word t.mem p.control (8 * j) = word s.mem p.control (8 * j) :=
    hf.readW (r := ⟨p.control, 128⟩)
      (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hd.2) (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, k.sp, k.gpr .x30 (by decide), fun r hr => (k.vcs r hr).trans (h.vcs r hr)⟩
  · rw [ha]
    have := result_status_lt result
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
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
  have hsp : 16 ≤ t.sp.toNat := by rw [k.sp, ← h.sp_eq]; have := h.sp_room; omega
  unfold search
  refine WP.frameReg hsp ?_ ?_ ?_
  · intro R hR
    rw [k.wr, h.1.2.2.2.1] at hR
    have hd := h.stack_disjoint (r := R) (List.mem_append_left _ hR)
    refine hd.sub_left ?_
    rw [k.sp]
    exact Offset.sub_below s.sp (a := 16) (b := 32) (by decide) (by decide)
  · refine WP.mono (search_loop c (expected := searchResult s) (n := p.attempts + 1)
      ⟨0, p.attempts, rfl, hl, h.tail_eq⟩) fun u hu => ?_
    refine ⟨hu.popped _ _, ?_, k.sp⟩
    show (u.write .x .x30 (t.gpr .x30)).gpr .x30 = _
    rw [RegUpd.gpr_write, ite_eq_left rfl]
    exact k.gpr .x30 (by decide)
  · show 16 * (iteration c.call).aarch64Depth + 16 < 2 ^ 64
    rw [iteration_depth c]; decide

theorem SReturned.post {s t : State} (h : SReturned (sOfState s) (searchResult s) t) : searchPost s t :=
  ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩

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
