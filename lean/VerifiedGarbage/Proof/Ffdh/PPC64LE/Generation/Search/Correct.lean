module
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Entry

import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Loop
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.GenerationBounds
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset

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
      (show p.len ≤ 2 ^ 64 by omega) (List.mem_range.mp hi)
  have hc (j : Nat) (hj : j < 4) : word t.mem p.control (8 * j) = word s.mem p.control (8 * j) :=
    hf.readW (r := ⟨p.control, 128⟩)
      (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hd.2) (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, k.sp, k.lr⟩
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
  · intro reg hreg
    by_cases he : reg = .r31
    · subst he; exact hr31
    · exact (k.gpr reg (by revert reg hreg he; decide)).trans (h.saved reg hreg he)

/-! ## The search's frame -/

theorem iteration_depth (c : Cand) : sdepth (iteration c.call) ≤ 288 := by
  have := c.stack
  simp only [iteration, candidateRun, exhausted, zeroOut, classify, short, Impl.Bignum.PPC64LE.countLoop,
    sdepth, Cand.call, Instr.frameBytes]
  omega

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

theorem SInput.tail_eq {p : SPub} {s : State} (h : SInput p s) : searchResult s = p.tail 0 p.attempts := by
  cases h.2
  simp only [searchResult, SPub.tail, sOfState, List.drop_zero, Proof.Ffdh.Generation.consume_zero]

theorem search_body {p : SPub} {s t : State} (c : Cand) (h : SInput p s)
    (hx : t.gpr .r31 = p.control)
    (hm : t.mem = Proof.Ffdh.Control.writeController s.mem p.control (entryValues s))
    (k : Keep entryRegs s t) :
    WP isa (search c.call) t fun u =>
      SDone p s (searchResult s) u ∧ u.lr = s.lr ∧ u.sp = s.sp := by
  unfold search
  refine WP.seq (WP.mono (WP.keep [.r0] (Q := fun t₁ => t₁.gpr .r0 = t.lr ∧ t₁.mem = t.mem) (by
    prun [exec_mflr]) (by decide)) fun t₁ ⟨⟨h0, hm₁⟩, k₁⟩ => ?_)
  have k' : Keep entryRegs s t₁ := k.trans' (k₁.mono (by decide))
  have hl := search_start h (by rw [k₁.gpr _ (by decide)]; exact hx) (hm₁.trans hm) k'
  have hsp : 48 ≤ t₁.sp.toNat := by rw [k'.sp, ← h.sp_eq]; have := h.sp_room; omega
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
      ⟨0, p.attempts, rfl, hl, h.tail_eq⟩) fun u hu => ⟨hu.popped _ _, ?_, k'.sp⟩
    show (u.write .r0 (t₁.gpr .r0)).gpr .r0 = _
    rw [RegUpd.gpr_write_self, h0, k.lr]
  · have := iteration_depth c
    simp only [sdepth]
    omega
  · prun [exec_mtlr]
    exact ⟨⟨hd.input, hd.rd, hd.wr, hd.r31, hd.saved, hd.savedR31, hd.usedPtr, hd.used, hd.status, hd.policy,
      hd.output⟩, h0', hsp'⟩

theorem SReturned.post {s t : State} (h : SReturned (sOfState s) (searchResult s) t) : searchPost s t :=
  ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩

theorem search_correct_ok (c : Cand) {s : State} (h : searchPre s) :
    WP isa (code c.call) s fun t => searchPost s t ∧ abiPreserved s t := by
  let p := sOfState s
  have hp : SInput p s := ⟨h, rfl⟩
  unfold code
  refine WP.seq (WP.mono (entry_ok hp) fun t ⟨⟨hx, hm⟩, k⟩ => ?_)
  refine WP.seq (WP.mono (search_body c hp hx hm k) fun u ⟨hd, hlr, hsp⟩ => ?_)
  refine WP.mono (search_finish hd) fun q ⟨hr, hg, hqsp, hqlr⟩ => ?_
  exact ⟨hr.post, hg, hqsp.trans hsp, hqlr.trans hlr⟩

theorem search_correct (c : Cand) (s : State) (h : searchContract.pre s) :
    ∃ tr t, Exec isa (code c.call) s tr t ∧ abiPreserved s t ∧ searchContract.post s t := by
  obtain ⟨tr, t, he, hp, ha⟩ := search_correct_ok c h
  exact ⟨tr, t, he, ha, hp⟩

end VG.Proof.Ffdh.PPC64LE.Generation
