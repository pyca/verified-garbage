module
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Live

import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Classify
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-! # Total correctness of the parameter search's loop (PPC64LE) -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Spec.Ffdh
open VG.Impl.Ffdh.PPC64LE.Generation.Search

theorem ofNat_beq_zero {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h]
  exact Iff.rfl

/-- The attempts left compared with zero. -/
theorem attempts_guard {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) :
    WP isa (.block [ldf .r9 0]) s fun t =>
      SLive p original used k t ∧ isa.eval (.zero .d .r9) t = some (decide (k = 0)) := by
  have a := h.access
  have hw := h.header (j := 0) (v := BitVec.ofNat 64 k) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.mul_zero, BitVec.add_zero] at hw
  have hk : k < 2 ^ 64 := by have := h.k_le; have := h.input.attempts_lt; omega
  refine WP.mono (WP.keep [.r9] (Q := fun t =>
    isa.eval (.zero .d .r9) t = some (decide (k = 0)) ∧ t.mem = s.mem) ?_ (by decide))
    fun _ ⟨⟨he, hm⟩, kt⟩ => ⟨h.keep kt hm, he⟩
  prun [ldf, h.r31, hw, a.ld 0 (by decide), a.ld0, BitVec.add_zero]
  refine (eval_zero _ _).trans ?_
  rw [RegUpd.gpr_write_self, ofNat_beq_zero hk]

/-- The status word, minus 4. -/
theorem status_guard {s : State} {B : Addr} (a : CtlAccess s B) (hb : s.gpr .r31 = B) {st : Nat}
    (hs : word s.mem B 112 = BitVec.ofNat 64 st) (hst : st < 5) :
    WP isa (.block [ldf .r9 14, .subi .r9 .r9 4]) s fun t =>
      (isa.eval (.zero .d .r9) t = some (decide (st = 4)) ∧ t.mem = s.mem) ∧ Keep [.r9] s t := by
  simp only [Bignum.word, off] at hs
  refine WP.keep [.r9] ?_ (by decide)
  prun [ldf, hb, hs, a.ld 112 (by decide)]
  have : ∀ st < 5, ((BitVec.ofNat 64 st - BitVec.ofNat 64 4) == 0) = decide (st = 4) := by decide
  refine (eval_zero _ _).trans ?_
  rw [RegUpd.gpr_write_self, this st hst]

theorem result_status_lt (r : ParameterSearchResult) : r.status < 5 := by
  unfold ParameterSearchResult.status; split <;> decide

theorem result_status_ne (r : ParameterSearchResult) : r.status ≠ 4 := by
  unfold ParameterSearchResult.status; split <;> decide

theorem done_loop_guard {p : SPub} {original s : State} {r : ParameterSearchResult}
    (h : SDone p original r s) :
    WP isa (.block [ldf .r9 14, .subi .r9 .r9 4]) s fun t =>
      isa.eval (.zero .d .r9) t = some false ∧ SDone p original r t := by
  have a := CtlAccess.of_scr (h.input.control_scr (t := s) h.wr)
  refine WP.mono (status_guard a h.r31 h.status (result_status_lt r)) fun t ⟨⟨he, hm⟩, k⟩ =>
    ⟨?_, h.keep k hm⟩
  rw [he, decide_eq_false (result_status_ne r)]

theorem live_loop_guard {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hs : word s.mem p.control 112 = 4) :
    WP isa (.block [ldf .r9 14, .subi .r9 .r9 4]) s fun t =>
      isa.eval (.zero .d .r9) t = some true ∧ SLive p original used k t :=
  WP.mono (status_guard (st := 4) h.access h.r31 hs (by decide))
    fun _ ⟨⟨he, hm⟩, k⟩ => ⟨he, h.keep k hm⟩

/-- The loop's state: the search from octet `used`, with `k` attempts left,
leads to the expected result. -/
def SInvariant (p : SPub) (original : State) (expected : ParameterSearchResult) (n : Nat) (s : State) :
    Prop :=
  ∃ used k, n = k + 1 ∧ SLive p original used k s ∧ expected = p.tail used k

theorem search_iteration (c : Cand) {p : SPub} {original s : State}
    {expected : ParameterSearchResult} {n : Nat}
    (h : SInvariant p original expected n s) :
    WP isa (iteration c.call) s fun t =>
      (isa.eval (.zero .d .r9) t = some false ∧ SDone p original expected t) ∨
      (isa.eval (.zero .d .r9) t = some true ∧ ∃ m < n, SInvariant p original expected m t) := by
  obtain ⟨used, k, hn, h, he⟩ := h
  subst he
  have done : ∀ t, SDone p original (p.tail used k) t →
      WP isa (.block [ldf .r9 14, .subi .r9 .r9 4]) t fun t =>
        (isa.eval (.zero .d .r9) t = some false ∧ SDone p original (p.tail used k) t) ∨
        (isa.eval (.zero .d .r9) t = some true ∧ ∃ m < n, SInvariant p original (p.tail used k) m t) :=
    fun _ hd => WP.mono (done_loop_guard hd) fun _ ⟨hq, hdq⟩ => Or.inl ⟨hq, hdq⟩
  unfold iteration
  refine WP.seq (WP.mono (attempts_guard h) fun u ⟨hu, he⟩ => ?_)
  apply WP.seq
  refine WP.ite (decide (k = 0)) he ?_ ?_
  · intro hz
    have hz' := of_decide_eq_true hz
    subst hz'
    rw [SPub.tail_zero]
    exact WP.mono (search_exhausted hu) fun t ht => done t (by rw [SPub.tail_zero]; exact ht)
  intro hnz
  have hk : k ≠ 0 := of_decide_eq_false hnz
  refine WP.seq (WP.mono (search_candidate_run c hu) fun t ⟨ht, hp⟩ => ?_)
  refine WP.mono (search_classify ht hk hp) fun q hq => ?_
  unfold SClassified at hq
  split at hq
  · rename_i h2
    obtain ⟨rest, hc⟩ : ∃ rest, p.cand used = some (none, rest) := by
      revert h2
      cases p.cand used with
      | none => intro h2; cases h2
      | some pair =>
        obtain ⟨value, rest⟩ := pair
        cases value with
        | some _ => intro h2; cases h2
        | none => intro _; exact ⟨rest, rfl⟩
    have hr : p.read used = (p.randLen - used) - rest.length := by simp only [SPub.read, hc]
    refine WP.mono (live_loop_guard hq.1 hq.2) fun z ⟨hz, hzl⟩ => Or.inr ⟨hz, _, ?_,
      used + p.read used, k - 1, rfl, hzl, ?_⟩
    · omega
    · rw [hr]; exact SPub.tail_reject hk h.rand_length hc
  · exact done q hq

theorem search_loop (c : Cand) {p : SPub} {original s : State}
    {expected : ParameterSearchResult} {n : Nat}
    (h : SInvariant p original expected n s) :
    WP isa (.loop (iteration c.call) (.zero .d .r9)) s (SDone p original expected) :=
  WP.loop (M := isa) (body := iteration c.call) (c := .zero .d .r9)
    (Q := SDone p original expected) (SInvariant p original expected)
    (fun _ _ h => search_iteration c h) n s h

end VG.Proof.Ffdh.PPC64LE.Generation
