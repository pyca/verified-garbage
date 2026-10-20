module
public import VerifiedGarbage.Impl.Ffdh.AArch64.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Live

import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Classify
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Total correctness of the parameter search's loop (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Spec.Ffdh
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Ffdh.AArch64.Generation.Search

theorem ofNat_beq_zero {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h]
  exact Iff.rfl

/-- The attempts left compared with zero. -/
theorem attempts_guard {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) :
    WP isa (.block [ldf .x9 0]) s fun t =>
      SLive p original used k t ∧ isa.eval (.zero .x .x9) t = some (decide (k = 0)) := by
  have a := h.access
  have hw := h.header (j := 0) (v := BitVec.ofNat 64 k) (by simp [SPub.headers])
  simp only [Bignum.word, off] at hw
  have hk : k < 2 ^ 64 := by have := h.k_le; have := h.input.attempts_lt; omega
  refine WP.mono (WP.keep [.x9] (Q := fun t =>
    isa.eval (.zero .x .x9) t = some (decide (k = 0)) ∧ t.mem = s.mem) ?_ (by decide) (by decide)
    (by decide +kernel)) fun _ ⟨⟨he, hm⟩, kt⟩ => ⟨h.keep kt hm, he⟩
  brun [ldf, h.x19, hw, a.ld 0 (by decide), a.ld0]
  simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq,
    ofNat_beq_zero hk]

/-- The status word, minus 4. -/
theorem status_guard {s : State} {B : Addr} (a : CtlAccess s B) (hb : s.gpr .x19 = B) {st : Nat}
    (hs : word s.mem B 112 = BitVec.ofNat 64 st) (hst : st < 5) :
    WP isa (.block [ldf .x9 14, .subImm .x .x9 .x9 4]) s fun t =>
      (isa.eval (.zero .x .x9) t = some (decide (st = 4)) ∧ t.mem = s.mem) ∧ Keep [.x9] s t := by
  simp only [Bignum.word, off] at hs
  refine WP.keep [.x9] ?_ (by decide) (by decide) (by decide +kernel)
  brun [ldf, hb, hs, a.ld 112 (by decide)]
  have : ∀ st < 5, ((BitVec.ofNat 64 st - BitVec.ofNat 64 4) == 0) = decide (st = 4) := by decide
  have hb' := this st hst
  simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq,
    Option.some.injEq] at hb' ⊢
  exact hb'

theorem result_status_lt (r : ParameterSearchResult) : r.status < 5 := by
  unfold ParameterSearchResult.status; split <;> decide

theorem result_status_ne (r : ParameterSearchResult) : r.status ≠ 4 := by
  unfold ParameterSearchResult.status; split <;> decide

theorem done_loop_guard {p : SPub} {original s : State} {r : ParameterSearchResult}
    (h : SDone p original r s) :
    WP isa (.block [ldf .x9 14, .subImm .x .x9 .x9 4]) s fun t =>
      isa.eval (.zero .x .x9) t = some false ∧ SDone p original r t := by
  have a := CtlAccess.of_scr (h.input.control_scr (t := s) h.wr)
  refine WP.mono (status_guard a h.x19 h.status (result_status_lt r)) fun t ⟨⟨he, hm⟩, k⟩ =>
    ⟨?_, h.keep k hm⟩
  rw [he, decide_eq_false (result_status_ne r)]

theorem live_loop_guard {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hs : word s.mem p.control 112 = 4) :
    WP isa (.block [ldf .x9 14, .subImm .x .x9 .x9 4]) s fun t =>
      isa.eval (.zero .x .x9) t = some true ∧ SLive p original used k t :=
  WP.mono (status_guard (st := 4) h.access h.x19 hs (by decide))
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
      (isa.eval (.zero .x .x9) t = some false ∧ SDone p original expected t) ∨
      (isa.eval (.zero .x .x9) t = some true ∧ ∃ m < n, SInvariant p original expected m t) := by
  obtain ⟨used, k, hn, h, he⟩ := h
  subst he
  have done : ∀ t, SDone p original (p.tail used k) t →
      WP isa (.block [ldf .x9 14, .subImm .x .x9 .x9 4]) t fun t =>
        (isa.eval (.zero .x .x9) t = some false ∧ SDone p original (p.tail used k) t) ∨
        (isa.eval (.zero .x .x9) t = some true ∧ ∃ m < n, SInvariant p original (p.tail used k) m t) :=
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
    WP isa (.loop (iteration c.call) (.zero .x .x9)) s (SDone p original expected) :=
  WP.loop (M := isa) (body := iteration c.call) (c := .zero .x .x9)
    (Q := SDone p original expected) (SInvariant p original expected)
    (fun _ _ h => search_iteration c h) n s h

end VG.Proof.Ffdh.AArch64.Generation
