module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Classify
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # The RSA prime search's loop (AArch64)

Each iteration from a loop state with counted candidates runs the candidate
and classifies it; one with none left gives up. The search goes on only past
a candidate that consumed something, so the octets left on the tape bound
the iterations.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Search

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Search
open VG.Spec.RsaKeyGen (PrimeSearchResult)

/-- The counted candidates left compared with zero. -/
theorem k_guard {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) :
    WP isa (.block [ldf .x9 0]) s fun t =>
      SLive p original used k t ∧ isa.eval (.zero .x .x9) t = some (decide (k = 0)) := by
  have a := h.access
  have hw := h.header (j := 0) (v := BitVec.ofNat 64 k) (by simp [SPub.headers])
  simp only [Bignum.word, off] at hw
  have hk : k < 2 ^ 64 := by
    have := h.k_le
    have : p.remaining < 2 ^ 64 := by rw [← h.input.2]; exact BitVec.isLt _
    omega
  refine WP.mono (WP.keep [.x9] (Q := fun t =>
    isa.eval (.zero .x .x9) t = some (decide (k = 0)) ∧ t.mem = s.mem) ?_ (by decide) (by decide)
    (by decide +kernel)) fun _ ⟨⟨he, hm⟩, kt⟩ => ⟨h.keep kt hm, he⟩
  brun [ldf, h.x19, hw, a.ld 0 (by decide), a.ld0]
  simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq,
    ofNat_beq_zero' hk]

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

theorem result_status_lt (r : PrimeSearchResult) : r.status < 5 := by
  simp only [Spec.Entropy.Result.status, Spec.Entropy.Outcome.status]; split <;> decide

theorem result_status_ne (r : PrimeSearchResult) : r.status ≠ 4 := by
  simp only [Spec.Entropy.Result.status, Spec.Entropy.Outcome.status]; split <;> decide

theorem done_loop_guard {p : SPub} {original s : State} {r : PrimeSearchResult}
    (h : SDone p original r s) :
    WP isa (.block [ldf .x9 14, .subImm .x .x9 .x9 4]) s fun t =>
      isa.eval (.zero .x .x9) t = some false ∧ SDone p original r t := by
  have a := CtlAccess.of_scr (h.input.frame_scr h.wr)
  refine WP.mono (status_guard a h.x19 h.status (result_status_lt r)) fun t ⟨⟨he, hm⟩, k⟩ =>
    ⟨?_, h.keep k hm⟩
  rw [he, decide_eq_false (result_status_ne r)]

theorem live_loop_guard {p : SPub} {original s : State} {used k : Nat}
    (h : SLive p original used k s) (hs : word s.mem p.F 112 = 4) :
    WP isa (.block [ldf .x9 14, .subImm .x .x9 .x9 4]) s fun t =>
      isa.eval (.zero .x .x9) t = some true ∧ SLive p original used k t :=
  WP.mono (status_guard (st := 4) h.access h.x19 hs (by decide))
    fun _ ⟨⟨he, hm⟩, k⟩ => ⟨he, h.keep k hm⟩

/-- The loop's state: the search from octet `used`, with `k` counted
candidates left, leads to `final`; `n` bounds the iterations left. -/
def SInvariant (p : SPub) (original : State) (final : PrimeSearchResult) (n : Nat) (s : State) : Prop :=
  ∃ used k, n = p.randLen - used + 1 ∧ SIter p original final used k s

theorem search_iteration (c : Cand) {p : SPub} {original s : State}
    {final : PrimeSearchResult} {n : Nat}
    (h : SInvariant p original final n s) :
    WP isa (iteration c.call) s fun t =>
      (isa.eval (.zero .x .x9) t = some false ∧ SDone p original final t) ∨
      (isa.eval (.zero .x .x9) t = some true ∧ ∃ m < n, SInvariant p original final m t) := by
  obtain ⟨used, k, hn, h, tr, hfinal⟩ := h
  have done : ∀ t, SDone p original final t →
      WP isa (.block [ldf .x9 14, .subImm .x .x9 .x9 4]) t fun t =>
        (isa.eval (.zero .x .x9) t = some false ∧ SDone p original final t) ∨
        (isa.eval (.zero .x .x9) t = some true ∧ ∃ m < n, SInvariant p original final m t) :=
    fun _ hd => WP.mono (done_loop_guard hd) fun _ ⟨hq, hdq⟩ => Or.inl ⟨hq, hdq⟩
  unfold iteration
  refine WP.seq (WP.mono (k_guard h) fun u ⟨hu, he⟩ => ?_)
  apply WP.seq
  refine WP.ite (decide (k = 0)) he ?_ ?_
  · intro hz
    have hz' := of_decide_eq_true hz
    subst hz'
    refine WP.mono (search_exhausted hu (result := final) ?_) fun t ht => done t ht
    rw [hfinal, tailOf, SPub.tail, VG.Proof.RsaKeyGen.Search.search_zero]
    rfl
  intro hnz
  have hk : k ≠ 0 := of_decide_eq_false hnz
  refine WP.seq (WP.mono (search_candidate_run c hu) fun t ⟨ht, hp⟩ => ?_)
  refine WP.mono (search_classify ⟨ht, tr, hfinal⟩ hk hp) fun q hq => ?_
  unfold SClassified at hq
  by_cases hc : Continues p original used k
  · simp only [hc, ite_true] at hq
    obtain ⟨⟨hql, hqt⟩, h4⟩ := hq
    have hu' := hql.used_le
    refine WP.mono (live_loop_guard hql h4) fun z ⟨hz, hzl⟩ => Or.inr ⟨hz, _, ?_,
      used + candUsed p original used, _, rfl, hzl, hqt⟩
    have := hc.2.2
    omega
  · simp only [hc, ite_false] at hq
    exact done q hq

theorem search_loop (c : Cand) {p : SPub} {original s : State}
    {final : PrimeSearchResult} {n : Nat}
    (h : SInvariant p original final n s) :
    WP isa (.loop (iteration c.call) (.zero .x .x9)) s (SDone p original final) :=
  WP.loop (M := isa) (body := iteration c.call) (c := .zero .x .x9)
    (Q := SDone p original final) (SInvariant p original final)
    (fun _ _ h => search_iteration c h) n s h

end VG.Proof.RsaKeyGen.AArch64.Search
