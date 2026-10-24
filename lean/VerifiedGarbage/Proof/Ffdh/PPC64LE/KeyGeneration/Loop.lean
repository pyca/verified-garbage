module
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Classify

import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Guards
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Live
import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Call
import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Writes

/-! # Total correctness of the key-generation controller's loop (PPC64LE) -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.KeyGeneration

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Proof.Ffdh.KeyGeneration
open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search

/-- The loop's state: the search from octet `used`, with `keys` and `scalars`
left, leads to the expected result. -/
def KeyInvariant (p : KeyPublic) (original : State) (expected : Spec.Ffdh.KeySearchResult)
    (n : Nat) (s : State) : Prop :=
  ∃ used keys scalars, n = 128 * keys + scalars + 1 ∧ KeyLive p original used keys scalars s ∧
    expected.outcome = (p.tail (keyRand original) used keys scalars).outcome ∧
    expected.used = (p.tail (keyRand original) used keys scalars).used

theorem KeyLive.rand_length {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) : (keyRand original).length = p.randLen := by
  rw [← h.random]; simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]

theorem key_iteration (a : Attempt) {p : KeyPublic} {original s : State}
    {expected : Spec.Ffdh.KeySearchResult} {n : Nat}
    (h : KeyInvariant p original expected n s) :
    WP isa (iteration a.call) s fun t =>
      (isa.eval (.zero .d .r9) t = some false ∧ KeyDone p original expected t) ∨
      (isa.eval (.zero .d .r9) t = some true ∧ ∃ m < n, KeyInvariant p original expected m t) := by
  obtain ⟨used, keys, scalars, hn, h, ho, hu⟩ := h
  have hlen := h.rand_length
  have done : ∀ (r : Spec.Ffdh.KeySearchResult) t, KeyDone p original r t →
      r.outcome = (p.tail (keyRand original) used keys scalars).outcome →
      r.used = (p.tail (keyRand original) used keys scalars).used →
      WP isa (.block [ldf .r9 14, .subi .r9 .r9 4]) t fun t =>
        (isa.eval (.zero .d .r9) t = some false ∧ KeyDone p original expected t) ∨
        (isa.eval (.zero .d .r9) t = some true ∧ ∃ m < n, KeyInvariant p original expected m t) :=
    fun _ _ hd hro hru => WP.mono (done_loop_guard hd) fun _ ⟨hq, hdq⟩ =>
      Or.inl ⟨hq, hdq.congr (hro.trans ho.symm) (hru.trans hu.symm)⟩
  unfold iteration
  refine WP.seq (WP.mono (keys_guard h) fun u ⟨hu1, he⟩ => ?_)
  apply WP.seq
  unfold branch
  refine WP.ite (decide (keys = 0)) he ?_ ?_
  · intro hz
    have hz' := of_decide_eq_true hz
    refine WP.mono (key_exhausted hu1) fun t ht => done _ t ht ?_ ?_ <;>
      simp only [KeyPublic.tail, keyTail_exhausted (Or.inl hz')]
  intro hnz
  have hk : keys ≠ 0 := of_decide_eq_false hnz
  refine WP.seq (WP.mono (scalars_guard hu1) fun u ⟨hu2, he2⟩ => ?_)
  refine WP.ite (decide (scalars = 0)) he2 ?_ ?_
  · intro hz
    have hz' := of_decide_eq_true hz
    refine WP.mono (key_exhausted hu2) fun t ht => done _ t ht ?_ ?_ <;>
      simp only [KeyPublic.tail, keyTail_exhausted (Or.inr hz')]
  intro hnz2
  have hs : scalars ≠ 0 := of_decide_eq_false hnz2
  unfold attemptOrRequest
  refine WP.seq (WP.mono (room_guard hu2) fun u ⟨hu3, hb⟩ => ?_)
  refine WP.ite _ hb ?_ ?_
  swap
  · intro hshort
    have hr : (keyRand original).length - used < p.len := by
      rw [hlen]; have := of_decide_eq_false hshort; omega
    refine WP.mono (key_request hu3) fun t ht => done _ t ht ?_ ?_ <;>
      simp only [KeyPublic.tail, keyTail_short hk hs hr]
  intro hlong
  have hroom : used + p.len ≤ p.randLen := by
    have := of_decide_eq_true hlong; have := h.used_le; omega
  have hr : p.len ≤ (keyRand original).length - used := by rw [hlen]; omega
  refine WP.seq (WP.mono (key_attempt_run a hu3 hroom) fun t ⟨ht, hp⟩ => ?_)
  refine WP.mono (key_classify ht hroom (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hs) hp)
    fun q hq => ?_
  rcases attemptStatus_cases p.a p.len ((keyRand original).drop used) with h1 | h2 | h3
  · simp only [KeyClassified, h1, ite_true] at hq
    refine done _ q hq ?_ ?_ <;> simp only [KeyPublic.tail, keyTail_accepted hk hs hr h1] <;> rfl
  · simp only [KeyClassified, h2, Nat.reduceEqDiff, ite_true, ite_false] at hq
    refine WP.mono (live_loop_guard hq.1 hq.2) fun z ⟨hz, hzl⟩ => Or.inr ⟨hz, _, ?_,
      used + p.len, keys, scalars - 1, rfl, hzl, ?_, ?_⟩
    · omega_using [hn, hs]
    · rw [ho]; simp only [KeyPublic.tail, keyTail_scalar hk hs hr h2]
    · rw [hu]; simp only [KeyPublic.tail, keyTail_scalar hk hs hr h2]
  · simp only [KeyClassified, h3, Nat.reduceEqDiff, ite_false] at hq
    refine WP.mono (live_loop_guard hq.1 hq.2) fun z ⟨hz, hzl⟩ => Or.inr ⟨hz, _, ?_,
      used + p.len, keys - 1, 128, rfl, hzl, ?_, ?_⟩
    · omega_using [hn, hk, hs]
    · rw [ho]; simp only [KeyPublic.tail, keyTail_public hk hs hr h3]
    · rw [hu]; simp only [KeyPublic.tail, keyTail_public hk hs hr h3]

theorem key_loop (a : Attempt) {p : KeyPublic} {original s : State}
    {expected : Spec.Ffdh.KeySearchResult} {n : Nat}
    (h : KeyInvariant p original expected n s) :
    WP isa (.loop (iteration a.call) (.zero .d .r9)) s (KeyDone p original expected) :=
  WP.loop (M := isa) (body := iteration a.call) (c := .zero .d .r9)
    (Q := KeyDone p original expected) (KeyInvariant p original expected)
    (fun _ _ h => key_iteration a h) n s h

end VG.Proof.Ffdh.PPC64LE.KeyGeneration
