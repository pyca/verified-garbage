module
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Attempt
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Classify

import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Guards
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.AttemptStep
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Exits

/-! # Total correctness of the key-generation controller's loop -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.KeyGeneration
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

/-- A finished search's state depends on its result's outcome and octets
consumed, not on its statuses. -/
theorem KeyDone.congr {p : KeyPublic} {original s : State} {r r' : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original r s) (ho : r.outcome = r'.outcome) (hu : r.used = r'.used) :
    KeyDone p original r' s := by
  have hs : r.status = r'.status := by unfold Spec.Ffdh.KeySearchResult.status; rw [ho]
  have hr : r.retries = r'.retries := by unfold Spec.Ffdh.KeySearchResult.retries; rw [ho]
  refine ⟨h.input, h.rd, h.wr, h.rsp, h.r12, h.saved, h.savedR12, h.usedPtr,
    by rw [← hu]; exact h.used, by rw [← hs]; exact h.status, ?_, ?_⟩
  · rw [h.policy]; unfold KeyPublic.policy; rw [hs, hr]
  · have ho' := h.output; unfold KeyOutput at ho' ⊢; rw [← ho]; exact ho'

/-- The loop's state: the search from octet `used`, with `keys` and `scalars`
left, leads to the expected result. -/
def KeyInvariant (p : KeyPublic) (original : State) (expected : Spec.Ffdh.KeySearchResult)
    (n : Nat) (s : State) : Prop :=
  ∃ used keys scalars, n = 128 * keys + scalars + 1 ∧ KeyLive p original used keys scalars s ∧
    expected.outcome = (p.tail (keyRand original) used keys scalars).outcome ∧
    expected.used = (p.tail (keyRand original) used keys scalars).used

theorem key_iteration (v : RoundImpl) {p : KeyPublic} {original s : State}
    {expected : Spec.Ffdh.KeySearchResult} {n : Nat}
    (h : KeyInvariant p original expected n s) :
    WP isa (iteration (attemptCall v)) s fun t =>
      (eval .e t = some false ∧ KeyDone p original expected t) ∨
      (eval .e t = some true ∧ ∃ m < n, KeyInvariant p original expected m t) := by
  obtain ⟨used, keys, scalars, hn, h, ho, hu⟩ := h
  have hlen : (keyRand original).length = p.randLen := by
    rw [← h.random]; simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have done : ∀ (r : Spec.Ffdh.KeySearchResult) t, KeyDone p original r t →
      r.outcome = (p.tail (keyRand original) used keys scalars).outcome →
      r.used = (p.tail (keyRand original) used keys scalars).used →
      WP isa (.block [.mov .rax (.mem (field 14)), .alu .cmp .rax (.imm 4)]) t fun t =>
        (eval .e t = some false ∧ KeyDone p original expected t) ∨
        (eval .e t = some true ∧ ∃ m < n, KeyInvariant p original expected m t) :=
    fun _ _ hd hro hru => WP.mono (done_loop_guard hd) fun _ ⟨hq, hdq⟩ =>
      Or.inl ⟨hq, hdq.congr (hro.trans ho.symm) (hru.trans hu.symm)⟩
  unfold iteration
  change WP isa (.seq _ (.seq _ _)) s _
  refine WP.seq (WP.mono (keys_guard h) fun u ⟨hu1, he⟩ => ?_)
  apply WP.seq
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
  · intro hshort
    have hr : (keyRand original).length - used < p.len := by
      rw [hlen]; exact of_decide_eq_true hshort
    refine WP.mono (key_request hu3) fun t ht => done _ t ht ?_ ?_ <;>
      simp only [KeyPublic.tail, keyTail_short hk hs hr]
  intro hlong
  have hroom : used + p.len ≤ p.randLen := by
    have := of_decide_eq_false hlong; have := h.used_le; omega
  have hr : p.len ≤ (keyRand original).length - used := by rw [hlen]; omega
  refine WP.seq (WP.mono (key_attempt_run v hu3 hroom) fun t ⟨ht, hp⟩ => ?_)
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

theorem key_loop (v : RoundImpl) {p : KeyPublic} {original s : State}
    {expected : Spec.Ffdh.KeySearchResult} {n : Nat}
    (h : KeyInvariant p original expected n s) :
    WP isa (.loop (iteration (attemptCall v)) .e) s (KeyDone p original expected) :=
  WP.loop (M := isa) (body := iteration (attemptCall v)) (c := .e)
    (Q := KeyDone p original expected) (KeyInvariant p original expected)
    (fun _ _ h => key_iteration v h) n s h

end VG.Proof.Ffdh.X86_64.KeyGeneration
