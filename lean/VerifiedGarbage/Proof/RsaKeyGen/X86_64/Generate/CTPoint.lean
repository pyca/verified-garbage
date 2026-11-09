module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Loop
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Spec.RsaKeyGen.GenerationAgrees

/-! # Where two runs of the loop are

Two runs at the same point (`GenPoint`) agree on the public descriptor, the
octets consumed, the progress' public words (the generations left, the
phase's word and the counted candidates left), the state's request word and
the trace still to come, which each run's own key search from there gives.
The trace's first entry is the prime search's status, consumption, octets
left and trace, and, after `q`'s, the key's status: what each step does
follows from it (`gen_ct_step`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

structure GenPoint where
  inputs : GenPublic
  used : Nat
  left : Nat
  ph : Nat
  remaining : Nat
  req : BitVec 64
  trace : List Nat

/-- A run's progress `st` from `original`, at the point. -/
def AtPoint (q : GenPoint) (original : State) (st : KeyProgress) : Prop :=
  st.left = q.left ∧ phaseWord st.phase = q.ph ∧ st.remaining = q.remaining ∧
    (tailOf q.inputs original q.used st).trace = q.trace

/-- A loop state at the point. -/
def GenCTL (q : GenPoint) (s : State) : Prop :=
  ∃ original st, AtPoint q original st ∧ GenLive q.inputs original q.used st s ∧
    word s.mem q.inputs.stp 24 = q.req

/-! ## The first step, from the trace -/

abbrev GenPoint.status (q : GenPoint) : Nat := traceStatus q.trace
abbrev GenPoint.cand (q : GenPoint) : Nat := traceUsed q.trace
abbrev GenPoint.key (q : GenPoint) : Nat := traceKey q.trace

/-- Whether the key search goes on past the point's step. -/
def GenPoint.continues (q : GenPoint) : Prop :=
  (q.status = 3 ∧ ¬q.left < 2) ∨ (q.status = 1 ∧ q.cand ≠ 0 ∧ (q.ph = 0 ∨ q.key = 2))

/-- The point past the step, when the key search goes on. -/
def GenPoint.next (q : GenPoint) : GenPoint :=
  ⟨q.inputs, q.used + q.cand, if q.status = 3 then q.left - 1 else q.left,
    if q.status = 1 ∧ q.ph = 0 then 1 else 0, limitOf q.inputs.L q.inputs.eB, BitVec.ofNat 64 0,
    q.trace.drop (traceEntry q.trace + if q.status = 1 ∧ q.ph ≠ 0 then 2 else 0)⟩

section

variable {q : GenPoint} {original s : State} {st : KeyProgress}

theorem AtPoint.entry (h : AtPoint q original st) :
    ∃ rest, q.trace = primeEntry (rOf q.inputs original q.used st) ++ rest := by
  obtain ⟨rest, hr⟩ := keySearch_trace (L := q.inputs.L) (eB := q.inputs.eB) st ((genRand original).drop q.used)
  exact ⟨rest, h.2.2.2.symm.trans hr⟩

theorem AtPoint.status (h : AtPoint q original st) : (rOf q.inputs original q.used st).status = q.status := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [GenPoint.status, hr, (primeEntry_facts _ rest).1]

theorem AtPoint.cand (h : AtPoint q original st) : (rOf q.inputs original q.used st).used = q.cand := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [GenPoint.cand, hr, (primeEntry_facts _ rest).2.1]

theorem AtPoint.available (h : AtPoint q original st) :
    (rOf q.inputs original q.used st).available = traceAvailable q.trace := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [hr, (primeEntry_facts _ rest).2.2.1]

theorem AtPoint.prime (h : AtPoint q original st) : (rOf q.inputs original q.used st).trace = tracePrime q.trace := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [hr, (primeEntry_facts _ rest).2.2.2.1]

theorem AtPoint.entryLen (h : AtPoint q original st) :
    (primeEntry (rOf q.inputs original q.used st)).length = traceEntry q.trace := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [hr, (primeEntry_facts _ rest).2.2.2.2]

/-- After `q`'s search accepted a prime, the key's status. -/
theorem AtPoint.keyStatus (h : AtPoint q original st)
    (hle : q.used + (rOf q.inputs original q.used st).used ≤ q.inputs.randLen)
    (hrl : (genRand original).length = q.inputs.randLen) {c : Nat}
    {pB : List Byte} (ho : (rOf q.inputs original q.used st).outcome = .accepted c)
    (hpos : 0 < (rOf q.inputs original q.used st).used) (hph : st.phase = .q pB) :
    keyResultStatus (keyFromPrimes (16 * q.inputs.L) (Spec.Rsa.os2ip q.inputs.eB) (Spec.Rsa.os2ip pB)
      (Spec.Rsa.os2ip (Spec.Rsa.i2osp c q.inputs.L))) = q.key := by
  have hrest : (rOf q.inputs original q.used st).used ≤ ((genRand original).drop q.used).length := by
    rw [List.length_drop, hrl]; omega
  obtain ⟨rest, hr⟩ := keySearch_trace_key (L := q.inputs.L) (eB := q.inputs.eB) ho (drop_lt hpos hrest) hph
  rw [GenPoint.key, ← h.2.2.2, tailOf, hr, primeEntry_key]

theorem keyResultStatus_two (k : Except Failure Key ⊕ Unit) : keyResultStatus k = 2 ↔ k = .inr () := by
  rcases k with (k | k) | ⟨⟩ <;> simp [keyResultStatus]

theorem continues_iff (h : AtPoint q original st) (hl : GenFrame q.inputs original q.used st s) :
    ContSpec q.inputs original q.used st ↔ q.continues := by
  have hs := h.status
  have hc := h.cand
  have hleft := h.1
  have hph := h.2.1
  unfold ContSpec GenPoint.continues
  rw [← hs, ← hc, ← hleft, ← hph]
  cases ho : (rOf q.inputs original q.used st).outcome with
  | entropy k a => simp [rOf_status, ho, Spec.Entropy.Outcome.status]
  | exhausted => simp [rOf_status, ho, Spec.Entropy.Outcome.status]
  | accepted c =>
    have hs1 : (rOf q.inputs original q.used st).status = 1 := by rw [rOf_status, ho]; rfl
    rw [hs1]
    by_cases h0 : (rOf q.inputs original q.used st).used = 0
    · simp [h0]
    · cases hp : st.phase with
      | p => simp [h0, phaseWord]
      | q pB =>
        have hk := h.keyStatus (rOf_used_le hl) (genRand_length hl) ho (by omega) hp
        rw [← hk]
        simp [h0, phaseWord, keyResultStatus_two]

end

/-! ## A step -/

/-- After an iteration: the next point and the loop's condition, or its end. -/
def GenCTStep (q : GenPoint) (t : State) : Prop :=
  (q.continues ∧ eval .e t = some true ∧ GenCTL q.next t) ∨ (¬q.continues ∧ eval .e t = some false)

theorem next_point {q : GenPoint} {original t : State} {st : KeyProgress} {final : KeySearchResult}
    (h : AtPoint q original st) (hc : Cont q.inputs original final q.used st t) : GenCTL q.next t := by
  obtain ⟨-, hreq, ⟨st', e, hlive, -, htail, hrem, hnext⟩, -⟩ := hc
  have hs := h.status
  have hcd := h.cand
  obtain ⟨hleft, hph, -, htr⟩ := h
  refine ⟨original, st', ⟨?_, ?_, ?_, ?_⟩, by rw [GenPoint.next, ← hcd]; exact hlive, hreq⟩
  all_goals simp only [GenPoint.next]
  · rcases hnext with ⟨ho, hl, -, -⟩ | ⟨c, ho, -, hl, -, -⟩ | ⟨c, pB, ho, -, hl, -, -⟩ <;>
      rw [← hs, rOf_status, ho] <;> simp [hl, hleft, Spec.Entropy.Outcome.status]
  · rcases hnext with ⟨ho, -, hp, -⟩ | ⟨c, ho, hp, -, hp', -⟩ | ⟨c, pB, ho, hp, -, hp', -⟩
    · rw [← hs, rOf_status, ho, hp]; simp [Spec.Entropy.Outcome.status, phaseWord]
    · rw [← hs, rOf_status, ho, hp', ← hph, hp]; simp [Spec.Entropy.Outcome.status, phaseWord]
    · rw [← hs, rOf_status, ho, hp', ← hph, hp]; simp [Spec.Entropy.Outcome.status, phaseWord]
  · exact hrem
  · rw [← hcd, ← htr, htail]
    simp only [Spec.Entropy.Result.consume, List.drop_append]
    rcases hnext with ⟨ho, -, -, rfl⟩ | ⟨c, ho, hp, -, -, rfl⟩ | ⟨c, pB, ho, hp, -, -, rfl⟩
    · rw [← hs, rOf_status, ho]; simp [Spec.Entropy.Outcome.status]
    · rw [← hs, rOf_status, ho, ← hph, hp]; simp [Spec.Entropy.Outcome.status, phaseWord]
    · rw [← hs, rOf_status, ho, ← hph, hp]; simp [Spec.Entropy.Outcome.status, phaseWord, List.length_append]

theorem gen_ct_step [Key.KeyProof] (v : RoundImpl) (q : GenPoint) (s : State) (h : GenCTL q s) :
    WP isa (iteration (searchCall v) keyCall) s (GenCTStep q) := by
  obtain ⟨o, st, ha, hl, -⟩ := h
  have hi : GenIter q.inputs o ((tailOf q.inputs o q.used st).consume q.used []) q.used st s := ⟨hl, [], rfl⟩
  unfold iteration
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (search_run v hl) fun t hs => ?_)
  refine WP.seq (WP.mono (classify_ok hi hs) fun u hc => ?_)
  rcases hc with ⟨hcs, hct⟩ | ⟨hcs, hd⟩
  · obtain ⟨o', st', ha', hl', hr'⟩ := next_point ha hct
    refine WP.mono (status_guard hl'.toGenFrame hct.status (by decide)) fun x ⟨⟨hx, hmem⟩, k⟩ =>
      .inl ⟨(continues_iff ha hl.toGenFrame).mp hcs, hx, o', st', ha', ⟨hl'.toGenFrame.keep hmem k.2.1 k.2.2
        (fun r hr => k.gpr (by revert r; decide)), by rw [hmem]; exact hl'.key⟩, by rw [hmem]; exact hr'⟩
  · have hlt := keyStatus_lt ((tailOf q.inputs o q.used st).consume q.used [])
    refine WP.mono (status_guard hd.1 hd.2.1 (by omega)) fun x ⟨⟨hx, _⟩, _⟩ =>
      .inr ⟨fun h => hcs ((continues_iff ha hl.toGenFrame).mpr h), ?_⟩
    rw [hx]; congr 1; simp only [decide_eq_false_iff_not]; omega

end VG.Proof.RsaKeyGen.X86_64.Generate
