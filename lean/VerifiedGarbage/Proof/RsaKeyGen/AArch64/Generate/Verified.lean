module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Generate.Implies
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Generate.Loop
import VerifiedGarbage.Proof.Framework.AArch64.Depth
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Generate.Loop
meta import VerifiedGarbage.Proof.Framework.AArch64.Depth
import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.CT
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.EntropyRequest
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.CT
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.EntropyRequest
import VerifiedGarbage.Spec.RsaKeyGen.GenerationAgrees
meta import VerifiedGarbage.Spec.RsaKeyGen.GenerationAgrees

/-! ### `RsaKeyGen.AArch64.Generate.CT`, which only this module used -/

section

/-! ### `RsaKeyGen.AArch64.Generate.CTClassify`, which only this module used -/

section

/-! ### `RsaKeyGen.AArch64.Generate.CTCalls`, which only this module used -/

section

/-! ### `RsaKeyGen.AArch64.Generate.CTPoint`, which only this module used -/

section

/-! # Where two runs of the loop are (AArch64)

Two runs at the same point (`GenPoint`) agree on the public descriptor, the
octets consumed, the progress' public words (the generations left, the
phase's word and the counted candidates left), the state's request word and
the trace still to come, which each run's own key search from there gives.
The trace's first entry is the prime search's status, consumption, octets
left and trace, and, after `q`'s, the key's status: what each step does
follows from it (`gen_ct_step`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MillerRabin.AArch64 (RoundImpl)
open VG.Impl.RsaKeyGen.AArch64.Generate
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
    rw [List.length_drop, hrl]; omega_using [hle]
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
        have hk := h.keyStatus (rOf_used_le hl) (genRand_length hl) ho (by omega_using [h0]) hp
        rw [← hk]
        simp [h0, phaseWord, keyResultStatus_two]

end

/-! ## A step -/

/-- After an iteration: the next point and the loop's condition, or its end. -/
def GenCTStep (q : GenPoint) (t : State) : Prop :=
  (q.continues ∧ isa.eval (.zero .x .x9) t = some true ∧ GenCTL q.next t) ∨
    (¬q.continues ∧ isa.eval (.zero .x .x9) t = some false)

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
  simp only [VG.Impl.Bignum.AArch64.seqs]
  refine WP.seq (WP.mono (search_run v hl) fun t hs => ?_)
  refine WP.seq (WP.mono (classify_ok hi hs) fun u hc => ?_)
  rcases hc with ⟨hcs, hct⟩ | ⟨hcs, hd⟩
  · obtain ⟨o', st', ha', hl', hr'⟩ := next_point ha hct
    refine WP.mono (status_guard hl'.toGenFrame hct.status (by decide)) fun x ⟨⟨hx, hmem⟩, k⟩ =>
      .inl ⟨(continues_iff ha hl.toGenFrame).mp hcs, hx, o', st', ha', ⟨hl'.toGenFrame.keep k hmem,
        by rw [hmem]; exact hl'.key⟩, by rw [hmem]; exact hr'⟩
  · have hlt := keyStatus_lt ((tailOf q.inputs o q.used st).consume q.used [])
    refine WP.mono (status_guard hd.1 hd.2.1 (by omega_using [hlt])) fun x ⟨⟨hx, _⟩, _⟩ =>
      .inr ⟨fun h => hcs ((continues_iff ha hl.toGenFrame).mpr h), ?_⟩
    refine hx.trans ?_; congr 1; simp only [decide_eq_false_iff_not]; omega_using [hlt]

end VG.Proof.RsaKeyGen.AArch64.Generate

end

end

/-! # The calls' timing (AArch64)

The taint analysis tracks registers only, so a pointer loaded from the frame
is made public by what correctness says of it (`ldf_then`). The prime
search's and the key's arguments are the same in two runs at a point, and so
is what their contracts let their timing depend on — the search's status,
consumption, request and trace, and the key's status, all from the point's
trace.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MillerRabin.AArch64 (RoundImpl)
open VG.Impl.RsaKeyGen.AArch64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-! ## Frame states, and pointers loaded from the frame -/

/-- A frame state of some run with the public descriptor `p`. -/
def AnyFrame (p : GenPublic) (s : State) : Prop := ∃ original used st, GenFrame p original used st s

theorem GenCTL.any {q : GenPoint} {s : State} (h : GenCTL q s) : AnyFrame q.inputs s :=
  let ⟨o, st, _, hl, _⟩ := h; ⟨o, _, st, hl.toGenFrame⟩

theorem no_pins {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ h => absurd h List.not_mem_nil

/-- `Φ` gives frame states of `f a`: `x19` is the frame's base. -/
theorem frame_pins {α : Type} {Φ : α → State → Prop} (f : α → GenPublic)
    (hΦ : ∀ a s, Φ a s → s.gpr .x19 = (f a).F) : Pins Φ [.x19] := by
  intro a s t h₁ h₂ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact (hΦ a s h₁).trans (hΦ a t h₂).symm

theorem AnyFrame.x19 {p : GenPublic} {s : State} (h : AnyFrame p s) : s.gpr .x19 = p.F :=
  let ⟨_, _, _, g⟩ := h; g.x19

/-- Code the taint analysis checks with `x19` public, from frame states. -/
theorem frame_ct {α : Type} {Φ : α → State → Prop} {c : Prog isa} (f : α → GenPublic)
    (hΦ : ∀ a s, Φ a s → s.gpr .x19 = (f a).F) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.x19]) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_taint [.x19] (frame_pins f hΦ) h

/-- A block that first loads `r` from the frame's word `j`, which `Φ a` fixes
as `v a`: the rest is checked with `r` public too. -/
theorem ldf_then {α : Type} {Φ : α → State → Prop} {rest : List Instr} {r : Reg} {j : Nat} (hj : j < 20)
    (F v : α → BitVec 64) (rs : List Reg) (hpin : Pins Φ rs)
    (hld : ∀ a s, Φ a s → s.gpr .x19 = F a ∧ InRegions (s.rd ++ s.wr) (F a + BitVec.ofNat 64 (8 * j)) 8 ∧
      s.mem.readW (F a + BitVec.ofNat 64 (8 * j)) 64 = v a)
    {h₁ : VG.Taint.Hint VG.AArch64.Taint.T} (c₁ : (taint.check (Taint.ofRegs rs) (.block [ldf r j]) h₁).isSome = true)
    {h₂ : VG.Taint.Hint VG.AArch64.Taint.T} (c₂ : (taint.check (Taint.ofRegs (r :: rs)) (.block rest) h₂).isSome = true) :
    RelCT isa (Two Φ) (.block (ldf r j :: rest)) fun _ _ => True := by
  change RelCT isa (Two Φ) (.block ([ldf r j] ++ rest)) _
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun a t => ∃ s, Φ a s ∧ t = s.write .x r (v a))
    rs hpin c₁ fun a s h => ?_) (two_taint (r :: rs) ?_ c₂))
  · obtain ⟨h19, hin, hv⟩ := hld a s h
    have he : exec (ldf r j) s = some (s.write .x r (v a)) := by
      show exec (.ldr .x r .x19 (8 * j)) s = _
      rw [exec_ldr_x' (by omega_using [hj]) (by rw [h19]; exact hin), h19, hv]
    brun [he]
    exact ⟨s, h, rfl⟩
  · rintro a _ _ ⟨s₁, h₁, rfl⟩ ⟨s₂, h₂, rfl⟩ x hx
    rw [RegUpd.gpr_write, RegUpd.gpr_write]
    split
    · rfl
    · exact hpin a _ _ h₁ h₂ x ((List.mem_cons.mp hx).resolve_left (by assumption))

/-- A header word of a frame state. -/
theorem GenFrame.hdr {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {j : Nat} {v : BitVec 64} (hj : (j, v) ∈ p.headers used) (hj' : 8 * j + 8 ≤ 160) :
    s.gpr .x19 = p.F ∧ InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 (8 * j)) 8 ∧
      s.mem.readW (p.F + BitVec.ofNat 64 (8 * j)) 64 = v :=
  ⟨h.x19, h.frame_ld _ hj', h.headers (j, v) hj⟩

/-- The state's pointer, from a frame state. -/
theorem AnyFrame.stp {p : GenPublic} {s : State} (h : AnyFrame p s) :
    s.gpr .x19 = p.F ∧ InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 (8 * 7)) 8 ∧
      s.mem.readW (p.F + BitVec.ofNat 64 (8 * 7)) 64 = p.stp :=
  let ⟨_, _, _, g⟩ := h; g.hdr (by simp [GenPublic.headers]) (by decide)

theorem outOf_ph {p : GenPublic} {st₁ st₂ : KeyProgress} (h : phaseWord st₁.phase = phaseWord st₂.phase) :
    outOf p st₁ = outOf p st₂ := by
  unfold outOf; rw [h]

theorem plenOf_ph {p : GenPublic} {st₁ st₂ : KeyProgress} (h : phaseWord st₁.phase = phaseWord st₂.phase) :
    plenOf p st₁ = plenOf p st₂ := by
  unfold plenOf; rw [h]

/-! ## The prime search -/

/-- The search's entry, before the call. -/
def CallSCT (q : GenPoint) (u : State) : Prop :=
  ∃ original st s, AtPoint q original st ∧ GenLive q.inputs original q.used st s ∧
    word s.mem q.inputs.stp 24 = q.req ∧ SearchRegs q.inputs q.used st u ∧
    u.mem = writeFrame s.mem (callSp q.inputs) (callValues q.inputs q.used) ∧
    Keep searchArgRegs (allocated 32 s) u

/-- The search's exponent and state words at its entry. -/
theorem callS_state {p : GenPublic} {original s u : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s) (hu : u.sp = callSp p) (ha : SearchRegs p used st u)
    (hm : u.mem = writeFrame s.mem (callSp p) (callValues p used)) :
    Search.searchE (callS p used st u) = p.eB ∧
      Spec.Rsa.wordsAt (callS p used st u).mem (stackArg (callS p used st u) 3) 4 =
        [BitVec.ofNat 64 st.remaining, BitVec.ofNat 64 p.L, BitVec.ofNat 64 (primeEntropy p.L),
          word s.mem p.stp 24] := by
  have hf := h.input.cfacts
  have hfr := callS_frame (st := st) hm
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨-, -, -, sT, -⟩ := hst
  obtain ⟨-, -, -, a3⟩ := callS_args (used := used) (st := st) hu hm
  obtain ⟨-, -, -, r3, r4, -⟩ := ha
  have hword (d : Nat) (hd : d + 8 ≤ 56) : word (callS p used st u).mem p.stp d = word s.mem p.stp d :=
    hfr.readW (r := cS p) (Offset.contains_base _ hd (by have := hf.nT; omega_using [hd]))
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact sT) (by decide)
  refine ⟨?_, ?_⟩
  · simp only [Search.searchE, callS_gpr (by decide : Reg.x3 ∉ linkRegs), callS_gpr (by decide : Reg.x4 ∉ linkRegs),
      r3, r4, toNat_ofNat_lt (show 8 < 2 ^ 64 by decide)]
    rw [← h.state.e]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hfr.bytes (R := ⟨p.stp + BitVec.ofNat 64 48, 8⟩) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact sT.sub_left rE_sub) (by show 8 ≤ 2 ^ 64; decide)
      (List.mem_range.mp hi)
  · rw [a3]
    show [word _ p.stp (8 * 0), word _ p.stp (8 * 1), word _ p.stp (8 * 2), word _ p.stp (8 * 3)] = _
    rw [hword _ (by decide), hword _ (by decide), hword _ (by decide), hword _ (by decide)]
    have h0 := h.state.remaining
    have h1 := h.state.len
    have h2 := h.state.cap
    simp only [Nat.reduceMul] at h0 h1 h2 ⊢
    rw [h0, h1, h2]

theorem CallSCT.sp {q : GenPoint} {u : State} (h : CallSCT q u) : u.sp = callSp q.inputs := by
  obtain ⟨o, st, s, -, hl, -, -, -, k⟩ := h
  exact k.sp.trans (alloc32_sp hl.toGenFrame)

theorem search_call_ct (v : RoundImpl) : RelCT isa (Two CallSCT) (searchCall v) (fun _ _ => True) := by
  refine RelCT.callEx (k := Search.searchContract) (Search.search_correct (Search.Cand.ofRound v))
    (Search.search_constantTime (Search.Cand.ofRound v)) fun u₁ u₂ ⟨q, h₁, h₂, _⟩ => ?_
  have hu₁ := h₁.sp
  have hu₂ := h₂.sp
  obtain ⟨o₁, st₁, s₁, a₁, l₁, w₁, r₁, m₁, k₁⟩ := h₁
  obtain ⟨o₂, st₂, s₂, a₂, l₂, w₂, r₂, m₂, k₂⟩ := h₂
  have hph : phaseWord st₁.phase = phaseWord st₂.phase := a₁.2.1.trans a₂.2.1.symm
  have hres₁ := callS_result l₁ hu₁ r₁ m₁
  have hres₂ := callS_result l₂ hu₂ r₂ m₂
  obtain ⟨e₁, ws₁⟩ := callS_state l₁ hu₁ r₁ m₁
  obtain ⟨e₂, ws₂⟩ := callS_state l₂ hu₂ r₂ m₂
  have hlen₁ : Search.searchLen (callS q.inputs q.used st₁ u₁) = q.inputs.L := by
    simp only [Search.searchLen, callS_gpr (by decide : Reg.x1 ∉ linkRegs), r₁.2.1]
    exact toNat_ofNat_lt (by have := l₁.input.cfacts.len.2.1; omega_using [this])
  have hlen₂ : Search.searchLen (callS q.inputs q.used st₂ u₂) = q.inputs.L := by
    simp only [Search.searchLen, callS_gpr (by decide : Reg.x1 ∉ linkRegs), r₂.2.1]
    exact toNat_ofNat_lt (by have := l₂.input.cfacts.len.2.1; omega_using [this])
  obtain ⟨b0, b1, b2, b3⟩ := callS_args (used := q.used) (st := st₁) hu₁ m₁
  obtain ⟨c0, c1, c2, c3⟩ := callS_args (used := q.used) (st := st₂) hu₂ m₂
  refine ⟨sReads q.inputs q.used st₁, sWrites q.inputs st₁, sReads q.inputs q.used st₂, sWrites q.inputs st₂,
    callS_pre l₁ hu₁ r₁ m₁, callS_pre l₂ hu₂ r₂ m₂, ?_,
    search_covers_reads l₁.toGenFrame k₁.rd k₁.wr, search_covers_writes l₁.toGenFrame k₁.wr,
    search_covers_reads l₂.toGenFrame k₂.rd k₂.wr, search_covers_writes l₂.toGenFrame k₂.wr⟩
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7⟩ := r₁
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7⟩ := r₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, e₁.trans e₂.symm, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.withRegions_sp, State.callEntry_sp, hu₁, hu₂]
  · rw [callS_gpr (by decide), callS_gpr (by decide), d0, f0, outOf_ph hph]
  · rw [callS_gpr (by decide), callS_gpr (by decide), d1, f1]
  · rw [callS_gpr (by decide), callS_gpr (by decide), d2, f2]
  · rw [callS_gpr (by decide), callS_gpr (by decide), d3, f3]
  · rw [callS_gpr (by decide), callS_gpr (by decide), d4, f4]
  · rw [callS_gpr (by decide), callS_gpr (by decide), d5, f5]
  · rw [callS_gpr (by decide), callS_gpr (by decide), d6, f6, plenOf_ph hph]
  · rw [callS_gpr (by decide), callS_gpr (by decide), d7, f7]
  · match j, hj with
    | 0, _ => rw [b0, c0]
    | 1, _ => rw [b1, c1]
    | 2, _ => rw [b2, c2]
    | 3, _ => rw [b3, c3]
  · rw [ws₁, ws₂, a₁.2.2.1, a₂.2.2.1, w₁, w₂]
  · rw [hres₁, hres₂, a₁.status, a₂.status]
  · rw [hres₁, hres₂, a₁.cand, a₂.cand]
  · rw [hlen₁, hlen₂, hres₁, hres₂]
    exact Entropy.requested_congr (a₁.status.trans a₂.status.symm) (a₁.available.trans a₂.available.symm)
  · rw [hres₁, hres₂, a₁.prime, a₂.prime]

/-- A loop state at the point, past the allocation of the search's frame. -/
def AllocSCT (q : GenPoint) (u : State) : Prop := ∃ s, GenCTL q s ∧ u = allocated 32 s

theorem search_run_ct (v : RoundImpl) :
    RelCT isa (Two GenCTL) (searchRun (searchCall v)) (fun _ _ => True) := by
  unfold searchRun
  apply RelCT.alloc
  have hct : RelCT isa (Two AllocSCT) (.block searchArgs) fun _ _ => True :=
    ldf_then (r := .x8) (j := 7) (by decide) (fun q => q.inputs.F) (fun q => q.inputs.stp) [.x19]
      (frame_pins (fun q => q.inputs) fun q u ⟨s, h, e⟩ => by subst e; exact h.any.x19)
      (fun q u ⟨s, ⟨o, st, _, hl, _⟩, e⟩ => by
        subst e
        exact ⟨hl.x19, hl.frame_ld' rfl _ (by decide), hl.headers (7, q.inputs.stp) (by simp [GenPublic.headers])⟩)
      (by taint_decide) (by taint_decide)
  have ha : RelCT isa (Two AllocSCT) (.block searchArgs) (Two CallSCT) :=
    two_post hct fun q u ⟨s, ⟨o, st, ha, hl, hw⟩, e⟩ => by
      subst e
      exact WP.mono (search_args_ok hl.toGenFrame) fun _ ⟨⟨hr, hm⟩, k⟩ => ⟨o, st, s, ha, hl, hw, hr, hm, k⟩
  refine (RelCT.seq ha (search_call_ct v)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocated, hsp]⟩

/-! ## The key -/

theorem keyStatus_keyOp (L : Nat) (eB pB qB : List Byte) :
    keyStatus (keyOp L eB pB qB) = keyResultStatus (keyFromPrimes (16 * L) (Spec.Rsa.os2ip eB)
      (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB)) := by
  unfold keyOp
  split <;> rename_i h <;> rw [h] <;> rfl

/-- After `q`'s search accepted a prime, at the point: the key's state. -/
def KeyCT (q : GenPoint) (u : State) : Prop :=
  ∃ original st final c pB, AtPoint q original st ∧ Mid q.inputs original final q.used st u ∧
    (rOf q.inputs original q.used st).outcome = .accepted c ∧ 0 < (rOf q.inputs original q.used st).used ∧
    st.phase = .q pB

theorem KeyCT.frame {q : GenPoint} {u : State} (h : KeyCT q u) : AnyFrame q.inputs u :=
  let ⟨o, _, _, _, _, _, hm, _⟩ := h; ⟨o, _, _, hm.frame⟩

/-- The key's status, from the point. -/
theorem KeyCT.status {q : GenPoint} {u : State} (h : KeyCT q u) : keyStatus (keyOf q.inputs u.mem) = q.key := by
  obtain ⟨o, st, final, c, pB, ha, hm, ho, hpos, hph⟩ := h
  have hs4 := hm.slot4
  have hs5 := hm.slot5
  rw [hph] at hs4 hs5
  simp only [outBytes, ho] at hs5
  simp only [keyOf, hs4, hs5, keyStatus_keyOp]
  exact ha.keyStatus hm.frame.used_le (genRand_length hm.frame) ho hpos hph

/-- The key's entry, before the call. -/
def CallKCT (q : GenPoint) (u : State) : Prop :=
  ∃ s, KeyCT q s ∧ KeyRegs q.inputs u ∧ u.mem = writeFrame s.mem (keySp q.inputs) (keyValues q.inputs) ∧
    Keep keyArgRegs (allocated 80 s) u

theorem key_call_ct [Key.KeyProof] : RelCT isa (Two CallKCT) keyCall (fun _ _ => True) := by
  refine RelCT.callEx (k := Key.keyA) Key.KeyProof.correct Key.KeyProof.ct fun u₁ u₂ ⟨q, h₁, h₂, _⟩ => ?_
  obtain ⟨s₁, c₁, r₁, m₁, k₁⟩ := h₁
  obtain ⟨s₂, c₂, r₂, m₂, k₂⟩ := h₂
  obtain ⟨o₁, _, _, _, _, _, hm₁, _⟩ := id c₁
  obtain ⟨o₂, _, _, _, _, _, hm₂, _⟩ := id c₂
  have g₁ := hm₁.frame
  have g₂ := hm₂.frame
  have hu₁ : u₁.sp = keySp q.inputs := k₁.sp.trans (alloc80_sp g₁)
  have hu₂ : u₂.sp = keySp q.inputs := k₂.sp.trans (alloc80_sp g₂)
  obtain ⟨res₁, e₁⟩ := callK_res g₁ hu₁ r₁ m₁
  obtain ⟨res₂, e₂⟩ := callK_res g₂ hu₂ r₂ m₂
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := callK_args (s := s₁) hu₁ m₁
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := callK_args (s := s₂) hu₂ m₂
  refine ⟨kReads q.inputs, kWrites q.inputs, kReads q.inputs, kWrites q.inputs,
    callK_pre g₁ hu₁ r₁ m₁, callK_pre g₂ hu₂ r₂ m₂, ?_,
    key_covers_reads g₁ k₁.rd k₁.wr, key_covers_writes g₁ k₁.wr,
    key_covers_reads g₂ k₂.rd k₂.wr, key_covers_writes g₂ k₂.wr⟩
  obtain ⟨x0₁, x1₁, x2₁, x3₁, x4₁, x5₁, x6₁, x7₁⟩ := r₁
  obtain ⟨x0₂, x1₂, x2₂, x3₂, x4₂, x5₂, x6₂, x7₂⟩ := r₂
  refine ⟨fun r hr => ?_, by simp only [State.withRegions_sp, State.callEntry_sp, hu₁, hu₂], fun i hi => ?_, ?_⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [callK_gpr (by decide), callK_gpr (by decide)]
    exacts [x0₁.trans x0₂.symm, x1₁.trans x1₂.symm, x2₁.trans x2₂.symm, x3₁.trans x3₂.symm, x4₁.trans x4₂.symm,
      x5₁.trans x5₂.symm, x6₁.trans x6₂.symm, x7₁.trans x7₂.symm]
  · match i, hi with
    | 0, _ => rw [b0, d0]
    | 1, _ => rw [b1, d1]
    | 2, _ => rw [b2, d2]
    | 3, _ => rw [b3, d3]
    | 4, _ => rw [b4, d4]
    | 5, _ => rw [b5, d5]
    | 6, _ => rw [b6, d6]
    | 7, _ => rw [b7, d7]
    | 8, _ => rw [b8, d8]
    | 9, _ => rw [b9, d9]
  · unfold Key.keyLeak
    rw [e₁, e₂, res₁, res₂, c₁.status, c₂.status]

/-- At the point, past the allocation of the key's frame. -/
def AllocKCT (q : GenPoint) (u : State) : Prop := ∃ s, KeyCT q s ∧ u = allocated 80 s

theorem key_run_ct [Key.KeyProof] : RelCT isa (Two KeyCT) (keyRun keyCall) (fun _ _ => True) := by
  unfold keyRun
  apply RelCT.alloc
  have ha : RelCT isa (Two AllocKCT) (.block keyArgs) (Two CallKCT) :=
    two_post (frame_ct (fun q => q.inputs) (fun q u ⟨s, h, e⟩ => by subst e; exact h.frame.x19)
      (by taint_decide))
      (fun q u ⟨s, hs, e⟩ => by
        subst e
        obtain ⟨o, _, _, _, _, _, hm, _⟩ := id hs
        exact WP.mono (key_args_ok hm.frame) fun _ ⟨⟨hr, hmem⟩, k⟩ => ⟨s, hs, hr, hmem, k⟩)
  refine (RelCT.seq ha key_call_ct).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocated, hsp]⟩

end VG.Proof.RsaKeyGen.AArch64.Generate

end

end

/-! # The classification's timing (AArch64)

After the search, every block's addresses are the frame's, the state's
pointer the frame holds, or the region to zero the frame holds; every test is
of the point's status, consumption, generations left, phase or key status.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.MillerRabin.AArch64 (RoundImpl)
open VG.Impl.RsaKeyGen.AArch64.Generate
open VG.Impl.Bignum.AArch64 (ld)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

theorem ev_false {r : Reg} {s : State} {b : Prop} [Decidable b]
    (he : isa.eval (.zero .x r) s = some (decide b)) (hf : isa.eval (.zero .x r) s = some false) : ¬b := fun h => by
  have hx : some (decide b) = some false := he.symm.trans hf
  simp [h] at hx

/-- The frame's base and the state's pointer in the frame. -/
def Hdr7 (p : GenPublic) (s : State) : Prop :=
  s.gpr .x19 = p.F ∧ InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 (8 * 7)) 8 ∧
    s.mem.readW (p.F + BitVec.ofNat 64 (8 * 7)) 64 = p.stp

/-! ## Blocks of the frame and the state -/

theorem nextPrime_ct {α : Type} {Φ : α → State → Prop} (f : α → GenPublic) (hΦ : ∀ a s, Φ a s → Hdr7 (f a) s)
    {phase : Nat} (hph : phase < 2) : RelCT isa (Two Φ) (.block (nextPrime phase)) fun _ _ => True := by
  obtain rfl | rfl : phase = 0 ∨ phase = 1 := by omega_using [hph]
  all_goals
  unfold nextPrime
  exact ldf_then (by decide) (fun a => (f a).F) (fun a => (f a).stp) [.x19] (frame_pins f fun a s h => (hΦ a s h).1)
    hΦ (by taint_decide) (by taint_decide)

theorem finishWith_ct {α : Type} {Φ : α → State → Prop} (f : α → GenPublic) (hΦ : ∀ a s, Φ a s → Hdr7 (f a) s)
    {status : Nat} (hs : status < 4) : RelCT isa (Two Φ) (.block (finishWith status)) fun _ _ => True := by
  obtain rfl | rfl | rfl | rfl : status = 0 ∨ status = 1 ∨ status = 2 ∨ status = 3 := by omega_using [hs]
  all_goals
  unfold finishWith
  exact ldf_then (by decide) (fun a => (f a).F) (fun a => (f a).stp) [.x19] (frame_pins f fun a s h => (hΦ a s h).1)
    hΦ (by taint_decide) (by taint_decide)

/-- Before `clear`: the region to zero, `len` octets at `op` in the key's
buffer, in the frame's words 12 and 13. -/
def ClearCT (a : GenPublic × Addr × Nat) (s : State) : Prop :=
  ∃ original used st, GenFrame a.1 original used st s ∧ word s.mem a.1.F (8 * 12) = a.2.1 ∧
    word s.mem a.1.F (8 * 13) = BitVec.ofNat 64 a.2.2 ∧ Region.Sub ⟨a.2.1, a.2.2⟩ (inKey original) ∧
    1 ≤ a.2.2 ∧ a.2.2 < 2 ^ 63

theorem clear_ct : RelCT isa (Two ClearCT) clear fun _ _ => True := by
  unfold clear
  refine RelCT.seq (two_piece (Ψ := fun a t => t.gpr .x1 = a.2.1 + BitVec.ofNat 64 0 ∧
    t.gpr .x2 = BitVec.ofNat 64 a.2.2) [.x19] (frame_pins Prod.fst fun _ _ ⟨_, _, _, g, _⟩ => g.x19)
    (by taint_decide) fun a s ⟨o, u, st, g, h12, h13, _⟩ => ?_) (two_taint [.x1, .x2] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide))
  have hl := g.frame_ld
  simp only [Bignum.word, off, Nat.reduceMul] at h12 h13
  brun [ldf, g.x19, imm64 (show 0 < 65536 by decide), hl 96 (by decide), hl 104 (by decide), h12, h13]

theorem clear_post (a : GenPublic × Addr × Nat) (s : State) (h : ClearCT a s) :
    WP isa clear s fun t => AnyFrame a.1 t := by
  obtain ⟨o, u, st, g, h12, h13, hsub, h1, hlt⟩ := h
  exact WP.mono (clear_ok g h12 h13 hsub h1 hlt) fun t ⟨g', _⟩ => ⟨o, u, st, g'⟩

theorem fail_ct {α : Type} {Φ : α → State → Prop} (f : α → GenPublic) (hΦ : ∀ a s, Φ a s → AnyFrame (f a) s)
    {status : Nat} (hs : status < 4) : RelCT isa (Two Φ) (fail status) fun _ _ => True := by
  unfold fail clearAll
  refine RelCT.seq (RelCT.seq (two_post (Ψ := fun a s => ClearCT (f a, (f a).kp, 9 * (f a).L) s)
    (frame_ct f (fun a s h => (hΦ a s h).x19) (by taint_decide)) fun a s h => ?_)
    (two_post (two_map (fun a => (f a, (f a).kp, 9 * (f a).L)) (fun _ _ h => h) clear_ct)
      fun a s h => clear_post _ s h)) (finishWith_ct f (fun _ _ h => h.stp) hs)
  obtain ⟨o, u, st, g⟩ := hΦ a s h
  obtain ⟨hL1, hL2, -⟩ := g.len_valid
  have h9 : BitVec.ofNat 64 (f a).L <<< 3 + BitVec.ofNat 64 (f a).L = BitVec.ofNat 64 (9 * (f a).L) := by
    rw [SearchInit.shl_ofNat _ _ (by omega_using [hL2]), SearchInit.add_ofNat]; congr 1; omega_using []
  refine WP.mono (setAll_ok g) fun t ⟨hm, k⟩ => ?_
  obtain ⟨g', w12, w13, -⟩ := store_region g hm k (by decide)
  rw [h9] at w13
  exact ⟨o, u, st, g', w12, w13, by rw [g.key_region]; exact fun _ h => h, by show 1 ≤ 9 * (f a).L; omega_using [hL1],
    by show 9 * (f a).L < 2 ^ 63; omega_using [hL2]⟩

/-! ## After the search -/

/-- After the search, at the point. -/
def AfterCT (q : GenPoint) (t : State) : Prop :=
  ∃ original st s, AtPoint q original st ∧ GenLive q.inputs original q.used st s ∧
    word s.mem q.inputs.stp 24 = q.req ∧ AfterSearch q.inputs original q.used st s t

/-- After the search and the count of its octets, at the point. -/
def MidCT (q : GenPoint) (u : State) : Prop :=
  ∃ original st, AtPoint q original st ∧
    Mid q.inputs original ((tailOf q.inputs original q.used st).consume q.used []) q.used st u

theorem MidCT.any {q : GenPoint} {u : State} (h : MidCT q u) : AnyFrame q.inputs u :=
  let ⟨o, _, _, hm⟩ := h; ⟨o, _, _, hm.frame⟩

theorem status_cases (r : PrimeSearchResult) : r.status = 0 ∨ r.status = 1 ∨ r.status = 3 := by
  rw [rOf_status]; cases r.outcome <;> simp [Spec.Entropy.Outcome.status]

theorem MidCT.status {q : GenPoint} {u : State} (h : MidCT q u) : q.status = 0 ∨ q.status = 1 ∨ q.status = 3 := by
  obtain ⟨o, st, ha, -⟩ := h
  rw [← ha.status]; exact status_cases _

/-- The frame's base and `used`'s pointer in the frame. -/
def Hdr2 (p : GenPublic) (s : State) : Prop :=
  s.gpr .x19 = p.F ∧ InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 (8 * 2)) 8 ∧
    s.mem.readW (p.F + BitVec.ofNat 64 (8 * 2)) 64 = p.up

/-- The head's tests, at the point. -/
def HeadCT (q : GenPoint) (u : State) : Prop :=
  MidCT q u ∧ u.gpr .x9 = BitVec.ofNat 64 q.status ∧ u.gpr .x10 = BitVec.ofNat 64 q.cand

theorem head_ct : RelCT isa (Two AfterCT) (.block [.addImm .w .x9 .x0 0, ldf .x11 2, ld .x10 .x11, ldf .x12 8,
    .add .x .x12 .x12 .x10, stf .x12 8]) (Two HeadCT) := by
  have hpin : Pins AfterCT [.x19] :=
    frame_pins (fun q => q.inputs) fun _ _ ⟨_, _, _, _, _, _, ha⟩ => ha.frame.x19
  have hct : RelCT isa (Two AfterCT) (.block [.addImm .w .x9 .x0 0, ldf .x11 2, ld .x10 .x11, ldf .x12 8,
      .add .x .x12 .x12 .x10, stf .x12 8]) fun _ _ => True := by
    change RelCT isa (Two AfterCT) (.block ([.addImm .w .x9 .x0 0] ++ (ldf .x11 2 :: [ld .x10 .x11, ldf .x12 8,
      .add .x .x12 .x12 .x10, stf .x12 8]))) _
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun q t => Hdr2 q.inputs t) [.x19] hpin (by taint_decide)
      fun q t ⟨o, st, s, _, _, _, ha⟩ => ?_) (ldf_then (by decide) (fun q => q.inputs.F) (fun q => q.inputs.up)
        [.x19] (frame_pins (fun q => q.inputs) fun _ _ h => h.1) (fun _ _ h => h) (by taint_decide)
        (by taint_decide)))
    have g := ha.frame
    refine WP.mono (WP.keep [.x9] (Q := fun u => u.mem = t.mem) (by brun [exec_addImm_w]) (by decide) (by decide)
      (by decide +kernel)) fun u ⟨hm, k⟩ => ?_
    exact (g.keep k hm).hdr (by simp [GenPublic.headers]) (by decide)
  refine two_post hct fun q t ⟨o, st, s, ha, hl, _, haf⟩ =>
    WP.mono (after_head ⟨hl, [], rfl⟩ haf) fun u ⟨hx9, hx10, hm⟩ =>
      ⟨⟨o, st, ha, hm⟩, by rw [hx9, ha.status], by rw [hx10, ha.cand]⟩

/-! ## A generation exhausted -/

/-- The generations' test, at the point. -/
def LeftCT (q : GenPoint) (u : State) : Prop :=
  ∃ original used st, GenFrame q.inputs original used st u ∧ u.gpr .x8 = q.inputs.stp ∧
    u.gpr .x10 = BitVec.ofNat 64 q.left ∧ q.left = st.left ∧
    isa.eval (.zero .x .x12) u = some (decide (q.left < 2))

theorem LeftCT.any {q : GenPoint} {u : State} (h : LeftCT q u) : AnyFrame q.inputs u :=
  let ⟨o, _, _, g, _⟩ := h; ⟨o, _, _, g⟩

theorem LeftCT.eval {q : GenPoint} {u : State} (h : LeftCT q u) :
    isa.eval (.zero .x .x12) u = some (decide (q.left < 2)) :=
  let ⟨_, _, _, _, _, _, _, e⟩ := h; e

/-- One generation fewer, then the state's pointer reloaded. -/
theorem dec_hdr (q : GenPoint) (s : State) (h : LeftCT q s ∧ isa.eval (.zero .x .x12) s = some false) :
    WP isa (.block [.subImm .x .x10 .x10 1, VG.Impl.Bignum.AArch64.st .x10 .x8 40]) s (Hdr7 q.inputs) := by
  obtain ⟨⟨o, u, st, g, h8, h10, -, -⟩, -⟩ := h
  have scr := g.scr
  have sst := g.stateScr
  have hs5 : InRegions s.wr (q.inputs.stp + BitVec.ofNat 64 40) 8 := sst.st (d := 40) (by decide)
  have hnF : q.inputs.F.toNat + 160 ≤ 2 ^ 64 := scr.nowrap
  have hnS : q.inputs.stp.toNat + 56 ≤ 2 ^ 64 := sst.nowrap
  have hk7 (v : BitVec 64) :
      (s.mem.writeW (q.inputs.stp + BitVec.ofNat 64 40) v).readW (q.inputs.F + BitVec.ofNat 64 (8 * 7)) 64 =
        q.inputs.stp :=
    ((Frame.writeW (Frame.refl _ _) (List.mem_singleton_self (⟨q.inputs.stp, 56⟩ : Region)) v
      (Offset.contains_base _ (by decide) (by omega_using []))).readW (r := q.inputs.frame)
      (Offset.contains_base _ (by decide) (by omega_using [])) (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr; exact g.input.frame_state) (by decide)).trans
      (g.headers (7, q.inputs.stp) (by simp [GenPublic.headers]))
  have hl7 := g.frame_ld (8 * 7) (by decide)
  brun [VG.Impl.Bignum.AArch64.st, h8, h10, hs5]
  exact ⟨by simp only [RegUpd.gpr_write_of_ne _ _ _ (show Reg.x19 ≠ .x10 by decide)]; exact g.x19, hl7, hk7 _⟩

theorem exhausted_ct : RelCT isa (Two MidCT) exhaustedGen (fun _ _ => True) := by
  unfold exhaustedGen
  refine RelCT.seq (two_post (Ψ := LeftCT) (ldf_then (by decide) (fun q => q.inputs.F) (fun q => q.inputs.stp)
    [.x19] (frame_pins (fun q => q.inputs) fun _ _ h => h.any.x19) (fun _ _ h => h.any.stp) (by taint_decide)
    (by taint_decide)) fun q u ⟨o, st, ha, hm⟩ => WP.mono (left_ok hm.frame) fun v ⟨⟨hb, hx8, hx10, hmem⟩, k⟩ =>
      ⟨o, _, _, hm.frame.keep k hmem, hx8, by rw [hx10, ha.1], ha.1.symm, by
        rw [eval_zero, hb, ← ha.1]; by_cases h2 : 2 ≤ st.left <;> simp [h2]; omega_using [h2]⟩) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.eval.trans h₂.eval.symm) ?_ ?_
  · exact fail_ct (fun q => q.inputs) (fun _ _ h => h.1.any) (by decide)
  · refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun q t => Hdr7 q.inputs t) [.x19, .x8] ?_
      (by taint_decide) dec_hdr) (nextPrime_ct (fun q : GenPoint => q.inputs) (fun _ _ h => h) (phase := 0) (by decide)))
    rintro q s t ⟨⟨o₁, _, _, g₁, a₁, -⟩, -⟩ ⟨⟨o₂, _, _, g₂, a₂, -⟩, -⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [g₁.x19.trans g₂.x19.symm, a₁.trans a₂.symm]

/-! ## After the key -/

/-- After the key, at the point. -/
def AfterKCT (q : GenPoint) (v : State) : Prop :=
  AnyFrame q.inputs v ∧ ((v.gpr .x0).setWidth 32).toNat = q.key ∧ q.key < 3

theorem keyStatus_lt3 (k : Except Failure (List (List Byte)) ⊕ Unit) : keyStatus k < 3 := by
  unfold keyStatus; split <;> decide

/-- The key's first test, at the point. -/
def Key1CT (q : GenPoint) (v : State) : Prop :=
  AnyFrame q.inputs v ∧ v.gpr .x9 = BitVec.ofNat 64 q.key ∧ q.key < 3 ∧
    isa.eval (.zero .x .x12) v = some (decide (q.key = 1))

/-- The key's second test, at the point. -/
def Key2CT (q : GenPoint) (v : State) : Prop :=
  AnyFrame q.inputs v ∧ isa.eval (.zero .x .x12) v = some (decide (q.key = 2))

theorem after_key_ct : RelCT isa (Two AfterKCT) afterKey (fun _ _ => True) := by
  unfold afterKey
  refine RelCT.seq (two_post (Ψ := Key1CT) (two_taint [] (no_pins _) (by taint_decide))
    fun q v ⟨⟨o, u, st, g⟩, hs, h3⟩ => WP.mono (keyStatus_guard hs) fun w ⟨⟨hx9, he, hmem⟩, k⟩ =>
      ⟨⟨o, u, st, g.keep k hmem⟩, hx9, h3, he⟩) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm) ?_ ?_
  · exact finishWith_ct (fun q => q.inputs) (fun _ _ h => h.1.1.stp) (by decide)
  · refine RelCT.seq (two_post (Ψ := Key2CT) (two_taint [] (no_pins _) (by taint_decide))
      fun q v ⟨⟨⟨o, u, st, g⟩, hx9, h3, _⟩, _⟩ => WP.mono (sub_guard (k := 2) (by decide) hx9 (by omega_using [h3]))
        fun w ⟨⟨he, hmem⟩, k⟩ => ⟨⟨o, u, st, g.keep k hmem⟩, he⟩) ?_
    refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
    · exact nextPrime_ct (fun q => q.inputs) (fun _ _ h => h.1.1.stp) (by decide)
    · exact fail_ct (fun q => q.inputs) (fun _ _ h => h.1.1) (by decide)

/-! ## A prime accepted -/

/-- The phase's test, at the point, after an accepted prime. -/
def PhCT (q : GenPoint) (u : State) : Prop :=
  MidCT q u ∧ q.status = 1 ∧ q.cand ≠ 0 ∧ u.gpr .x10 = BitVec.ofNat 64 q.ph

theorem accepted_ct [Key.KeyProof] :
    RelCT isa (Two fun q u => MidCT q u ∧ q.status = 1 ∧ q.cand ≠ 0) (accepted keyCall) (fun _ _ => True) := by
  unfold accepted
  refine RelCT.seq (two_post (Ψ := PhCT) (ldf_then (by decide) (fun q => q.inputs.F) (fun q => q.inputs.stp)
    [.x19] (frame_pins (fun q => q.inputs) fun _ _ h => h.1.any.x19) (fun _ _ h => h.1.any.stp) (by taint_decide)
    (by taint_decide))
    fun q u ⟨⟨o, st, ha, hm⟩, h1, h0⟩ => WP.mono (phase_ok hm.frame) fun v ⟨⟨hx10, hmem⟩, k⟩ =>
      ⟨⟨o, st, ha, hm.keep k hmem⟩, h1, h0, by rw [hx10, ha.2.1]⟩) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2.2.2, h₂.2.2.2]) ?_ ?_
  · exact nextPrime_ct (fun q => q.inputs) (fun _ _ h => h.1.1.any.stp) (by decide)
  · -- `q`: the key.
    have hk : ∀ q u, (PhCT q u ∧ isa.eval (.zero .x .x10) u = some false) → KeyCT q u := by
      rintro q u ⟨⟨⟨o, st, ha, hm⟩, h1, h0, hx⟩, hf⟩
      have hph : q.ph ≠ 0 := by
        intro h0'
        rw [eval_zero, hx, h0'] at hf
        cases hf
      obtain ⟨left, phase, remaining⟩ := st
      cases phase with
      | p => exact absurd (ha.2.1.symm.trans rfl) hph
      | q pB =>
        cases ho : (rOf q.inputs o q.used ⟨left, .q pB, remaining⟩).outcome with
        | entropy k a => rw [← ha.status, rOf_status, ho] at h1; cases h1
        | exhausted => rw [← ha.status, rOf_status, ho] at h1; cases h1
        | accepted c => exact ⟨o, _, _, c, pB, ha, hm, ho, by rw [ha.cand]; omega_using [h0], rfl⟩
    refine RelCT.seq (two_post (Ψ := AfterKCT) ((key_run_ct).mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ =>
      ⟨q, hk q _ h₁, hk q _ h₂, hsp⟩) fun _ _ h => h) fun q u h => ?_) after_key_ct
    have hkc := hk q u h
    obtain ⟨o, st, final, c, pB, ha, hm, ho, hpos, hph⟩ := hkc
    refine WP.mono (key_run hm.frame) fun v hak => ⟨⟨o, _, _, hak.frame⟩, ?_, ?_⟩
    · rw [hak.status, (show KeyCT q u from ⟨o, st, final, c, pB, ha, hm, ho, hpos, hph⟩).status]
    · rw [← (show KeyCT q u from ⟨o, st, final, c, pB, ha, hm, ho, hpos, hph⟩).status]
      exact keyStatus_lt3 _

/-! ## The classification -/

/-- The test of the search's status 3, at the point. -/
def Mid3CT (q : GenPoint) (u : State) : Prop :=
  MidCT q u ∧ u.gpr .x10 = BitVec.ofNat 64 q.cand ∧ q.status ≠ 0 ∧
    isa.eval (.zero .x .x12) u = some (decide (q.status = 3))

theorem accepted_of {q : GenPoint} {u : State}
    (h : (Mid3CT q u ∧ isa.eval (.zero .x .x12) u = some false) ∧ isa.eval (.zero .x .x10) u = some false) :
    MidCT q u ∧ q.status = 1 ∧ q.cand ≠ 0 := by
  obtain ⟨⟨⟨hm, hx10, h0, he⟩, hf3⟩, hf4⟩ := h
  have hs := MidCT.status hm
  have h3 : q.status ≠ 3 := ev_false he hf3
  have hu64 : q.cand < 2 ^ 64 := by
    obtain ⟨o, st, ha, hm'⟩ := hm
    have := hm'.frame.used_le; have := hm'.frame.input.cfacts.rand64; rw [← ha.cand]; omega_arith
  refine ⟨hm, by omega_using [h0, hs, h3], fun hc => ?_⟩
  rw [eval_zero, hx10, ofNat_beq_zero hu64, hc] at hf4
  cases hf4

theorem classify_ct [Key.KeyProof] : RelCT isa (Two AfterCT) (classify keyCall) (fun _ _ => True) := by
  unfold classify
  simp only [VG.Impl.Bignum.AArch64.seqs]
  refine RelCT.seq head_ct ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2.1, h₂.2.1]) ?_ ?_
  · exact frame_ct (fun q => q.inputs) (fun _ _ h => h.1.1.any.x19) (by taint_decide)
  · refine RelCT.seq (two_post (Ψ := Mid3CT) (two_taint [] (no_pins _) (by taint_decide))
      fun q u ⟨⟨hm, hx9, hx10⟩, hf⟩ => ?_) ?_
    · have hs := MidCT.status hm
      have h0 : q.status ≠ 0 := by
        intro h0'; rw [eval_zero, hx9, h0'] at hf; cases hf
      refine WP.mono (sub_guard (k := 3) (by decide) hx9 (by omega_using [hs])) fun v ⟨⟨he3, hmem⟩, k⟩ =>
        ⟨let ⟨o, st, ha, hm'⟩ := hm; ⟨o, st, ha, hm'.keep k hmem⟩, by rw [k.gpr _ (by decide)]; exact hx10, h0, he3⟩
    refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm) ?_ ?_
    · exact (exhausted_ct.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.1.1, h₂.1.1, hsp⟩) fun _ _ h => h)
    · refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.1.2.1, h₂.1.2.1]) ?_ ?_
      · exact fail_ct (fun q => q.inputs) (fun _ _ h => h.1.1.1.any) (by decide)
      · exact (accepted_ct.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, accepted_of h₁, accepted_of h₂, hsp⟩)
          fun _ _ h => h)

end VG.Proof.RsaKeyGen.AArch64.Generate

end

end

/-! ### `RsaKeyGen.AArch64.Generate.Correct`, which this module and modules that import it used -/

section

/-! # RSA key generation's controller on AArch64: correctness

The entry, the frame saving `x30` around the key's buffer cleared but `p` and
the loop, and the return: the contract's postcondition and the registers and
stack pointer the ABI preserves.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MillerRabin.AArch64 (RoundImpl)
open VG.Impl.RsaKeyGen.AArch64.Generate
open VG.Impl.Bignum.AArch64 (st)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-- The controller, with the prime search and the key it calls. -/
abbrev genCode (v : RoundImpl) : Prog isa := code (searchCall v) keyCall

theorem F_16 (p : GenPublic) : p.F - 16 = p.sp - BitVec.ofNat 64 176 := by
  rw [GenPublic.F, BitVec.sub_sub]; rfl

/-- The slot saving `x30` is apart from the frame. -/
theorem slot_frame (p : GenPublic) : Region.Disjoint ⟨p.F - 16, 16⟩ p.frame := by
  rw [F_16]
  have hs := Offset.sep_below p.sp 208 (a := 176) (n := 16) (b := 160) (k := 160) (by decide) (by decide)
    (Or.inl (by decide)) (by decide) (by decide)
  exact fun x hx hy => hs x (Nat.lt_of_succ_le (by simpa only [Region.Contains] using hx))
    (Nat.lt_of_succ_le (by simpa only [Region.Contains, GenPublic.F] using hy))

/-- The slot saving `x30` is in the controller's stack. -/
theorem slot_stack (p : GenPublic) : Region.Sub ⟨p.F - 16, 16⟩ (cStack p) := by
  rw [F_16]; exact Offset.sub_below p.sp (a := 176) (b := 416) (by decide) (by decide)

/-- The return, from a state with a finished key search's memory and
regions: the octets consumed to `used`, the status, and `x19`. -/
theorem finish_ok {p : GenPublic} {original d x : State} {final : KeySearchResult}
    (h : GenDone p original final d) (hm : Frame [⟨p.F - 16, 16⟩] d.mem x.mem) (hrd : x.rd = d.rd)
    (hwr : x.wr = d.wr) (hx19 : x.gpr .x19 = p.F) :
    WP isa (.block finish) x fun t =>
      (t.gpr .x0 = BitVec.ofNat 64 final.keyStatus ∧ t.gpr .x19 = original.gpr .x19 ∧
        t.mem = x.mem.writeW p.up (BitVec.ofNat 64 final.used)) ∧ Keep [.x0, .x1, .x2, .x19] x t := by
  have hF (e : Nat) (he : e + 8 ≤ 160) :
      x.mem.readW (p.F + BitVec.ofNat 64 e) 64 = d.mem.readW (p.F + BitVec.ofNat 64 e) 64 :=
    hm.readW (r := p.frame) (Offset.contains_base _ he (by omega_using [he]))
      (fun R hR => by obtain rfl := List.mem_singleton.mp hR; exact (slot_frame p).symm) (by decide)
  obtain ⟨g, hst, -, -⟩ := h
  have hl : ∀ e, e + 8 ≤ 160 → InRegions (x.rd ++ x.wr) (p.F + BitVec.ofNat 64 e) 8 := by
    rw [hrd, hwr]; exact g.frame_ld
  have hu := g.usedScr
  have hsu0 : InRegions x.wr (p.up + BitVec.ofNat 64 0) 8 := by rw [hwr]; exact hu.st (d := 0) (by decide)
  have hsu : InRegions x.wr p.up 8 := by simpa only [BitVec.add_zero] using hsu0
  have h2 := g.header (j := 2) (v := p.up) (by simp [GenPublic.headers])
  have h8 := g.header (j := 8) (v := BitVec.ofNat 64 final.used) (by simp [GenPublic.headers])
  have h9 : x.mem.readW (p.F + BitVec.ofNat 64 72) 64 = original.gpr .x19 := (hF 72 (by decide)).trans g.savedX19
  have h10 : x.mem.readW (p.F + BitVec.ofNat 64 80) 64 = BitVec.ofNat 64 final.keyStatus :=
    (hF 80 (by decide)).trans hst
  simp only [Nat.reduceMul] at h2 h8
  have h2' : x.mem.readW (p.F + BitVec.ofNat 64 16) 64 = p.up := (hF 16 (by decide)).trans h2
  have h8' : x.mem.readW (p.F + BitVec.ofNat 64 64) 64 = BitVec.ofNat 64 final.used := (hF 64 (by decide)).trans h8
  refine WP.keep [.x0, .x1, .x2, .x19] ?_ (by decide) (by decide) (by decide +kernel)
  unfold finish
  brun [ldf, hx19, hl 16 (by decide), hl 64 (by decide), hl 72 (by decide), hl 80 (by decide), h2', h8', h9,
    h10, hsu0, hsu]

theorem phase_word_if (ph : KeyPhase) :
    BitVec.ofNat 64 (phaseWord ph) = BitVec.ofNat 64 (if ph = .p then 0 else 1) := by
  cases ph <;> rfl

/-- What the controller returns, from what the loop leaves. -/
theorem done_post {p : GenPublic} {s d t : State} (hp : GenInput p s)
    (h : GenDone p s (genResult s) d)
    (hx0 : t.gpr .x0 = BitVec.ofNat 64 (genResult s).keyStatus)
    (hfr : Frame [rU p, cStack p] d.mem t.mem)
    (hu : t.mem.readW p.up 64 = BitVec.ofNat 64 (genResult s).used) : genPost s t := by
  obtain ⟨g, -, hkey, req, hreq, hr⟩ := h
  have hf := hp.cfacts
  have hst := g.state
  have hkp : s.gpr .x0 = p.kp := by rw [← hp.2]; rfl
  have hup : s.gpr .x2 = p.up := by rw [← hp.2]; rfl
  have hstp : s.gpr .x7 = p.stp := by rw [← hp.2]; rfl
  have hL : genLen s = p.L := by rw [← hp.2]; rfl
  have heB : genE s = p.eB := by rw [← hp.2]; rfl
  -- The store to `used` and the stack are apart from the key's buffer and the state.
  have hword (j : Nat) (hj : j < 7) : word t.mem p.stp (8 * j) = word d.mem p.stp (8 * j) :=
    hfr.readW (r := cS p) (Offset.contains_base _ (by omega_using [hj]) (by have := hf.nT; omega_using [hj]))
      (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        exacts [hf.uT.symm, hf.stack _ (by simp)]) (by decide)
  have hbytes {R : Region} (hR : Region.Sub R (cK p) ∨ Region.Sub R (cS p)) (hn : R.len ≤ 2 ^ 64) :
      Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt d.mem R.base R.len := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    refine hfr.bytes (fun q hq => ?_) hn (List.mem_range.mp hi)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> rcases hR with hR | hR
    exacts [(hf.kU.sub_left hR), (hf.uT.symm.sub_left hR), (hf.stack _ (by simp)).sub_left hR,
      (hf.stack _ (by simp)).sub_left hR]
  refine ⟨?_, ?_, ?_, req, ?_, ?_, ?_⟩
  · have := keyStatus_lt (genResult s)
    rw [hx0, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [this]), Nat.mod_eq_of_lt (by omega_using [this])]
  · rw [hkp, hL, ← hkey]
    exact hbytes (R := ⟨p.kp, 9 * p.L⟩) (.inl fun _ h => h) (by show 9 * p.L ≤ 2 ^ 64; have := hf.nK; omega_using [this])
  · rw [hup]
    show [t.mem.readW (p.up + BitVec.ofNat 64 (8 * 0)) 64] = _
    rw [Nat.mul_zero, BitVec.add_zero, hu]
  · rw [hstp, hL]
    show [word t.mem p.stp (8 * 0), word t.mem p.stp (8 * 1), word t.mem p.stp (8 * 2), word t.mem p.stp (8 * 3),
      word t.mem p.stp (8 * 4), word t.mem p.stp (8 * 5)] = _
    rw [hword 0 (by decide), hword 1 (by decide), hword 2 (by decide), hword 3 (by decide), hword 4 (by decide),
      hword 5 (by decide)]
    simp only [Nat.reduceMul]
    rw [show word d.mem p.stp 0 = _ from hst.remaining, show word d.mem p.stp 8 = _ from hst.len,
      show word d.mem p.stp 16 = _ from hst.cap, show word d.mem p.stp 24 = _ from hreq,
      show word d.mem p.stp 32 = _ from hst.phase, show word d.mem p.stp 40 = _ from hst.left, phase_word_if]
  · rw [hstp, heB]
    have := hbytes (R := ⟨p.stp + BitVec.ofNat 64 48, 8⟩) (.inr rE_sub) (by show 8 ≤ 2 ^ 64; decide)
    exact this.trans hst.e
  · rw [hL]; exact hr

/-! ## The frame saving `x30` -/

theorem iteration_depth (v : RoundImpl) : (iteration (searchCall v) keyCall).aarch64Depth = 15 := by
  have hk : VG.Impl.RsaKeyGen.AArch64.Key.code.aarch64Depth = 0 := Search.depth_of_noFrames keyCode_noFrames
  have he : exhaustedGen.aarch64Depth = 0 := rfl
  have hf : (fail 3).aarch64Depth = 0 := rfl
  have ha : afterKey.aarch64Depth = 0 := rfl
  simp only [iteration, searchRun, classify, accepted, keyRun, searchCall, keyCall, VG.Impl.Bignum.AArch64.seqs,
    Code.aarch64Depth, searchCode_depth, hk, he, hf, ha, Instr.frameUnits]
  decide

/-- `p`'s slot at the start, for `q`'s search. -/
theorem start_other {p : GenPublic} {s x : State} (h : GenInput p s) (hu : GenFrame p s 0 (genProgress s) x)
    (hfu : Frame [p.frame, belowFrame s] s.mem x.mem) :
    ∀ pB, (genProgress s).phase = .q pB → Spec.Rsa.bytesAt x.mem (p.slot 4) p.L = pB := by
  have hf := h.cfacts
  obtain ⟨hL1, -, -⟩ := hf.len
  intro pB hpB
  simp only [genProgress, keyProgressAt] at hpB
  split at hpB
  · cases hpB
  · cases hpB
    have hst := hf.stack
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
    obtain ⟨sK, -, -, -, -⟩ := hst
    have hsub : Region.Sub ⟨p.slot 4, p.L⟩ (cK p) := slot_sub _ (by omega_using [])
    have hk : Spec.Rsa.bytesAt x.mem (p.slot 4) p.L = Spec.Rsa.bytesAt s.mem (p.slot 4) p.L := by
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      refine hfu.bytes (R := ⟨p.slot 4, p.L⟩) (fun q hq => ?_) (by show p.L ≤ 2 ^ 64; have := hf.nK; omega_using [this])
        (List.mem_range.mp hi)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact (hu.frame_key.sub_right hsub).symm
      · refine (sK.sub_left hsub).sub_right ?_
        show Region.Sub ⟨s.sp - BitVec.ofNat 64 stackUse, 256⟩ ⟨p.sp - BitVec.ofNat 64 416, 416⟩
        rw [h.sp_eq]
        exact Region.sub_prefix (by decide)
    rw [hk, ← h.2]
    rfl

/-- The key's buffer cleared but `p`, and the loop, from the start. -/
theorem gen_inner [Key.KeyProof] (v : RoundImpl) {p : GenPublic} {s x : State} (h : GenInput p s)
    (hu : GenFrame p s 0 (genProgress s) x) (hfu : Frame [p.frame, belowFrame s] s.mem x.mem) :
    WP isa (.seq clearAround (.loop (iteration (searchCall v) keyCall) (.zero .x .x9))) x
      (GenDone p s (genResult s)) := by
  refine WP.seq (WP.mono (clearAround_ok hu (start_other h hu hfu)) fun w ⟨hw, _⟩ => ?_)
  have hinv : GenInv p s (genResult s) (genMeasure p 0 (genProgress s)) w :=
    ⟨0, genProgress s, rfl, hw, [], by rw [consume_zero]; rw [← h.2]; rfl⟩
  exact gen_loop v hinv

/-- The frame saving `x30` writes below the controller's frame. -/
theorem push_disjoint {p : GenPublic} {s t : State} (h : GenInput p s) (htsp : t.sp = p.F)
    (hw : t.wr = p.frame :: s.wr) : ∀ R ∈ t.wr, Region.Disjoint ⟨t.sp - 16, 16⟩ R := by
  intro R hR
  rw [hw] at hR
  rw [htsp]
  rcases List.mem_cons.mp hR with rfl | hR
  · rw [F_16]
    have hs := Offset.sep_below p.sp 208 (a := 176) (n := 16) (b := 160) (k := 160) (by decide) (by decide)
      (Or.inl (by decide)) (by decide) (by decide)
    exact fun x hx hy => hs x (Nat.lt_of_succ_le (by simpa only [Region.Contains] using hx))
      (Nat.lt_of_succ_le (by simpa only [Region.Contains, GenPublic.F] using hy))
  · rw [h.1.2.2.1] at hR
    have hd := h.stack_disjoint (r := R) (List.mem_append_left _ hR)
    refine hd.sub_left ?_
    rw [F_16, h.sp_eq]
    exact Offset.sub_below s.sp (a := 176) (b := 416) (by decide) (by decide)

/-- The body, in the frame saving `x30`: the loop's end, with `x30` and the
stack pointer back. -/
theorem gen_body [Key.KeyProof] (v : RoundImpl) {p : GenPublic} {s t : State} (h : GenInput p s)
    (hx : t.gpr .x19 = p.F) (hm : t.mem = writeFrame s.mem p.F (entryValues s))
    (k : Keep [.x9, .x10, .x12, .x13, .x14, .x15, .x16, .x17, .x19] (allocated 160 s) t) :
    WP isa (body (searchCall v) keyCall) t fun u =>
      ∃ d, GenDone p s (genResult s) d ∧ ∃ m uu, Frame [⟨p.F - 16, 16⟩] d.mem m ∧
        u = { d.write .x .x30 (t.gpr .x30) with sp := t.sp, mem := m, unknowns := uu } := by
  obtain ⟨hu, hfu⟩ := gen_start h hx hm k
  have hf := h.cfacts
  have htsp : t.sp = p.F := k.sp.trans (alloc_sp h)
  have hroom : 416 ≤ p.sp.toNat := hf.room
  have hF := h.F_toNat
  have hsp : 16 ≤ t.sp.toNat := by
    rw [htsp, hF]; exact Nat.le_sub_of_add_le (Nat.le_trans (by decide) hroom)
  unfold body
  refine WP.frameReg hsp (push_disjoint h htsp (k.wr.trans (alloc_wr h))) ?_ ?_
  · exact WP.mono (gen_inner v h hu hfu) fun d hd m uu f => ⟨d, hd, m, uu, by rw [htsp] at f; exact f, rfl⟩
  · show 16 * (Code.seq clearAround (.loop (iteration (searchCall v) keyCall) (.zero .x .x9))).aarch64Depth + 16 <
      2 ^ 64
    have hc : clearAround.aarch64Depth = 0 := rfl
    simp only [Code.aarch64Depth, iteration_depth v, hc]
    decide

/-! ## The whole controller -/

theorem gen_correct_ok [Key.KeyProof] (v : RoundImpl) {s : State} (h : genPre s) :
    WP isa (genCode v) s fun t => genPost s t ∧ abiPreserved s t := by
  have hp : GenInput (genOfState s) s := ⟨h, rfl⟩
  have hroom : 160 ≤ s.sp.toNat := Nat.le_trans (by decide) h.1
  unfold genCode code
  refine WP.alloc (by decide) hroom ?_
  simp only [VG.Impl.Bignum.AArch64.seqs]
  refine WP.seq (WP.mono (entry_ok hp) fun t ⟨⟨hx, hm⟩, k⟩ => ?_)
  refine WP.seq (WP.mono (gen_body v hp hx hm k) fun u ⟨d, hd, m₁, u₁, f₁, hu⟩ => ?_)
  subst hu
  have g := hd.1
  have hx19 : (d.write .x .x30 (t.gpr .x30)).gpr .x19 = (genOfState s).F := by
    rw [RegUpd.gpr_write_of_ne _ _ _ (by decide)]; exact g.x19
  refine WP.mono (finish_ok hd f₁ rfl rfl hx19) fun q ⟨⟨hx0, hg19, hmq⟩, kq⟩ m₂ u₂ f₂ => ?_
  have hf := hp.cfacts
  have hA : Region.Sub ⟨s.sp - BitVec.ofNat 64 160, 160⟩ (cStack (genOfState s)) := by
    rw [← hp.sp_eq]; exact Offset.sub_below _ (a := 160) (b := 416) (by decide) (by decide)
  have hfr : Frame [rU (genOfState s), cStack (genOfState s)] d.mem m₂ := by
    refine ((f₁.sub fun R hR => ⟨cStack (genOfState s), by simp, by
      obtain rfl := List.mem_singleton.mp hR; exact slot_stack _⟩).trans ?_).trans
      (f₂.sub fun R hR => ⟨cStack (genOfState s), by simp, by obtain rfl := List.mem_singleton.mp hR; exact hA⟩)
    rw [hmq]
    exact Frame.writeW (Frame.refl _ _) (List.mem_cons_self) _ (Region.contains_self _ _)
  have hu₂ : m₂.readW (genOfState s).up 64 = BitVec.ofNat 64 (genResult s).used := by
    rw [f₂.readW (r := rU (genOfState s)) (Region.contains_self _ _)
      (fun R hR => by obtain rfl := List.mem_singleton.mp hR; exact (hf.stack _ (by simp)).sub_right hA)
      (by decide), hmq, Mem.readW_writeW_self64]
  refine ⟨done_post hp hd hx0 hfr hu₂, ?_, ?_, ?_⟩
  · intro reg hreg
    change q.gpr reg = s.gpr reg
    by_cases h19 : reg = .x19
    · subst h19; exact hg19
    · rw [kq.gpr reg (by revert reg hreg h19; decide)]
      show (d.write .x .x30 (t.gpr .x30)).gpr reg = _
      by_cases h30 : reg = .x30
      · subst h30
        rw [RegUpd.gpr_write_self _ _ _ _, BitVec.setWidth_eq]
        exact k.gpr .x30 (by decide)
      · rw [RegUpd.gpr_write_of_ne _ _ _ h30]
        exact g.saved reg hreg h19 h30
  · change q.sp + BitVec.ofNat 64 160 = s.sp
    rw [kq.sp]
    show t.sp + _ = _
    rw [k.sp, alloc_sp hp]
    show s.sp - _ + _ = _
    rw [BitVec.sub_add_cancel]
  · intro r hr
    exact (kq.vcs r hr).trans (g.vcs r hr)

theorem gen_correct [Key.KeyProof] (v : RoundImpl) (s : State) (h : genContract.pre s) :
    ∃ tr t, Exec isa (genCode v) s tr t ∧ abiPreserved s t ∧ genContract.post s t := by
  obtain ⟨tr, t, he, hp, ha⟩ := gen_correct_ok v h
  exact ⟨tr, t, he, ha, hp⟩

end VG.Proof.RsaKeyGen.AArch64.Generate

end

end

/-! # RSA key generation's controller on AArch64: constant time

Two runs whose public data agree start at the same point (`initialPoint`):
the same public descriptor, progress words, request word and key search
trace. Each iteration takes them to the same next point or both out of the
loop (`gen_ct_step`), and every block, call and test between is of the
point.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.MillerRabin.AArch64 (RoundImpl)
open VG.Impl.RsaKeyGen.AArch64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-! ## The key's buffer cleared but `p` -/

theorem clearAround_ct {α : Type} {Φ : α → State → Prop} (f : α → GenPublic)
    (hΦ : ∀ a s, Φ a s → AnyFrame (f a) s) : RelCT isa (Two Φ) clearAround fun _ _ => True := by
  unfold clearAround
  simp only [VG.Impl.Bignum.AArch64.seqs]
  refine RelCT.seq (two_post (Ψ := fun a s => ClearCT (f a, (f a).kp, 4 * (f a).L) s)
    (frame_ct f (fun a s h => (hΦ a s h).x19) (by taint_decide)) fun a s h => ?_)
    (RelCT.seq (two_post (Ψ := fun a s => AnyFrame (f a) s)
      (two_map (fun a => (f a, (f a).kp, 4 * (f a).L)) (fun _ _ h => h) clear_ct) fun a s h => clear_post _ s h)
    (RelCT.seq (two_post (Ψ := fun a s => ClearCT (f a, (f a).slot 5, 4 * (f a).L) s)
      (frame_ct f (fun a s h => h.x19) (by taint_decide)) fun a s h => ?_)
      (two_map (fun a => (f a, (f a).slot 5, 4 * (f a).L)) (fun _ _ h => h) clear_ct)))
  · obtain ⟨o, u, st, g⟩ := hΦ a s h
    obtain ⟨hL1, hL2, -⟩ := g.len_valid
    have h4 : BitVec.ofNat 64 (f a).L <<< 2 = BitVec.ofNat 64 (4 * (f a).L) := by
      rw [SearchInit.shl_ofNat _ _ (by omega_using [hL2])]; congr 1; omega_using []
    refine WP.mono (setLow_ok g) fun t ⟨hm, k⟩ => ?_
    obtain ⟨g', w12, w13, -⟩ := store_region g hm k (by decide)
    rw [h4] at w13
    exact ⟨o, u, st, g', w12, w13, by
      rw [g.key_region]; exact Region.sub_prefix (by show 4 * (f a).L ≤ 9 * (f a).L; omega_using []),
      by show 1 ≤ 4 * (f a).L; omega_using [hL1], by show 4 * (f a).L < 2 ^ 63; omega_using [hL2]⟩
  · obtain ⟨o, u, st, g⟩ := h
    obtain ⟨hL1, hL2, -⟩ := g.len_valid
    have h4 : BitVec.ofNat 64 (f a).L <<< 2 = BitVec.ofNat 64 (4 * (f a).L) := by
      rw [SearchInit.shl_ofNat _ _ (by omega_using [hL2])]; congr 1; omega_using []
    have h5 : (f a).kp + (BitVec.ofNat 64 (f a).L <<< 2 + BitVec.ofNat 64 (f a).L) = (f a).slot 5 := by
      rw [h4, SearchInit.add_ofNat]; congr 2; omega_using []
    refine WP.mono (setHigh_ok g) fun t ⟨hm, k⟩ => ?_
    obtain ⟨g', w12, w13, -⟩ := store_region g hm k (by decide)
    rw [h4] at w13
    rw [h5] at w12
    exact ⟨o, u, st, g', w12, w13, by
      rw [g.key_region]; exact slot_sub _ (by show 5 * (f a).L + 4 * (f a).L ≤ 9 * (f a).L; omega_using []),
      by show 1 ≤ 4 * (f a).L; omega_using [hL1], by show 4 * (f a).L < 2 ^ 63; omega_using [hL2]⟩

/-! ## An iteration -/

theorem search_run_post (v : RoundImpl) :
    RelCT isa (Two GenCTL) (searchRun (searchCall v)) (Two AfterCT) :=
  two_post (search_run_ct v) fun _ s ⟨o, st, ha, hl, hw⟩ =>
    WP.mono (search_run v hl) fun _ h => ⟨o, st, s, ha, hl, hw, h⟩

theorem classify_any [Key.KeyProof] (q : GenPoint) (t : State) (h : AfterCT q t) :
    WP isa (classify keyCall) t (AnyFrame q.inputs) := by
  obtain ⟨o, st, s, -, hl, -, ha⟩ := h
  refine WP.mono (classify_ok ⟨hl, [], rfl⟩ ha) fun u hc => ?_
  rcases hc with ⟨-, -, -, ⟨st', -, hl', -⟩, -⟩ | ⟨-, hd⟩
  · exact ⟨o, _, st', hl'.toGenFrame⟩
  · exact ⟨o, _, _, hd.1⟩

theorem iteration_ct [Key.KeyProof] (v : RoundImpl) :
    RelCT isa (Two GenCTL) (iteration (searchCall v) keyCall) (fun _ _ => True) := by
  unfold iteration
  simp only [VG.Impl.Bignum.AArch64.seqs]
  exact RelCT.seq (search_run_post v) (RelCT.seq (two_post classify_ct classify_any)
    (frame_ct (fun q : GenPoint => q.inputs) (fun _ _ h => h.x19) (by taint_decide)))

/-! ## The loop -/

/-- What each step that goes on lowers. -/
def GenPoint.measure (q : GenPoint) : Nat := (q.inputs.randLen - q.used) * 2 ^ 64 + q.left

theorem next_measure {q : GenPoint} {t : State} (hc : q.continues) (h : GenCTL q.next t) :
    q.next.measure < q.measure := by
  obtain ⟨o, st, ha, hl, -⟩ := h
  have hle := hl.used_le
  have hlt := hl.state.left_lt
  rw [ha.1] at hlt
  unfold GenPoint.measure
  simp only [GenPoint.next] at hle hlt ⊢
  rcases hc with ⟨h3, hl2⟩ | ⟨h1, hc0, -⟩
  · simp only [h3, ↓reduceIte] at hlt ⊢
    have hmul : (q.inputs.randLen - (q.used + q.cand)) * 2 ^ 64 ≤ (q.inputs.randLen - q.used) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (by omega_using [])
    omega_using [hl2]
  · have h3 : ¬q.status = 3 := by omega_using [h1]
    simp only [h3, ↓reduceIte] at hlt ⊢
    have hmul : (q.inputs.randLen - (q.used + q.cand) + 1) * 2 ^ 64 ≤ (q.inputs.randLen - q.used) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (by omega_using [hle, hc0])
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega_using [hle, hc0]

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q : GenPoint, n = q.measure ∧ GenCTL q s ∧ GenCTL q t ∧ s.sp = t.sp

private theorem iteration_pair [Key.KeyProof] (v : RoundImpl) (n : Nat) :
    RelCT isa (LoopPair n) (iteration (searchCall v) keyCall) fun s t =>
      isa.eval (.zero .x .x9) s = isa.eval (.zero .x .x9) t ∧ (isa.eval (.zero .x .x9) s = some false → True) ∧
      (isa.eval (.zero .x .x9) s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (q : GenPoint) (s : State) (h : n = q.measure ∧ GenCTL q s) :
      WP isa (iteration (searchCall v) keyCall) s fun t => n = q.measure ∧ GenCTStep q t :=
    WP.mono (gen_ct_step v q s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((iteration_ct v).mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.2, h₂.2, hsp⟩)
    (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂, hsp⟩ => ⟨q, ⟨hn, h₁⟩, ⟨hn, h₂⟩, hsp⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, ⟨_, h₂⟩, hsp⟩
  rcases h₁ with ⟨hb, e₁, c₁⟩ | ⟨hb, e₁⟩ <;> rcases h₂ with ⟨hb', e₂, c₂⟩ | ⟨hb', e₂⟩
  · exact ⟨e₁.trans e₂.symm, fun _ => trivial, fun _ => ⟨_, by rw [hn]; exact next_measure hb c₁, q.next, rfl,
      c₁, c₂, hsp⟩⟩
  · exact absurd hb hb'
  · exact absurd hb' hb
  · exact ⟨e₁.trans e₂.symm, fun _ => trivial, fun h => by rw [e₁] at h; cases h⟩

theorem loop_ct [Key.KeyProof] (v : RoundImpl) :
    RelCT isa (Two GenCTL) (.loop (iteration (searchCall v) keyCall) (.zero .x .x9)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht, hsp⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration (searchCall v) keyCall) (c := .zero .x .x9)
    (Q := fun _ _ => True) LoopPair (iteration_pair v) q.measure _ _ _ _ _ _ ⟨q, rfl, hs, ht, hsp⟩ he₁ he₂

/-! ## Entry and return -/

/-- The point a run starts at. -/
def initialPoint (s : State) : GenPoint :=
  ⟨genOfState s, 0, (genProgress s).left, phaseWord (genProgress s).phase, (genProgress s).remaining,
    word s.mem (s.gpr .x7) 24, (genResult s).trace⟩

/-- A run's entry at a point. -/
def GenStart (q : GenPoint) (s : State) : Prop := genPre s ∧ initialPoint s = q

theorem GenStart.input {q : GenPoint} {s : State} (h : GenStart q s) : GenInput q.inputs s :=
  ⟨h.1, by rw [← h.2]; rfl⟩

/-- A run's entry, past the frame's allocation. -/
def AllocStart (q : GenPoint) (u : State) : Prop := ∃ s, GenStart q s ∧ u = allocated 160 s

theorem entry_ct : RelCT isa (Two AllocStart) (.block entry) (fun _ _ => True) := by
  refine two_taint [.x7] ?_ (by taint_decide)
  rintro q _ _ ⟨s, h₁, rfl⟩ ⟨t, h₂, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst r
  show s.gpr .x7 = t.gpr .x7
  have e₁ : (genOfState s).stp = q.inputs.stp := by rw [← h₁.2]; rfl
  have e₂ : (genOfState t).stp = q.inputs.stp := by rw [← h₂.2]; rfl
  exact e₁.trans e₂.symm

/-- After the entry: the frame's words written. -/
def Entered (q : GenPoint) (t : State) : Prop :=
  ∃ s, GenStart q s ∧ t.gpr .x19 = q.inputs.F ∧ t.mem = writeFrame s.mem q.inputs.F (entryValues s) ∧
    Keep [.x9, .x10, .x12, .x13, .x14, .x15, .x16, .x17, .x19] (allocated 160 s) t

theorem entry_ready (q : GenPoint) (u : State) (h : AllocStart q u) : WP isa (.block entry) u (Entered q) := by
  obtain ⟨s, hs, rfl⟩ := h
  exact WP.mono (entry_ok hs.input) fun _ ⟨⟨hx, hm⟩, k⟩ => ⟨s, hs, hx, hm, k⟩

/-- Past the entry and the push of `x30`, at the point. -/
def StartCT (q : GenPoint) (x : State) : Prop :=
  ∃ s, GenStart q s ∧ GenFrame q.inputs s 0 (genProgress s) x ∧
    Frame [q.inputs.frame, belowFrame s] s.mem x.mem

theorem start_of {q : GenPoint} {t : State} (h : Entered q t) : StartCT q (pushedX30 t) := by
  obtain ⟨s, hs, hx, hm, k⟩ := h
  obtain ⟨hu, hfu⟩ := gen_start hs.input hx hm k
  exact ⟨s, hs, hu, hfu⟩

theorem start_point (q : GenPoint) (x : State) (h : StartCT q x) : WP isa clearAround x (GenCTL q) := by
  obtain ⟨s, hs, hg, hfr⟩ := h
  have hi := hs.input
  obtain ⟨hp, e⟩ := hs
  subst e
  have hf := hg.input.cfacts
  refine WP.mono (clearAround_ok hg (start_other hi hg hfr)) fun w ⟨hw, hfw⟩ =>
    ⟨s, genProgress s, ⟨rfl, rfl, rfl, rfl⟩, hw, ?_⟩
  -- The state's request word, kept through the push and the clearing.
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨-, -, -, sT, -⟩ := hst
  have hd : ∀ r ∈ [(⟨(initialPoint s).inputs.kp, 9 * (initialPoint s).inputs.L⟩ : Region),
      (initialPoint s).inputs.frame], (cS (initialPoint s).inputs).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hf.kT.symm
    · exact hi.frame_state.symm
  have hd' : ∀ r ∈ [(initialPoint s).inputs.frame, belowFrame s], (cS (initialPoint s).inputs).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hi.frame_state.symm
    · refine sT.sub_right ?_
      show Region.Sub ⟨s.sp - BitVec.ofNat 64 stackUse, 256⟩ ⟨s.sp - BitVec.ofNat 64 416, 416⟩
      exact Region.sub_prefix (by decide)
  have h1 := hfw.readW (r := cS (initialPoint s).inputs) (a := (initialPoint s).inputs.stp + BitVec.ofNat 64 24)
    (w := 64) (Offset.contains_base _ (d := 24) (n := 8) (k := 56) (by decide) (by have := hf.nT; omega_using [])) hd
    (by decide)
  have h2 := hfr.readW (r := cS (initialPoint s).inputs) (a := (initialPoint s).inputs.stp + BitVec.ofNat 64 24)
    (w := 64) (Offset.contains_base _ (d := 24) (n := 8) (k := 56) (by decide) (by have := hf.nT; omega_using [])) hd'
    (by decide)
  exact h1.trans h2

/-- A loop's end, with `x30` and the stack pointer back. -/
def DoneCT (q : GenPoint) (x : State) : Prop :=
  ∃ original final d, GenDone q.inputs original final d ∧ Frame [⟨q.inputs.F - 16, 16⟩] d.mem x.mem ∧
    x.rd = d.rd ∧ x.wr = d.wr ∧
    x.gpr .x19 = q.inputs.F

theorem body_ct [Key.KeyProof] (v : RoundImpl) :
    RelCT isa (Two Entered) (body (searchCall v) keyCall) (fun _ _ => True) := by
  unfold body
  refine Search.relCT_pushX30 (fun _ _ ⟨_, _, _, hsp⟩ => hsp) (fun x y ⟨q, h₁, h₂, _⟩ => ?_) ?_
  · have run : ∀ {t : State}, Entered q t → ∃ tr s',
        Exec isa (.seq clearAround (.loop (iteration (searchCall v) keyCall) (.zero .x .x9))) (pushedX30 t) tr s' :=
      fun h => by
        obtain ⟨s, hs, hx, hm, k⟩ := h
        obtain ⟨hu, hfu⟩ := gen_start hs.input hx hm k
        obtain ⟨tr, s', e, -⟩ := gen_inner v hs.input hu hfu
        exact ⟨tr, s', e⟩
    exact ⟨run h₁, run h₂⟩
  · refine (RelCT.seq (two_post (clearAround_ct (fun q : GenPoint => q.inputs)
      (fun _ _ ⟨s, _, hg, _⟩ => ⟨s, _, _, hg⟩)) start_point) (loop_ct v)).mono ?_ fun _ _ h => h
    rintro _ _ ⟨x, y, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
    exact ⟨q, start_of h₁, start_of h₂, by simp only [hsp]⟩

theorem body_post [Key.KeyProof] (v : RoundImpl) (q : GenPoint) (t : State) (h : Entered q t) :
    WP isa (body (searchCall v) keyCall) t (DoneCT q) := by
  obtain ⟨s, hs, hx, hm, k⟩ := h
  refine WP.mono (gen_body v hs.input hx hm k) fun u ⟨d, hd, m, uu, f, hu⟩ => ?_
  subst hu
  exact ⟨s, _, d, hd, f, rfl, rfl, by rw [RegUpd.gpr_write_of_ne _ _ _ (by decide)]; exact hd.1.x19⟩

theorem finish_ct : RelCT isa (Two DoneCT) (.block finish) (fun _ _ => True) := by
  unfold finish
  refine ldf_then (by decide) (fun q => q.inputs.F) (fun q => q.inputs.up) [.x19]
    (frame_pins (fun q => q.inputs) fun _ _ ⟨_, _, _, _, _, _, _, h⟩ => h) ?_ (by taint_decide) (by taint_decide)
  rintro q x ⟨o, f, d, hd, hm, hrd, hwr, h19⟩
  refine ⟨h19, by rw [hrd, hwr]; exact hd.1.frame_ld _ (by decide), ?_⟩
  refine Eq.trans ?_ (hd.1.headers (2, q.inputs.up) (by simp [GenPublic.headers]))
  exact hm.readW (r := q.inputs.frame) (Offset.contains_base _ (by decide) (by decide))
    (fun R hR => by obtain rfl := List.mem_singleton.mp hR; exact (slot_frame _).symm) (by decide)

/-! ## The whole controller -/

theorem gen_code_ct [Key.KeyProof] (v : RoundImpl) : RelCT isa (Two GenStart) (genCode v) (fun _ _ => True) := by
  unfold genCode code
  apply RelCT.alloc
  simp only [VG.Impl.Bignum.AArch64.seqs]
  refine (RelCT.seq (two_post entry_ct entry_ready)
    (RelCT.seq (two_post (body_ct v) (body_post v)) finish_ct)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocated, hsp]⟩

/-- A word's bytes agree where the words do. -/
theorem word_bytes {m₁ m₂ : Mem} {a : Addr} (h : m₁.readW a 64 = m₂.readW a 64) {k : Nat} (hk : k < 8) :
    m₁ (a + BitVec.ofNat 64 k) = m₂ (a + BitVec.ofNat 64 k) := by
  have e : m₁.read a 8 = m₂.read a 8 := h
  rw [← Mem.extractLsb'_read m₁ a hk, ← Mem.extractLsb'_read m₂ a hk, e]

theorem initial_point_eq {s t : State} (hp : genPub s t) : initialPoint s = initialPoint t := by
  obtain ⟨hsp, h0, -, h2, h3, h4, h5, h6, h7, hw, -, -, -, htr⟩ := hp
  have hj : ∀ j < 7, s.mem.readW (s.gpr .x7 + BitVec.ofNat 64 (8 * j)) 64 =
      t.mem.readW (t.gpr .x7 + BitVec.ofNat 64 (8 * j)) 64 := fun j hj' => by
    have := congrArg (fun l => l[j]?) hw
    simpa [Spec.Rsa.wordsAt, List.getElem?_map, hj'] using this
  have w0 := hj 0 (by decide)
  have w1 := hj 1 (by decide)
  have w3 := hj 3 (by decide)
  have w4 := hj 4 (by decide)
  have w5 := hj 5 (by decide)
  have w6 := hj 6 (by decide)
  simp only [Nat.reduceMul, BitVec.add_zero] at w0 w1 w3 w4 w5 w6
  rw [h7] at w0 w1 w3 w4 w5 w6
  have he : genE s = genE t := by
    simp only [genE, Spec.Rsa.bytesAt, h7]
    refine List.map_congr_left fun i hi => ?_
    exact word_bytes (m₁ := s.mem) (m₂ := t.mem) (a := t.gpr .x7 + BitVec.ofNat 64 48) w6 (List.mem_range.mp hi)
  have hL : genLen s = genLen t := by
    simp only [genLen, h7]
    exact congrArg BitVec.toNat w1
  have hG : genOfState s = genOfState t := by
    simp only [genOfState, h0, h2, h3, h4, h5, h6, h7, hsp, hL, he]
  have hpw : phaseWord (genProgress s).phase = phaseWord (genProgress t).phase := by
    have e4 : (s.mem.readW (t.gpr .x7 + 32) 64).toNat = (t.mem.readW (t.gpr .x7 + 32) 64).toNat :=
      congrArg BitVec.toNat w4
    simp only [genProgress, keyProgressAt, h7, e4]
    split <;> rfl
  have hl : (genProgress s).left = (genProgress t).left := by
    have e5 : (s.mem.readW (t.gpr .x7 + 40) 64).toNat = (t.mem.readW (t.gpr .x7 + 40) 64).toNat :=
      congrArg BitVec.toNat w5
    simp only [genProgress, keyProgressAt, h7, e5]
  have hr : (genProgress s).remaining = (genProgress t).remaining := by
    have e0 : (s.mem.readW (t.gpr .x7) 64).toNat = (t.mem.readW (t.gpr .x7) 64).toNat :=
      congrArg BitVec.toNat w0
    simp only [genProgress, keyProgressAt, h7, e0]
  simp only [initialPoint, hG, hpw, hl, hr, htr, Bignum.word, off, h7]
  rw [w3]

theorem gen_constantTime [Key.KeyProof] (v : RoundImpl) :
    ConstantTime isa genContract.pre genContract.pub (genCode v) := by
  refine RelCT.constantTime ((gen_code_ct v).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨initialPoint s, ⟨hs, rfl⟩, ⟨ht, (initial_point_eq hp).symm⟩, hp.1⟩

end VG.Proof.RsaKeyGen.AArch64.Generate

end

end

/-! # The verified key search on AArch64, for every arithmetic backend -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG VG.AArch64 VG.Proof.MillerRabin.AArch64

/-- The controller, given the key's proof (`Key.keyProof`, which the
registration file imports). -/
theorem gen_verified [Key.KeyProof] (v : RoundImpl) :
    Verified target (genCode v) (Spec.RsaKeyGen.keySearchContract abi stackUse) :=
  Verified.of_correct (gen_correct v) (gen_constantTime v) gen_implies

end VG.Proof.RsaKeyGen.AArch64.Generate
