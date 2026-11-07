module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Generate.Steps
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Generate.Loop
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Generate.Correct
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.CT
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.KeyCT
import VerifiedGarbage.Proof.EntropyRequest
import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.Correct
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.RsaKeyGen.GenerationAgrees
meta import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Generate.Steps
meta import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Generate.Loop
meta import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Generate.Correct
meta import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.CT
meta import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.KeyCT
meta import VerifiedGarbage.Proof.EntropyRequest
meta import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.Correct
meta import VerifiedGarbage.Proof.RsaKeyGen.InitWords
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Syms
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Spec.RsaKeyGen.GenerationAgrees

-- separate module: its proofs build in parallel with those of `Implies`, which `Verified` also imports

/-! # The controller's timing depends on its public data and its trace (RISC-V)

As the search's (`Proof/RsaKeyGen/RISCV64/Search/CT.lean`): the taint
analysis treats memory as secret, so each block is checked from the registers
the functional proofs pin, split after each load of a pointer from the frame.
Two runs at the same point (`GenPoint`, as on x86-64) agree on the public
descriptor, the octets consumed, the progress' public words, the state's
request word and the trace still to come: an iteration takes both to the
next point or ends both.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.RISCV64 VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Impl.RsaKeyGen.RISCV64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch
open VG.Proof.Rsa.RISCV64 (InvLaw)
open VG.Proof.MillerRabin.RISCV64 (RoundImpl)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)
open VG.Proof.RsaKeyGen.RISCV64.Search (WP.keepS KeepS two_piece two_map two_ite no_pins relCT_pushRa relCT_alloc)

/-! ## The point -/

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

abbrev GenPoint.status (q : GenPoint) : Nat := traceStatus q.trace
abbrev GenPoint.cand (q : GenPoint) : Nat := traceUsed q.trace
abbrev GenPoint.key (q : GenPoint) : Nat := traceKey q.trace

/-- Whether the key search goes on past the point's step. -/
def GenPoint.continues (q : GenPoint) : Prop :=
  (q.status = 3 ∧ ¬q.left ≤ 1) ∨ (q.status = 1 ∧ q.cand ≠ 0 ∧ (q.ph = 0 ∨ q.key = 2))

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

/-- After an iteration: the next point and the loop's condition, or its end. -/
def GenCTStep (q : GenPoint) (t : State) : Prop :=
  (q.continues ∧ isa.eval (.zero .a6) t = some true ∧ GenCTL q.next t) ∨
    (¬q.continues ∧ isa.eval (.zero .a6) t = some false)

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

theorem gen_ct_step [InvLaw] (v : RoundImpl) (q : GenPoint) (s : State) (h : GenCTL q s) :
    WP isa (iteration (searchCall v) keyCall) s (GenCTStep q) := by
  obtain ⟨o, st, ha, hl, -⟩ := h
  have hi : GenIter q.inputs o ((tailOf q.inputs o q.used st).consume q.used []) q.used st s := ⟨hl, [], rfl⟩
  unfold iteration
  simp only [seqs]
  refine WP.seq (WP.mono (search_run v hl) fun t hs => ?_)
  refine WP.seq (WP.mono (classify_ok hi hs) fun u hc => ?_)
  rcases hc with ⟨hcs, hct⟩ | ⟨hcs, hd⟩
  · obtain ⟨o', st', ha', hl', hr'⟩ := next_point ha hct
    refine WP.mono (status_guard hl'.toGenFrame hct.status (by decide)) fun x ⟨⟨⟨hx, hmem⟩, k⟩, hy⟩ =>
      .inl ⟨(continues_iff ha hl.toGenFrame).mp hcs, hx, o', st', ha', ⟨hl'.toGenFrame.keepK k hmem hy
        (fun r hr => by revert r; decide), by rw [hmem]; exact hl'.key⟩, by rw [hmem]; exact hr'⟩
  · have hlt := keyStatus_lt ((tailOf q.inputs o q.used st).consume q.used [])
    refine WP.mono (status_guard hd.1 hd.2.1 (by omega)) fun x ⟨⟨⟨hx, _⟩, _⟩, _⟩ =>
      .inr ⟨fun h => hcs ((continues_iff ha hl.toGenFrame).mpr h), ?_⟩
    refine hx.trans ?_; congr 1; simp only [decide_eq_false_iff_not]; omega

/-! ## Pieces checked by the taint analysis -/

/-- A frame state of some run with the public descriptor `p`. -/
def GenAny (p : GenPublic) (s : State) : Prop := ∃ original used st, GenFrame p original used st s

theorem gen_any_pins : Pins GenAny [.s0] := by
  intro p s t ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.s0.trans h₂.s0.symm

theorem two_leaf {α : Type} {Φ : α → State → Prop} {c : Prog isa} (f : α → GenPublic)
    (hΦ : ∀ a s, Φ a s → GenAny (f a) s) (hc : RelCT isa (Two GenAny) c fun _ _ => True) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨f a, hΦ a _ h₁, hΦ a _ h₂, hsp⟩) fun _ _ h => h

/-- A block that loads a pointer from the frame, then uses it: the load from
the frame's base, and the rest from the base and the pointer, which the
functional proofs fix. -/
theorem two_load {α : Type} {Φ : α → State → Prop} {r : Reg} {j : Nat} {rest : List Instr}
    (F v : α → BitVec 64) (hr : r ≠ .s0)
    (hld : ∀ a s, Φ a s → s.gpr .s0 = F a ∧ InRegions (s.rd ++ s.wr) (F a + BitVec.ofNat 64 (8 * j)) 8 ∧
      (F a + BitVec.ofNat 64 (8 * j)).toNat % 8 = 0 ∧ s.mem.readW (F a + BitVec.ofNat 64 (8 * j)) 64 = v a)
    (hj : 8 * j < 2048)
    {h₁ : VG.Taint.Hint taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.s0]) (.block [ldf r j]) h₁).isSome = true)
    {h₂ : VG.Taint.Hint taint.T}
    (ht₂ : (taint.check (Taint.ofRegs [.s0, r]) (.block rest) h₂).isSome = true) :
    RelCT isa (Two Φ) (.block (ldf r j :: rest)) fun _ _ => True := by
  change RelCT isa (Two Φ) (.block ([ldf r j] ++ rest)) _
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun a t => t.gpr .s0 = F a ∧ t.gpr r = v a) [.s0]
    (fun a _ _ h₁ h₂ x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      rw [(hld a _ h₁).1, (hld a _ h₂).1]) ht₁ ?_) ?_)
  · intro a s hs
    obtain ⟨h31, hin, hal, hv⟩ := hld a s hs
    refine WP.of_runBlock ⟨s.write r (s.mem.readW (s.gpr .s0 + BitVec.ofNat 64 (8 * j)) 64), ?_, ?_⟩
    · rw [runBlock_cons, ldf, exec_load_d hj (by rw [h31]; exact hal) (by rw [h31]; exact hin)]
      rfl
    · rw [RegUpd.gpr_write_of_ne _ _ (fun e => hr e.symm), RegUpd.gpr_write_self, h31, hv]
      exact ⟨rfl, rfl⟩
  · exact two_taint [.s0, r] (fun a _ _ h₁ h₂ x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) ht₂

/-- A loop state's frame word, read. -/
theorem GenFrame.ldf_facts {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) {j : Nat} {v : BitVec 64} (hj : (j, v) ∈ p.headers used) :
    s.gpr .s0 = p.F ∧ InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 (8 * j)) 8 ∧
      (p.F + BitVec.ofNat 64 (8 * j)).toNat % 8 = 0 ∧ s.mem.readW (p.F + BitVec.ofNat 64 (8 * j)) 64 = v :=
  ⟨h.s0, h.frame_ld _ (by have := GenPublic.headers_bound _ _ _ hj; omega),
    h.frame_al (by have := GenPublic.headers_bound _ _ _ hj; omega) (by omega), h.slot hj⟩

/-- `nextPrime phase`, from any frame state. -/
theorem nextPrime_ct (phase : Nat) (hph : phase < 2) :
    RelCT isa (Two GenAny) (.block (nextPrime phase)) fun _ _ => True := by
  unfold nextPrime
  rcases (by omega : phase = 0 ∨ phase = 1) with rfl | rfl <;>
  exact two_load (r := .t2) (j := 7) GenPublic.F GenPublic.stp (by decide)
    (fun p s ⟨_, _, _, h⟩ => h.ldf_facts (by simp [GenPublic.headers])) (by decide) (by taint_decide)
    (by taint_decide)

/-- `finishWith status`, from any frame state. -/
theorem finishWith_ct (status : Nat) (hs : status < 4) :
    RelCT isa (Two GenAny) (.block (finishWith status)) fun _ _ => True := by
  unfold finishWith
  rcases (by omega : status = 0 ∨ status = 1 ∨ status = 2 ∨ status = 3) with rfl | rfl | rfl | rfl <;>
  exact two_load (r := .t2) (j := 7) GenPublic.F GenPublic.stp (by decide)
    (fun p s ⟨_, _, _, h⟩ => h.ldf_facts (by simp [GenPublic.headers])) (by decide) (by taint_decide)
    (by taint_decide)

/-- Before `clear`: the region to zero in frame words 12 and 13. -/
def ClearCT (a : GenPublic × Addr × Nat) (s : State) : Prop :=
  GenAny a.1 s ∧ word s.mem a.1.F (8 * 12) = a.2.1 ∧ word s.mem a.1.F (8 * 13) = BitVec.ofNat 64 a.2.2

/-- The region to zero, loaded. -/
def ClearRegs (a : GenPublic × Addr × Nat) (s : State) : Prop :=
  s.gpr .a1 = a.2.1 ∧ s.gpr .a2 = BitVec.ofNat 64 a.2.2

theorem clear_ct : RelCT isa (Two ClearCT) clear fun _ _ => True := by
  unfold clear
  refine RelCT.seq (two_piece (Ψ := ClearRegs) [.s0] (fun a _ _ h₁ h₂ => gen_any_pins a.1 _ _ h₁.1 h₂.1)
    (by taint_decide) ?_) ?_
  · intro a s ⟨⟨o, u, st, h⟩, h12, h13⟩
    simp only [Bignum.word, off] at h12 h13
    refine WP.mono (WP.keepS [.a1, .a2, .a3] (Q := fun t => ClearRegs a t) ?_ (by decide +kernel)) fun _ h => h.1.1
    unfold ClearRegs
    brun [ldf, h.s0, h.frame_ld 96 (by decide), h.frame_ld 104 (by decide), h.frame_al (d := 96) (by decide) (by decide),
      h.frame_al (d := 104) (by decide) (by decide), h12, h13, exec_li]
  · exact two_taint [.a1, .a2] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

/-- `clearAll`, from any frame state. -/
theorem clearAll_ct : RelCT isa (Two GenAny) clearAll fun _ _ => True := by
  unfold clearAll
  refine RelCT.seq (two_post (two_taint [.s0] gen_any_pins (by taint_decide))
    (Ψ := fun p s => ClearCT (p, p.kp, 9 * p.L) s) ?_) ?_
  · intro p s ⟨o, u, st, h⟩
    obtain ⟨hL1, hL2, -⟩ := h.len_valid
    have h9 : BitVec.ofNat 64 p.L <<< 3 + BitVec.ofNat 64 p.L = BitVec.ofNat 64 (9 * p.L) := by
      rw [VG.Proof.RsaKeyGen.SearchInit.shl_ofNat _ _ (by omega), VG.Proof.RsaKeyGen.SearchInit.add_ofNat]; congr 1; omega
    refine WP.mono (setAll_ok h) fun t ⟨⟨hm, k⟩, hy⟩ => ?_
    obtain ⟨g, w12, w13, -⟩ := store_region h hm k hy (by decide)
    exact ⟨⟨o, u, st, g⟩, w12, w13.trans h9⟩
  · exact (clear_ct).mono (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨(a, a.kp, 9 * a.L), h₁, h₂, hsp⟩) fun _ _ h => h

/-- `fail status`, from any frame state. -/
theorem fail_ct (status : Nat) (hs : status < 4) : RelCT isa (Two GenAny) (fail status) fun _ _ => True := by
  unfold fail
  refine RelCT.seq (two_post clearAll_ct (Ψ := GenAny) fun p s ⟨o, u, st, h⟩ =>
    WP.mono (clearAll_ok h) fun t ⟨g, _, _⟩ => ⟨o, u, st, g⟩) (finishWith_ct status hs)

/-! ## The prime search's call -/

theorem outOf_ph {p : GenPublic} {st₁ st₂ : KeyProgress} (h : phaseWord st₁.phase = phaseWord st₂.phase) :
    outOf p st₁ = outOf p st₂ := by
  unfold outOf; rw [h]

theorem plenOf_ph {p : GenPublic} {st₁ st₂ : KeyProgress} (h : phaseWord st₁.phase = phaseWord st₂.phase) :
    plenOf p st₁ = plenOf p st₂ := by
  unfold plenOf; rw [h]

/-- A loop state at the point, past the allocation of the search's frame. -/
def AllocSCT (q : GenPoint) (u : State) : Prop := ∃ s, GenCTL q s ∧ u = allocd 32 s

theorem alloc_s_pins : Pins AllocSCT [.s0] := by
  rintro q _ _ ⟨a, ⟨o₁, _, _, h₁, _⟩, rfl⟩ ⟨b, ⟨o₂, _, _, h₂, _⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.s0.trans h₂.s0.symm

/-- The search's stack arguments stored. -/
def StackSCT (q : GenPoint) (u : State) : Prop :=
  ∃ o st s, AtPoint q o st ∧ GenLive q.inputs o q.used st s ∧ word s.mem q.inputs.stp 24 = q.req ∧
    u.mem = callMem q.inputs q.used s ∧ KeepS stackRegs (allocd 32 s) u ∧ u.syms = (allocd 32 s).syms

theorem stack_s_ready (q : GenPoint) (u : State) (h : AllocSCT q u) :
    WP isa (.block searchStack) u (StackSCT q) := by
  obtain ⟨s, ⟨o, st, ha, hl, hw⟩, rfl⟩ := h
  exact WP.mono (search_stack_ok hl.toGenFrame) fun _ ⟨⟨hm, k⟩, hy⟩ => ⟨o, st, s, ha, hl, hw, hm, k, hy⟩

theorem search_args_ct : RelCT isa (Two StackSCT) (.block searchArgs) fun _ _ => True := by
  unfold searchArgs
  refine two_load (r := .t2) (j := 7) (fun q => q.inputs.F) (fun q => q.inputs.stp) (by decide) ?_ (by decide)
    (by taint_decide) (by taint_decide)
  rintro q u ⟨o, st, s, -, hl, -, hm, ku, -⟩
  have hf := alloc_args_frame hl.toGenFrame (used := q.used)
  rw [← hm] at hf
  refine ⟨(ku.gpr .s0 (by decide)).trans hl.s0, hl.frame_ldA (t := u) (k := 32) ku.wr 56 (by decide),
    hl.frame_al (d := 56) (by decide) (by decide), ?_⟩
  exact hl.call_word hf (j := 7) (v := q.inputs.stp) (by simp [GenPublic.headers])

/-- The search's entry, before the call. -/
def CallSCT (q : GenPoint) (w : State) : Prop :=
  ∃ o st s u, AtPoint q o st ∧ GenLive q.inputs o q.used st s ∧ word s.mem q.inputs.stp 24 = q.req ∧
    u.mem = callMem q.inputs q.used s ∧ KeepS stackRegs (allocd 32 s) u ∧ u.syms = (allocd 32 s).syms ∧
    SearchRegs q.inputs q.used st w ∧ w.mem = u.mem ∧ KeepS searchArgRegs u w ∧ w.syms = u.syms

theorem args_s_ready (q : GenPoint) (u : State) (h : StackSCT q u) :
    WP isa (.block searchArgs) u (CallSCT q) := by
  obtain ⟨o, st, s, ha, hl, hw, hm, ku, hyu⟩ := h
  exact WP.mono (search_args_ok hl.toGenFrame hm ku) fun _ ⟨⟨⟨hr, hmw⟩, kw⟩, hyw⟩ =>
    ⟨o, st, s, u, ha, hl, hw, hm, ku, hyu, hr, hmw, kw, hyw⟩

/-- The search's exponent and state words at its entry. -/
theorem callS_state {p : GenPublic} {original s u : State} {used : Nat} {st : KeyProgress}
    (h : GenLive p original used st s) (hu : u.sp = callSp p) (ha : SearchRegs p used st u)
    (hm : u.mem = callMem p used s) :
    Search.searchE (callS p used st u) = p.eB ∧
      Spec.Rsa.wordsAt (callS p used st u).mem (stackArg (callS p used st u) 3) 4 =
        [BitVec.ofNat 64 st.remaining, BitVec.ofNat 64 p.L, BitVec.ofNat 64 (primeEntropy p.L),
          word s.mem p.stp 24] := by
  have hf := h.input.cfacts
  have hfs : Frame [cStack p] s.mem u.mem := by rw [hm]; exact call_stack_frame h.toGenFrame
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨-, -, -, sT, -⟩ := hst
  obtain ⟨-, -, -, a3⟩ := callS_args (st := st) hu hm
  have hword (d : Nat) (hd : d + 8 ≤ 56) : word (callS p used st u).mem p.stp d = word s.mem p.stp d :=
    hfs.readW (r := cS p) (Offset.contains_base _ hd (by have := hf.nT; omega))
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact sT) (by decide)
  refine ⟨?_, ?_⟩
  · simp only [Search.searchE, callS_gpr (show Reg.a3 ∉ linkRegs by decide),
      callS_gpr (show Reg.a4 ∉ linkRegs by decide), ha.2.2.2.1, ha.2.2.2.2.1,
      toNat_ofNat_lt (show 8 < 2 ^ 64 by decide), callS_mem]
    rw [← h.state.e]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hfs.bytes (R := ⟨p.stp + 48, 8⟩) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact sT.sub_left (by
        rw [show (p.stp + 48 : Addr) = p.stp + BitVec.ofNat 64 48 from rfl]; exact Offset.sub_base _ (by decide)))
      (by show 8 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  · rw [a3]
    show [word _ p.stp (8 * 0), word _ p.stp (8 * 1), word _ p.stp (8 * 2), word _ p.stp (8 * 3)] = _
    rw [hword _ (by decide), hword _ (by decide), hword _ (by decide), hword _ (by decide)]
    have h0 := h.state.remaining
    have h1 := h.state.len
    have h2 := h.state.cap
    simp only [Nat.reduceMul] at h0 h1 h2 ⊢
    rw [h0, h1, h2]

/-- What the call needs, from a run's entry. -/
theorem CallSCT.facts {q : GenPoint} {w : State} (h : CallSCT q w) :
    ∃ o st s, AtPoint q o st ∧ GenLive q.inputs o q.used st s ∧ word s.mem q.inputs.stp 24 = q.req ∧
      w.sp = callSp q.inputs ∧ SearchRegs q.inputs q.used st w ∧ w.mem = callMem q.inputs q.used s ∧
      Search.searchPre (callS q.inputs q.used st w) ∧
      Covers (sReads q.inputs q.used st ++ sWrites q.inputs st) (w.rd ++ w.wr) ∧
      Covers (sWrites q.inputs st) w.wr ∧ w.syms Impl.RsaKeyGen.TrialTable32.symbol = q.inputs.T := by
  obtain ⟨o, st, s, u, ha, hl, hw, hm, ku, hyu, hr, hmw, kw, hyw⟩ := h
  have hu : w.sp = callSp q.inputs := kw.sp.trans (ku.sp.trans (alloc_call_sp hl.toGenFrame))
  have hm' : w.mem = callMem q.inputs q.used s := hmw.trans hm
  have hy : w.syms = o.syms := hyw.trans (hyu.trans hl.syms)
  have krd : w.rd = (allocd 32 s).rd := kw.rd.trans ku.rd
  have kwr : w.wr = (allocd 32 s).wr := kw.wr.trans ku.wr
  have hT : w.syms Impl.RsaKeyGen.TrialTable32.symbol = q.inputs.T := by rw [hy, ← hl.input.2]; rfl
  have hft : Frame (GenInput.changes o) o.mem w.mem :=
    hl.tab.trans (frame_of_callChanges o (by rw [hm']; exact alloc_args_frame hl.toGenFrame))
  have htab : ∀ i < 1024, w.mem.readW (q.inputs.T + BitVec.ofNat 64 (8 * i)) 64 =
      Impl.RsaKeyGen.TrialTable32.packed.getD i 0 := by
    intro i hi; rw [← hT, hy]; exact hl.input.tab_frame hft i hi
  exact ⟨o, st, s, ha, hl, hw, hu, hr, hm', callS_pre hl hu hr hm' hT htab,
    search_covers_reads hl.toGenFrame krd kwr, search_covers_writes hl.toGenFrame kwr, hT⟩

theorem search_call_ct (v : RoundImpl) : RelCT isa (Two CallSCT) (searchCall v) fun _ _ => True := by
  refine RelCT.callEx (k := Search.searchContract) (Search.search_correct (Search.Cand.ofRound v))
    (Search.search_constantTime (Search.Cand.ofRound v)) fun w₁ w₂ ⟨q, h₁, h₂, _⟩ => ?_
  obtain ⟨o₁, st₁, s₁, a₁, l₁, rq₁, hu₁, r₁, m₁, pre₁, cr₁, cw₁, T₁⟩ := h₁.facts
  obtain ⟨o₂, st₂, s₂, a₂, l₂, rq₂, hu₂, r₂, m₂, pre₂, cr₂, cw₂, T₂⟩ := h₂.facts
  have hph : phaseWord st₁.phase = phaseWord st₂.phase := a₁.2.1.trans a₂.2.1.symm
  have hres₁ := callS_result l₁ hu₁ r₁ m₁
  have hres₂ := callS_result l₂ hu₂ r₂ m₂
  obtain ⟨e₁, ws₁⟩ := callS_state l₁ hu₁ r₁ m₁
  obtain ⟨e₂, ws₂⟩ := callS_state l₂ hu₂ r₂ m₂
  have hlen₁ : Search.searchLen (callS q.inputs q.used st₁ w₁) = q.inputs.L := by
    simp only [Search.searchLen, callS_gpr (show Reg.a1 ∉ linkRegs by decide), r₁.2.1]
    exact toNat_ofNat_lt (by have := l₁.input.cfacts.len.2.1; omega)
  have hlen₂ : Search.searchLen (callS q.inputs q.used st₂ w₂) = q.inputs.L := by
    simp only [Search.searchLen, callS_gpr (show Reg.a1 ∉ linkRegs by decide), r₂.2.1]
    exact toNat_ofNat_lt (by have := l₂.input.cfacts.len.2.1; omega)
  obtain ⟨b0, b1, b2, b3⟩ := callS_args (st := st₁) hu₁ m₁
  obtain ⟨c0, c1, c2, c3⟩ := callS_args (st := st₂) hu₂ m₂
  obtain ⟨x3, x4, x5, x6, x7, x8, x9, x10⟩ := r₁
  obtain ⟨y3, y4, y5, y6, y7, y8, y9, y10⟩ := r₂
  refine ⟨sReads q.inputs q.used st₁, sWrites q.inputs st₁, sReads q.inputs q.used st₂, sWrites q.inputs st₂,
    pre₁, pre₂, ?_, cr₁, cw₁, cr₂, cw₂⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, e₁.trans e₂.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show w₁.sp = w₂.sp; rw [hu₁, hu₂]
  · rw [callS_gpr (by decide), callS_gpr (by decide), x3, y3, outOf_ph hph]
  · rw [callS_gpr (by decide), callS_gpr (by decide), x4, y4]
  · rw [callS_gpr (by decide), callS_gpr (by decide), x5, y5]
  · rw [callS_gpr (by decide), callS_gpr (by decide), x6, y6]
  · rw [callS_gpr (by decide), callS_gpr (by decide), x7, y7]
  · rw [callS_gpr (by decide), callS_gpr (by decide), x8, y8]
  · rw [callS_gpr (by decide), callS_gpr (by decide), x9, y9, plenOf_ph hph]
  · rw [callS_gpr (by decide), callS_gpr (by decide), x10, y10]
  · match j, hj with
    | 0, _ => rw [b0, c0]
    | 1, _ => rw [b1, c1]
    | 2, _ => rw [b2, c2]
    | 3, _ => rw [b3, c3]
  · rw [ws₁, ws₂, a₁.2.2.1, a₂.2.2.1, rq₁, rq₂]
  · rw [hres₁, hres₂, a₁.status, a₂.status]
  · rw [hres₁, hres₂, a₁.cand, a₂.cand]
  · rw [hlen₁, hlen₂, hres₁, hres₂]
    exact Entropy.requested_congr (a₁.status.trans a₂.status.symm) (a₁.available.trans a₂.available.symm)
  · rw [hres₁, hres₂, a₁.prime, a₂.prime]
  · show w₁.syms _ = w₂.syms _
    rw [T₁, T₂]

theorem search_run_ct (v : RoundImpl) :
    RelCT isa (Two GenCTL) (searchRun (searchCall v)) fun _ _ => True := by
  unfold searchRun
  refine relCT_alloc (R := fun _ _ => True) ?_
  refine (RelCT.seq (two_piece [.s0] alloc_s_pins (by taint_decide) stack_s_ready)
    (RelCT.seq (two_post search_args_ct args_s_ready) (search_call_ct v))).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocd, hsp]⟩

/-! ## The key's call -/

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

theorem KeyCT.frame {q : GenPoint} {u : State} (h : KeyCT q u) : GenAny q.inputs u :=
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

def AllocKCT (q : GenPoint) (u : State) : Prop := ∃ s, KeyCT q s ∧ u = allocd 80 s

theorem alloc_k_pins : Pins AllocKCT [.s0] := by
  rintro q _ _ ⟨a, h₁, rfl⟩ ⟨b, h₂, rfl⟩ r hr
  exact gen_any_pins q.inputs _ _ h₁.frame h₂.frame r hr

/-- The key's stack arguments stored. -/
def StackKCT (q : GenPoint) (u : State) : Prop :=
  ∃ s, KeyCT q s ∧ u.mem = keyMem q.inputs s ∧ KeepS keyStackRegs (allocd 80 s) u

theorem stack_k_pins : Pins StackKCT [.s0] := by
  rintro q _ _ ⟨a, h₁, -, k₁⟩ ⟨b, h₂, -, k₂⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  rw [k₁.gpr .s0 (by decide), k₂.gpr .s0 (by decide)]
  exact gen_any_pins q.inputs _ _ h₁.frame h₂.frame .s0 (by simp)

theorem stack_k_ready (q : GenPoint) (u : State) (h : AllocKCT q u) :
    WP isa (.block keyStack) u (StackKCT q) := by
  obtain ⟨s, hs, rfl⟩ := h
  obtain ⟨o, _, _, _, _, _, hm, _⟩ := id hs
  exact WP.mono (key_stack_ok hm.frame) fun _ ⟨⟨hmem, k⟩, _⟩ => ⟨s, hs, hmem, k⟩

/-- The key's entry, before the call. -/
def CallKCT (q : GenPoint) (w : State) : Prop :=
  ∃ s u, KeyCT q s ∧ u.mem = keyMem q.inputs s ∧ KeepS keyStackRegs (allocd 80 s) u ∧
    KeyRegs q.inputs w ∧ w.mem = u.mem ∧ KeepS keyArgRegs u w

theorem args_k_ready (q : GenPoint) (u : State) (h : StackKCT q u) :
    WP isa (.block keyArgs) u (CallKCT q) := by
  obtain ⟨s, hs, hm, ku⟩ := h
  obtain ⟨o, _, _, _, _, _, hmid, _⟩ := id hs
  exact WP.mono (key_args_ok hmid.frame hm ku) fun _ ⟨⟨⟨hr, hmw⟩, kw⟩, _⟩ => ⟨s, u, hs, hm, ku, hr, hmw, kw⟩

/-- The key's public data, from its arguments. -/
theorem key_pub_of {s₁ s₂ : State} (hr : ∀ r ∈ RISCV64.argRegs, s₁.gpr r = s₂.gpr r)
    (ha : ∀ j < 10, stackArg s₁ j = stackArg s₂ j) (hsp : s₁.sp = s₂.sp)
    (he : Spec.Rsa.bytesAt s₁.mem (stackArg s₁ 6) (stackArg s₁ 7).toNat =
      Spec.Rsa.bytesAt s₂.mem (stackArg s₂ 6) (stackArg s₂ 7).toNat)
    (hk : keyStatus (Key.resOf s₁) = keyStatus (Key.resOf s₂)) :
    (Spec.RsaKeyGen.keyContract RISCV64.abi).pub s₁ s₂ := by
  have r0 := hr .a0 (by decide)
  have r1 := hr .a1 (by decide)
  have r2 := hr .a2 (by decide)
  have r3 := hr .a3 (by decide)
  have r4 := hr .a4 (by decide)
  have r5 := hr .a5 (by decide)
  have r6 := hr .a6 (by decide)
  have r7 := hr .a7 (by decide)
  have b0 := ha 0 (by decide)
  have b1 := ha 1 (by decide)
  have b2 := ha 2 (by decide)
  have b3 := ha 3 (by decide)
  have b4 := ha 4 (by decide)
  have b5 := ha 5 (by decide)
  have b6 := ha 6 (by decide)
  have b7 := ha 7 (by decide)
  have b8 := ha 8 (by decide)
  have b9 := ha 9 (by decide)
  sig_pub [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, RISCV64.abi, RISCV64.argRegs,
    Key.stackArgs_ten, List.append_eq, List.range, List.range.loop]
  sig_reduce [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, RISCV64.abi, RISCV64.argRegs,
    Key.stackArgs_ten, List.append_eq, List.range, List.range.loop, List.getD]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | trivial
    | rw [hk, he]

theorem key_call_ct [InvLaw] : RelCT isa (Two CallKCT) keyCall fun _ _ => True := by
  refine RelCT.callEx (k := Key.fnContract) (fun s' h' => Key.code_correct s' h') Key.key_ct
    fun w₁ w₂ ⟨q, h₁, h₂, _⟩ => ?_
  obtain ⟨s₁, u₁, c₁, m₁, k₁, r₁, mw₁, kw₁⟩ := h₁
  obtain ⟨s₂, u₂, c₂, m₂, k₂, r₂, mw₂, kw₂⟩ := h₂
  obtain ⟨o₁, _, _, _, _, _, hm₁, _⟩ := id c₁
  obtain ⟨o₂, _, _, _, _, _, hm₂, _⟩ := id c₂
  have g₁ := hm₁.frame
  have g₂ := hm₂.frame
  have hu₁ : w₁.sp = keySp q.inputs := kw₁.sp.trans (k₁.sp.trans (alloc_key_sp g₁))
  have hu₂ : w₂.sp = keySp q.inputs := kw₂.sp.trans (k₂.sp.trans (alloc_key_sp g₂))
  have hmm₁ : w₁.mem = keyMem q.inputs s₁ := mw₁.trans m₁
  have hmm₂ : w₂.mem = keyMem q.inputs s₂ := mw₂.trans m₂
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := callK_args (s := s₁) hu₁ hmm₁
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := callK_args (s := s₂) hu₂ hmm₂
  obtain ⟨e₁, k₁'⟩ := callK_res g₁ hu₁ r₁ hmm₁
  obtain ⟨e₂, k₂'⟩ := callK_res g₂ hu₂ r₂ hmm₂
  have hst₁ := c₁.status
  have hst₂ := c₂.status
  obtain ⟨x3, x4, x5, x6, x7, x8, x9, x10⟩ := r₁
  obtain ⟨y3, y4, y5, y6, y7, y8, y9, y10⟩ := r₂
  refine ⟨kReads q.inputs, kWrites q.inputs, kReads q.inputs, kWrites q.inputs,
    callK_pre g₁ hu₁ ⟨x3, x4, x5, x6, x7, x8, x9, x10⟩ hmm₁, callK_pre g₂ hu₂ ⟨y3, y4, y5, y6, y7, y8, y9, y10⟩ hmm₂,
    key_pub_of ?_ ?_ (by show w₁.sp = w₂.sp; rw [hu₁, hu₂]) (e₁.trans e₂.symm) ?_,
    key_covers_reads g₁ (kw₁.rd.trans k₁.rd) (kw₁.wr.trans k₁.wr), key_covers_writes g₁ (kw₁.wr.trans k₁.wr),
    key_covers_reads g₂ (kw₂.rd.trans k₂.rd) (kw₂.wr.trans k₂.wr), key_covers_writes g₂ (kw₂.wr.trans k₂.wr)⟩
  · intro r hr
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [callK_gpr (by decide), callK_gpr (by decide)]
    exacts [x3.trans y3.symm, x4.trans y4.symm, x5.trans y5.symm, x6.trans y6.symm, x7.trans y7.symm,
      x8.trans y8.symm, x9.trans y9.symm, x10.trans y10.symm]
  · intro j hj
    match j, hj with
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
  · rw [k₁', k₂', hst₁, hst₂]

theorem key_run_ct [InvLaw] : RelCT isa (Two KeyCT) (keyRun keyCall) fun _ _ => True := by
  unfold keyRun
  refine relCT_alloc (R := fun _ _ => True) ?_
  refine (RelCT.seq (two_piece [.s0] alloc_k_pins (by taint_decide) stack_k_ready)
    (RelCT.seq (two_post (two_taint [.s0] stack_k_pins (by taint_decide)) args_k_ready) key_call_ct)).mono ?_
    (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocd, hsp]⟩

/-! ## After the key -/

/-- After the key: its status in `a0`, from the point. -/
def AfterKCT (q : GenPoint) (v : State) : Prop :=
  GenAny q.inputs v ∧ ((v.gpr .a0).setWidth 32).toNat = q.key ∧ q.key < 4

theorem key_after_ready [InvLaw] (q : GenPoint) (u : State) (h : KeyCT q u) :
    WP isa (keyRun keyCall) u (AfterKCT q) := by
  obtain ⟨o, _, _, _, _, _, hm, _⟩ := id h
  exact WP.mono (key_run hm.frame) fun v hk => ⟨⟨o, _, _, hk.frame⟩, hk.status.trans h.status, by
    rw [← h.status]; exact keyStatus_lt' _⟩

/-- The key's status compared with 1. -/
def AK1 (q : GenPoint) (w : State) : Prop :=
  GenAny q.inputs w ∧ w.gpr .a0 = BitVec.ofNat 64 q.key ∧ isa.eval (.zero .t1) w = some (decide (q.key = 1)) ∧
    q.key < 4

/-- The key's status compared with 2. -/
def AK2 (q : GenPoint) (w : State) : Prop :=
  GenAny q.inputs w ∧ isa.eval (.zero .t1) w = some (decide (q.key = 2))

theorem afterKey_ct : RelCT isa (Two AfterKCT) afterKey fun _ _ => True := by
  unfold afterKey
  refine RelCT.seq (two_post (two_taint [] no_pins (by taint_decide)) (Ψ := AK1) ?_) ?_
  · intro q v ⟨⟨o, u, st, g⟩, hs, hk⟩
    exact WP.mono (key_status_guard hs hk) fun w ⟨⟨⟨he, h3, hm⟩, k⟩, hy⟩ =>
      ⟨⟨o, u, st, g.keepK k hm hy (fun r hr => by revert r; decide)⟩, h3, he, hk⟩
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.1.trans h₂.2.2.1.symm)
    (two_leaf GenPoint.inputs (fun _ _ h => h.1.1) (finishWith_ct 1 (by decide))) ?_
  refine RelCT.seq (two_post (two_taint [] no_pins (by taint_decide)) (Ψ := AK2) ?_) ?_
  · rintro q w ⟨⟨⟨o, u, st, g⟩, h3, -, hk⟩, -⟩
    exact WP.mono (sub_guard3_t1 h3 (by omega)) fun x ⟨⟨⟨he, hm⟩, k⟩, hy⟩ =>
      ⟨⟨o, u, st, g.keepK k hm hy (fun r hr => by revert r; decide)⟩, he⟩
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (two_leaf GenPoint.inputs (fun _ _ h => h.1.1) (nextPrime_ct 0 (by decide)))
    (two_leaf GenPoint.inputs (fun _ _ h => h.1.1) (fail_ct 2 (by decide)))

/-! ## The classification -/

/-- After the search, at the point. -/
def AfterCT (q : GenPoint) (t : State) : Prop :=
  ∃ o st s, AtPoint q o st ∧ GenLive q.inputs o q.used st s ∧ word s.mem q.inputs.stp 24 = q.req ∧
    AfterSearch q.inputs o q.used st s t

/-- After the count of the octets consumed, at the point. -/
def MidCT (q : GenPoint) (u : State) : Prop :=
  ∃ o st final, AtPoint q o st ∧ Mid q.inputs o final q.used st u ∧
    u.gpr .a0 = BitVec.ofNat 64 q.status ∧ u.gpr .t1 = BitVec.ofNat 64 q.cand

theorem MidCT.any {q : GenPoint} {u : State} (h : MidCT q u) : GenAny q.inputs u :=
  let ⟨o, _, _, _, hm, _⟩ := h; ⟨o, _, _, hm.frame⟩

theorem head_pins : Pins (fun (q : GenPoint) u => u.gpr .s0 = q.inputs.F ∧ u.gpr .t1 = q.inputs.up) [.s0, .t1] := by
  intro q s t h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]

theorem head1_ready (q : GenPoint) (t : State) (h : AfterCT q t) :
    WP isa (.block [.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32, ldf .t1 2]) t fun u =>
      u.gpr .s0 = q.inputs.F ∧ u.gpr .t1 = q.inputs.up := by
  obtain ⟨o, st, s, -, -, -, ha⟩ := h
  have g := ha.frame
  obtain ⟨h31, hin, hal, hv⟩ := g.ldf_facts (j := 2) (v := q.inputs.up) (by simp [GenPublic.headers])
  simp only [Nat.reduceMul] at hin hal hv
  refine WP.mono (WP.keepS [.a0, .t1] (Q := fun u => u.gpr .t1 = q.inputs.up) ?_ (by decide +kernel)) fun u hu =>
    ⟨(hu.1.2.gpr .s0 (by decide)).trans h31, hu.1.1⟩
  brun [ldf, h31, hin, hal, hv]

theorem head_ready (q : GenPoint) (t : State) (h : AfterCT q t) :
    WP isa (.block (low32 .a0 ++ ([ldf .t1 2, .load .d .t1 .t1 0, ldf .t2 8, .add .t2 .t2 .t1,
      stf .t2 8] : List Instr))) t (MidCT q) := by
  obtain ⟨o, st, s, ha, hl, hw, haf⟩ := h
  refine WP.mono (after_head (final := (tailOf q.inputs o q.used st).consume q.used []) ⟨hl, [], rfl⟩ haf)
    fun u ⟨h3, h11, hm⟩ => ⟨o, st, _, ha, hm, by rw [h3, ha.status], by rw [h11, ha.cand]⟩

/-- The status compared with 3. -/
def Sub3CT (q : GenPoint) (u : State) : Prop :=
  MidCT q u ∧ isa.eval (.zero .t2) u = some (decide (q.status = 3))

theorem sub3_ready (q : GenPoint) (u : State) (h : MidCT q u) :
    WP isa (.block [.addi .t2 .a0 (-3)]) u (Sub3CT q) := by
  obtain ⟨o, st, final, ha, hm, h3, h11⟩ := h
  have hst : q.status < 2 ^ 64 := by rw [← ha.status]; have := prime_status_lt (rOf q.inputs o q.used st); omega
  exact WP.mono (sub_guard3_t2 h3 hst) fun v ⟨⟨⟨he, hmem⟩, k⟩, hy⟩ =>
    ⟨⟨o, st, final, ha, hm.keepK k hmem hy (fun r hr => by revert r; decide),
      by rw [k.gpr .a0 (by decide)]; exact h3, by rw [k.gpr .t1 (by decide)]; exact h11⟩, he⟩

/-- The exhausted generation's header loaded. -/
def LeftCT (q : GenPoint) (u : State) : Prop :=
  ∃ o st final, AtPoint q o st ∧ Mid q.inputs o final q.used st u ∧ u.gpr .t2 = q.inputs.stp ∧
    isa.eval (.zero .a7) u = some (decide (q.left ≤ 1))

theorem left_ready (q : GenPoint) (u : State) (h : MidCT q u) :
    WP isa (.block [ldf .t2 7, .load .d .t1 .t2 40, .shift .srl .d .a7 .t1 1]) u (LeftCT q) := by
  obtain ⟨o, st, final, ha, hm, -, -⟩ := h
  refine WP.mono (left_ok hm.frame) fun v ⟨⟨⟨he, h12, _, hmem⟩, k⟩, hy⟩ =>
    ⟨o, st, final, ha, hm.keepK k hmem hy (fun r hr => by revert r; decide), h12, ?_⟩
  rw [he]; dsimp only; rw [ha.1]

/-- The decrement's first piece: `r12` reloaded. -/
theorem dec1_ok {p : GenPublic} {original s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) (h12 : s.gpr .t2 = p.stp) :
    WP isa (.block [.addi .t1 .t1 (-1), .store .d .t1 .t2 40, ldf .t2 7]) s fun t =>
      t.gpr .s0 = p.F ∧ t.gpr .t2 = p.stp := by
  have sst := h.stateScr
  have h7 := h.slot (j := 7) (v := p.stp) (by simp [GenPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h7
  have hs5 : InRegions s.wr (p.stp + BitVec.ofNat 64 40) 8 := sst.st (d := 40) (n := 8) (by decide)
  have hnF : p.F.toNat + 112 ≤ 2 ^ 64 := (h.input.frame_scr h.wr).nowrap
  have hnS : p.stp.toNat + 56 ≤ 2 ^ 64 := sst.nowrap
  have hk7 : ∀ v : BitVec 64, (s.mem.writeW (p.stp + BitVec.ofNat 64 40) v).readW (p.F + BitVec.ofNat 64 56) 64 =
      p.stp := fun v => by
    refine ((Frame.writeW (Frame.refl _ _) (List.mem_singleton_self (⟨p.stp, 56⟩ : Region)) v
      (Offset.contains_base _ (by decide) (by omega))).readW (r := p.frame)
      (Offset.contains_base _ (by decide) (by omega)) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq; exact h.state_frame) (by decide)).trans h7
  have ha5 : (p.stp + BitVec.ofNat 64 40).toNat % 8 = 0 := sst.al8 (d := 40) (by decide) (by decide)
  refine WP.mono (WP.keepS [.t1, .t2] (Q := fun t => t.gpr .t2 = p.stp) ?_ (by decide +kernel)) fun t ht =>
    ⟨(ht.1.2.gpr .s0 (by decide)).trans h.s0, ht.1.1⟩
  brun [ldf, h.s0, h12, h.frame_ld 56 (by decide), h.frame_al (d := 56) (by decide) (by decide), hk7, hs5, ha5]

theorem exhaustedGen_ct : RelCT isa (Two MidCT) exhaustedGen fun _ _ => True := by
  unfold exhaustedGen
  refine RelCT.seq (two_post (two_load (r := .t2) (j := 7) (fun q => q.inputs.F) (fun q => q.inputs.stp) (by decide)
    (fun q u h => let ⟨_, _, _, _, hm, _⟩ := h; hm.frame.ldf_facts (by simp [GenPublic.headers])) (by decide)
    (by taint_decide) (by taint_decide)) left_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => let ⟨_, _, _, _, _, _, e₁⟩ := h₁; let ⟨_, _, _, _, _, _, e₂⟩ := h₂; e₁.trans e₂.symm)
    (two_leaf GenPoint.inputs (fun _ _ h => let ⟨o, _, _, _, hm, _⟩ := h.1; ⟨o, _, _, hm.frame⟩) (fail_ct 3 (by decide)))
    ?_
  change RelCT isa _ (.block ([.addi .t1 .t1 (-1), .store .d .t1 .t2 40, ldf .t2 7] ++
    [ldf .t1 11, .store .d .t1 .t2 0, .li .t1 0, .store .d .t1 .t2 32, .li .t1 4, stf .t1 10])) _
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun q t => t.gpr .s0 = q.inputs.F ∧ t.gpr .t2 = q.inputs.stp)
    [.s0, .t2] ?_ (by taint_decide) ?_) ?_)
  · rintro q s t ⟨⟨_, _, _, _, hm₁, h₁, -⟩, -⟩ ⟨⟨_, _, _, _, hm₂, h₂, -⟩, -⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [hm₁.frame.s0.trans hm₂.frame.s0.symm, h₁.trans h₂.symm]
  · rintro q s ⟨⟨_, _, _, _, hm, h12, -⟩, -⟩
    exact dec1_ok hm.frame h12
  · exact two_taint [.s0, .t2] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

/-- A prime accepted, at the point: the phase tested. -/
def PhCT (q : GenPoint) (u : State) : Prop :=
  ∃ o st final, AtPoint q o st ∧ Mid q.inputs o final q.used st u ∧
    isa.eval (.zero .t1) u = some (decide (q.ph = 0)) ∧
    (q.status = 1 → q.cand ≠ 0 → ∃ c, (rOf q.inputs o q.used st).outcome = .accepted c ∧
      0 < (rOf q.inputs o q.used st).used)

theorem ph_ready (q : GenPoint) (u : State) (h : Sub3CT q u ∧ q.status ≠ 0 ∧ q.status ≠ 3) :
    WP isa (.block [ldf .t2 7, .load .d .t1 .t2 32]) u (PhCT q) := by
  obtain ⟨⟨⟨o, st, final, ha, hm, -, -⟩, -⟩, h0, h3⟩ := h
  refine WP.mono (phase_ok hm.frame) fun v ⟨⟨⟨he, _, hmem⟩, k⟩, hy⟩ =>
    ⟨o, st, final, ha, hm.keepK k hmem hy (fun r hr => by revert r; decide), by rw [he, ha.2.1], fun _ hc => ?_⟩
  have hs := ha.status
  have hcd := ha.cand
  cases ho : (rOf q.inputs o q.used st).outcome with
  | entropy k a => rw [rOf_status, ho] at hs; exact absurd hs.symm h0
  | exhausted => rw [rOf_status, ho] at hs; exact absurd hs.symm h3
  | accepted c => exact ⟨c, rfl, by omega⟩

theorem accepted_ct [InvLaw] :
    RelCT isa (Two fun q u => (Sub3CT q u ∧ q.status ≠ 0 ∧ q.status ≠ 3) ∧ q.cand ≠ 0) (accepted keyCall)
      fun _ _ => True := by
  unfold accepted
  refine RelCT.seq (two_post (Ψ := fun q u => PhCT q u ∧ q.cand ≠ 0 ∧ q.status ≠ 0 ∧ q.status ≠ 3)
    (two_load (r := .t2) (j := 7) (fun q => q.inputs.F) (fun q => q.inputs.stp) (by decide)
    (fun q u h => let ⟨⟨⟨⟨_, _, _, _, hm, _⟩, _⟩, _⟩, _⟩ := h; hm.frame.ldf_facts (by simp [GenPublic.headers]))
    (by decide) (by taint_decide) (by taint_decide))
    fun q u h => WP.mono (ph_ready q u h.1) fun v hv => ⟨hv, h.2, h.1.2⟩) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => let ⟨_, _, _, _, _, e₁, _⟩ := h₁.1; let ⟨_, _, _, _, _, e₂, _⟩ := h₂.1;
    e₁.trans e₂.symm)
    (two_leaf GenPoint.inputs (fun _ _ h => let ⟨o, _, _, _, hm, _⟩ := h.1.1; ⟨o, _, _, hm.frame⟩)
      (nextPrime_ct 1 (by decide))) ?_
  have hkey : ∀ q u, (PhCT q u ∧ q.cand ≠ 0 ∧ q.status ≠ 0 ∧ q.status ≠ 3) ∧
      isa.eval (.zero .t1) u = some false → KeyCT q u := by
    rintro q u ⟨⟨⟨o, st, final, ha, hm, he, hacc⟩, hc, h0, h3⟩, hf⟩
    have hs1 : q.status = 1 := by
      rw [← ha.status]
      have := ha.status
      cases ho : (rOf q.inputs o q.used st).outcome with
      | entropy k a => rw [rOf_status, ho] at this; exact absurd this.symm h0
      | exhausted => rw [rOf_status, ho] at this; exact absurd this.symm h3
      | accepted c => rw [rOf_status, ho]; rfl
    obtain ⟨c, ho, hpos⟩ := hacc hs1 hc
    have hph : q.ph ≠ 0 := by
      intro h; rw [he, h] at hf; cases hf
    cases hp : st.phase with
    | p => exact absurd (by rw [← ha.2.1, hp]; rfl) hph
    | q pB => exact ⟨o, st, final, c, pB, ha, hm, ho, hpos, hp⟩
  refine RelCT.seq (two_post (Ψ := AfterKCT) ((key_run_ct).mono
    (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, hkey q _ h₁, hkey q _ h₂, hsp⟩) fun _ _ h => h)
    fun q u h => key_after_ready q u (hkey q u h)) ?_
  exact afterKey_ct

theorem MidCT.a0 {q : GenPoint} {u : State} (h : MidCT q u) : u.gpr .a0 = BitVec.ofNat 64 q.status :=
  let ⟨_, _, _, _, _, h3, _⟩ := h; h3

theorem MidCT.t1 {q : GenPoint} {u : State} (h : MidCT q u) : u.gpr .t1 = BitVec.ofNat 64 q.cand :=
  let ⟨_, _, _, _, _, _, h11⟩ := h; h11

theorem MidCT.s0 {q : GenPoint} {u : State} (h : MidCT q u) : u.gpr .s0 = q.inputs.F :=
  let ⟨_, _, _, _, hm, _⟩ := h; hm.frame.s0

theorem MidCT.status_lt {q : GenPoint} {u : State} (h : MidCT q u) : q.status < 2 ^ 64 := by
  obtain ⟨o, st, _, ha, _⟩ := h
  rw [← ha.status]; have := prime_status_lt (rOf q.inputs o q.used st); omega

theorem MidCT.cand_lt {q : GenPoint} {u : State} (h : MidCT q u) : q.cand < 2 ^ 64 := by
  obtain ⟨o, st, _, ha, hm, _⟩ := h
  rw [← ha.cand]; have := hm.frame.used_le; have := hm.frame.input.cfacts.rand64; omega

theorem ne_of_eval {s : State} {r : Reg} {n : Nat} (h : s.gpr r = BitVec.ofNat 64 n) (hn : n < 2 ^ 64)
    (he : isa.eval (.zero r) s = some false) : n ≠ 0 := by
  rw [VG.RISCV64.Steps.eval_zero_ofNat s r hn h] at he
  simpa using he

theorem classify_ct [InvLaw] : RelCT isa (Two AfterCT) (classify keyCall) fun _ _ => True := by
  unfold classify
  simp only [seqs]
  refine RelCT.seq (two_post (Ψ := MidCT) ?_ head_ready) ?_
  · change RelCT isa _ (.block ([.shift .sll .d .a0 .a0 32, .shift .srl .d .a0 .a0 32, ldf .t1 2] ++
      [.load .d .t1 .t1 0, ldf .t2 8, .add .t2 .t2 .t1, stf .t2 8])) _
    refine RelCT.block_append (RelCT.seq (two_piece [.s0] ?_ (by taint_decide) head1_ready)
      (two_taint [.s0, .t1] head_pins (by taint_decide)))
    rintro q _ _ ⟨_, _, _, -, -, -, h₁⟩ ⟨_, _, _, -, -, -, h₂⟩ r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact h₁.frame.s0.trans h₂.frame.s0.symm
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.a0, h₂.a0]) ?_ ?_
  · exact two_taint [.s0] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h₁.1.s0.trans h₂.1.s0.symm) (by taint_decide)
  refine RelCT.seq (two_post (two_taint [] no_pins (by taint_decide))
    (Ψ := fun q u => Sub3CT q u ∧ q.status ≠ 0)
    fun q u h => WP.mono (sub3_ready q u h.1) fun v hv => ⟨hv, ne_of_eval h.1.a0 h.1.status_lt h.2⟩) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.1.2.trans h₂.1.2.symm)
    ((exhaustedGen_ct).mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.1.1.1, h₂.1.1.1, hsp⟩) fun _ _ h => h) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.1.1.1.t1, h₂.1.1.1.t1]) ?_ ?_
  · exact two_leaf GenPoint.inputs (fun _ _ h => h.1.1.1.1.any) (fail_ct 3 (by decide))
  · refine (accepted_ct).mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, ?_, ?_, hsp⟩) fun _ _ h => h
    · obtain ⟨⟨⟨hs3, h0⟩, h3⟩, h11⟩ := h₁
      refine ⟨⟨hs3, h0, fun e => ?_⟩, ne_of_eval hs3.1.t1 hs3.1.cand_lt h11⟩
      rw [hs3.2, e] at h3; cases h3
    · obtain ⟨⟨⟨hs3, h0⟩, h3⟩, h11⟩ := h₂
      refine ⟨⟨hs3, h0, fun e => ?_⟩, ne_of_eval hs3.1.t1 hs3.1.cand_lt h11⟩
      rw [hs3.2, e] at h3; cases h3

/-! ## An iteration -/

theorem search_run_post (v : RoundImpl) :
    RelCT isa (Two GenCTL) (searchRun (searchCall v)) (Two AfterCT) :=
  two_post (search_run_ct v) fun _ s ⟨o, st, ha, hl, hw⟩ =>
    WP.mono (search_run v hl) fun _ h => ⟨o, st, s, ha, hl, hw, h⟩

theorem classify_any [InvLaw] (q : GenPoint) (t : State) (h : AfterCT q t) :
    WP isa (classify keyCall) t (GenAny q.inputs) := by
  obtain ⟨o, st, s, -, hl, -, ha⟩ := h
  refine WP.mono (classify_ok (final := (tailOf q.inputs o q.used st).consume q.used []) ⟨hl, [], rfl⟩ ha)
    fun u hc => ?_
  rcases hc with ⟨-, -, -, ⟨st', -, hl', -⟩, -⟩ | ⟨-, hd⟩
  · exact ⟨o, _, st', hl'.toGenFrame⟩
  · exact ⟨o, _, _, hd.1⟩

theorem iteration_ct [InvLaw] (v : RoundImpl) :
    RelCT isa (Two GenCTL) (iteration (searchCall v) keyCall) (fun _ _ => True) := by
  unfold iteration
  simp only [seqs]
  exact RelCT.seq (search_run_post v) (RelCT.seq (two_post classify_ct classify_any)
    (two_map GenPoint.inputs (fun _ _ h => h) (two_taint [.s0] gen_any_pins (by taint_decide))))

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
      Nat.mul_le_mul_right _ (by omega)
    omega
  · have h3 : ¬q.status = 3 := by omega
    simp only [h3, ↓reduceIte] at hlt ⊢
    have hmul : (q.inputs.randLen - (q.used + q.cand) + 1) * 2 ^ 64 ≤ (q.inputs.randLen - q.used) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q : GenPoint, n = q.measure ∧ GenCTL q s ∧ GenCTL q t ∧ s.sp = t.sp

private theorem iteration_pair [InvLaw] (v : RoundImpl) (n : Nat) :
    RelCT isa (LoopPair n) (iteration (searchCall v) keyCall) fun s t =>
      isa.eval (.zero .a6) s = isa.eval (.zero .a6) t ∧
      (isa.eval (.zero .a6) s = some false → True) ∧
      (isa.eval (.zero .a6) s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (q : GenPoint) (s : State) (h : n = q.measure ∧ GenCTL q s) :
      WP isa (iteration (searchCall v) keyCall) s fun t => n = q.measure ∧ GenCTStep q t :=
    WP.mono (gen_ct_step v q s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((iteration_ct v).mono
    (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.2, h₂.2, hsp⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂, hsp⟩ => ⟨q, ⟨hn, h₁⟩, ⟨hn, h₂⟩, hsp⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, ⟨_, h₂⟩, -⟩
  rcases h₁ with ⟨hb, e₁, c₁⟩ | ⟨hb, e₁⟩ <;> rcases h₂ with ⟨hb', e₂, c₂⟩ | ⟨hb', e₂⟩
  · refine ⟨e₁.trans e₂.symm, fun _ => trivial, fun _ => ⟨_, ?_, q.next, rfl, c₁, c₂, ?_⟩⟩
    · rw [hn]; exact next_measure hb c₁
    · obtain ⟨_, _, _, hl₁, _⟩ := c₁
      obtain ⟨_, _, _, hl₂, _⟩ := c₂
      exact hl₁.sp.trans hl₂.sp.symm
  · exact absurd hb hb'
  · exact absurd hb' hb
  · exact ⟨e₁.trans e₂.symm, fun _ => trivial, fun h => by rw [e₁] at h; cases h⟩

theorem gen_loop_ct [InvLaw] (v : RoundImpl) :
    RelCT isa (Two GenCTL) (.loop (iteration (searchCall v) keyCall) (.zero .a6)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht, hsp⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration (searchCall v) keyCall) (c := .zero .a6)
    (Q := fun _ _ => True) LoopPair (iteration_pair v) q.measure
    _ _ _ _ _ _ ⟨q, rfl, hs, ht, hsp⟩ he₁ he₂

/-! ## The key's buffer cleared but `p` -/

theorem clearAround_ct : RelCT isa (Two GenAny) clearAround fun _ _ => True := by
  unfold clearAround
  simp only [seqs]
  refine RelCT.seq (two_post (two_taint [.s0] gen_any_pins (by taint_decide))
    (Ψ := fun p s => ClearCT (p, p.kp, 4 * p.L) s) ?_) ?_
  · intro p s ⟨o, u, st, h⟩
    obtain ⟨hL1, hL2, -⟩ := h.len_valid
    have h4 : BitVec.ofNat 64 p.L <<< 2 = BitVec.ofNat 64 (4 * p.L) := by
      rw [VG.Proof.RsaKeyGen.SearchInit.shl_ofNat _ _ (by omega)]; congr 1; omega
    refine WP.mono (setLow_ok h) fun t ⟨⟨hm, k⟩, hy⟩ => ?_
    obtain ⟨g, w12, w13, -⟩ := store_region h hm k hy (by decide)
    exact ⟨⟨o, u, st, g⟩, w12, w13.trans h4⟩
  refine RelCT.seq (two_post ((clear_ct).mono (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨(a, a.kp, 4 * a.L), h₁, h₂, hsp⟩)
    fun _ _ h => h) (Ψ := GenAny) ?_) ?_
  · intro p s ⟨⟨o, u, st, h⟩, h12, h13⟩
    dsimp only at h h12 h13
    have hn := h.key_nowrap
    obtain ⟨hL1, hL2, -⟩ := h.len_valid
    have hkr := h.key_region
    refine WP.mono (clear_ok h h12 h13 (by rw [hkr]; exact Region.sub_prefix (by omega)) (by omega) (by omega)
      (by omega)) fun t ⟨g, _⟩ => ⟨o, u, st, g⟩
  refine RelCT.seq (two_post (two_taint [.s0] gen_any_pins (by taint_decide))
    (Ψ := fun p s => ClearCT (p, p.slot 5, 4 * p.L) s) ?_) ?_
  · intro p s ⟨o, u, st, h⟩
    obtain ⟨hL1, hL2, -⟩ := h.len_valid
    have h4 : BitVec.ofNat 64 p.L <<< 2 = BitVec.ofNat 64 (4 * p.L) := by
      rw [VG.Proof.RsaKeyGen.SearchInit.shl_ofNat _ _ (by omega)]; congr 1; omega
    have h5 : p.kp + (BitVec.ofNat 64 p.L + BitVec.ofNat 64 p.L <<< 2) = p.slot 5 := by
      rw [h4, VG.Proof.RsaKeyGen.SearchInit.add_ofNat, GenPublic.slot]; congr 2; omega
    refine WP.mono (setHigh_ok h) fun t ⟨⟨hm, k⟩, hy⟩ => ?_
    obtain ⟨g, w12, w13, -⟩ := store_region h hm k hy (by decide)
    exact ⟨⟨o, u, st, g⟩, w12.trans h5, w13.trans h4⟩
  exact (clear_ct).mono (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨(a, a.slot 5, 4 * a.L), h₁, h₂, hsp⟩) fun _ _ h => h

/-! ## Entry and return -/

/-- A run's entry, at the point its loop starts at. -/
def GenStart (q : GenPoint) (s : State) : Prop :=
  GenInput q.inputs s ∧ q.used = 0 ∧ AtPoint q s (genProgress s) ∧ word s.mem q.inputs.stp 24 = q.req

theorem GenStart.input' {q : GenPoint} {s : State} (h : GenStart q s) : GenInput (genOfState s) s :=
  ⟨h.1.1, rfl⟩

theorem GenStart.ofState {q : GenPoint} {s : State} (h : GenStart q s) : genOfState s = q.inputs := h.1.2

/-- The arguments in registers, from the public descriptor. -/
theorem GenStart.regs {q : GenPoint} {s : State} (h : GenStart q s) :
    s.gpr .a0 = q.inputs.kp ∧ s.gpr .a1 = BitVec.ofNat 64 (9 * q.inputs.L) ∧ s.gpr .a2 = q.inputs.up ∧
      s.gpr .a3 = q.inputs.rp ∧ s.gpr .a4 = BitVec.ofNat 64 q.inputs.randLen ∧ s.gpr .a5 = q.inputs.B ∧
      s.gpr .a6 = BitVec.ofNat 64 (q.inputs.Z / 8) ∧ s.gpr .a7 = q.inputs.stp := by
  have h4 : (s.gpr .a1).toNat = 9 * genLen s := h.1.base.2.2.2.2.2.2.2.2.2.1
  rw [← h.ofState]
  refine ⟨rfl, ?_, rfl, rfl, ?_, rfl, ?_, rfl⟩
  · apply BitVec.eq_of_toNat_eq; rw [h4, BitVec.toNat_ofNat]; simp only [genOfState]
    have := (s.gpr .a1).isLt; omega
  · apply BitVec.eq_of_toNat_eq; simp only [genOfState, BitVec.toNat_ofNat]
    have := (s.gpr .a4).isLt; omega
  · apply BitVec.eq_of_toNat_eq; simp only [genOfState, BitVec.toNat_ofNat]
    have := (s.gpr .a6).isLt; omega

def AllocStart (q : GenPoint) (u : State) : Prop := ∃ s, GenStart q s ∧ u = allocd 112 s

theorem alloc_start_pins : Pins AllocStart [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] := by
  rintro q _ _ ⟨a, h₁, rfl⟩ ⟨b, h₂, rfl⟩ r hr
  obtain ⟨a3, a4, a5, a6, a7, a8, a9, a10⟩ := h₁.regs
  obtain ⟨b3, b4, b5, b6, b7, b8, b9, b10⟩ := h₂.regs
  show a.gpr r = b.gpr r
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [a3.trans b3.symm, a4.trans b4.symm, a5.trans b5.symm, a6.trans b6.symm, a7.trans b7.symm,
    a8.trans b8.symm, a9.trans b9.symm, a10.trans b10.symm]

/-- After the entry's block. -/
def Entered (q : GenPoint) (t : State) : Prop :=
  ∃ s, GenStart q s ∧ t.gpr .s0 = (genOfState s).F ∧
    t.mem = writeFrame s.mem (genOfState s).F (entryValues s) ∧
    KeepS entryRegs (allocd 112 s) t ∧ t.syms = s.syms

theorem entry_ready (q : GenPoint) (u : State) (h : AllocStart q u) :
    WP isa (.block (entryHead ++ entryWords)) u (Entered q) := by
  obtain ⟨s, hs, rfl⟩ := h
  exact WP.block_append_iff.mpr (VG.RISCV64.WP.mono_syms (entryHead_ok hs.input') fun u ⟨⟨hx, hmu⟩, ku⟩ hyu =>
    VG.RISCV64.WP.mono_syms (entryWords_ok hs.input' hx hmu ku) fun t ⟨hmt, kt⟩ hyt =>
      ⟨s, hs, (kt.gpr .s0 (by decide)).trans hx, by rw [hmt, hmu, entryValues, writeFrame_append], ku.trans kt,
        hyt.trans hyu⟩)

theorem Entered.start {q : GenPoint} {t : State} (h : Entered q t) :
    ∃ s, GenStart q s ∧ KeepS entryRegs (allocd 112 s) t ∧
      GenFrame (genOfState s) s 0 (genProgress s) (framed .ra t) ∧
      Frame [below s.sp stackUse] s.mem (framed .ra t).mem := by
  obtain ⟨s, hs, hx, hm, k, hy⟩ := h
  obtain ⟨hl, hfb⟩ := gen_start hs.input' hx hm k hy
  exact ⟨s, hs, k, hl, hfb⟩

/-- The loop's start, at the point. -/
theorem framed_ctl {q : GenPoint} {t : State} (h : Entered q t) :
    WP isa clearAround (framed .ra t) (GenCTL q) := by
  obtain ⟨s, hs, -, hl, hfb⟩ := h.start
  have hp := hs.input'
  have hf := hp.cfacts
  have hq := hs.ofState
  refine WP.mono (clearAround_ok hl ?_) fun w ⟨hw, hfw⟩ => ?_
  · intro pB hpB
    simp only [genProgress, keyProgressAt] at hpB
    split at hpB
    · cases hpB
    · cases hpB
      obtain ⟨hL1, -, -⟩ := hf.len
      refine bytes_kept hfb ?_ (by show (genOfState s).L ≤ 2 ^ 64; have := hf.nK; omega)
      have hd := hp.stack_disjoint (r := inKey s) (by simp [inWrites])
      rw [hl.key_region] at hd
      exact hd.sub_right (slot_sub _ (by omega))
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨-, -, -, sT, -⟩ := hst
  have hw24 : word w.mem (genOfState s).stp 24 = word s.mem (genOfState s).stp 24 := by
    have e1 := hfw.readW (r := cS (genOfState s)) (a := off (genOfState s).stp 24) (w := 64)
      (Offset.contains_base _ (by decide) (by have := hf.nT; omega)) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hf.kT.symm
        · exact hl.state_frame.symm) (by decide)
    have e2 := hfb.readW (r := cS (genOfState s)) (a := off (genOfState s).stp 24) (w := 64)
      (Offset.contains_base _ (by decide) (by have := hf.nT; omega)) (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact sT) (by decide)
    exact e1.trans e2
  obtain ⟨-, hu0, ha, hreq⟩ := hs
  refine ⟨s, genProgress s, ha, ?_, ?_⟩
  · rw [hu0, ← hq]; exact hw
  · rw [← hq, hw24, hq]; exact hreq

/-- The frame saving `ra`, around the clearing and the loop. -/
theorem frame_ct [InvLaw] (v : RoundImpl) : RelCT isa (Two Entered) (body (searchCall v) keyCall)
      fun a b => a.sp = b.sp := by
  unfold body
  refine relCT_pushRa (fun _ _ ⟨_, _, _, hsp⟩ => hsp) (fun x y ⟨a, h₁, h₂, _⟩ => ?_) ?_
  · obtain ⟨s₁, hs₁, -, hl₁, hfb₁⟩ := h₁.start
    obtain ⟨s₂, hs₂, -, hl₂, hfb₂⟩ := h₂.start
    obtain ⟨t, s', e, -⟩ := gen_body_ok v hs₁.input' hl₁ hfb₁
    obtain ⟨t', s'', e', -⟩ := gen_body_ok v hs₂.input' hl₂ hfb₂
    exact ⟨⟨t, s', e⟩, ⟨t', s'', e'⟩⟩
  · have hc : RelCT isa (Two fun q x => ∃ t, Entered q t ∧ x = framed .ra t) clearAround (Two GenCTL) :=
      two_post (two_leaf GenPoint.inputs (fun q x ⟨t, ht, e⟩ => by
        subst e
        obtain ⟨s, hs, -, hl, -⟩ := ht.start
        exact ⟨s, 0, genProgress s, by rw [← hs.ofState]; exact hl⟩) clearAround_ct)
        fun q x ⟨t, ht, e⟩ => by subst e; exact framed_ctl ht
    refine (RelCT.seq hc (gen_loop_ct v)).mono ?_ fun _ _ h => h
    rintro _ _ ⟨x, y, ⟨a, h₁, h₂, hsp⟩, rfl, rfl⟩
    exact ⟨a, ⟨x, h₁, rfl⟩, ⟨y, h₂, rfl⟩, by simp only [framed, hsp]⟩

/-- After the frame saving `ra`. -/
def Popped (q : GenPoint) (y : State) : Prop :=
  ∃ (s t' d : State), GenStart q s ∧ GenDone (genOfState s) s (genResult s) d ∧
    y = { d.write .ra (t'.gpr .ra) with sp := t'.sp }

theorem frame_ready [InvLaw] (v : RoundImpl) (q : GenPoint) (t : State) (h : Entered q t) :
    WP isa (body (searchCall v) keyCall) t (Popped q) := by
  obtain ⟨s, hs, k, hl, hfb⟩ := h.start
  exact WP.mono (gen_frame_ok v hs.input' k hl hfb) fun y ⟨d, hd, e⟩ => ⟨s, t, d, hs, hd, e⟩

theorem finish_ct : RelCT isa (Two Popped) (.block finish) fun _ _ => True := by
  unfold finish
  refine two_load (r := .a2) (j := 2) (fun q => q.inputs.F) (fun q => q.inputs.up) (by decide) ?_ (by decide)
    (by taint_decide) (by taint_decide)
  rintro q z ⟨s, t', d, hs, hd, rfl⟩
  have g := hd.1
  rw [hs.ofState] at g
  obtain ⟨-, hin, hal, hv⟩ := g.ldf_facts (j := 2) (v := q.inputs.up) (by simp [GenPublic.headers])
  refine ⟨?_, hin, hal, hv⟩
  show (d.write .ra (t'.gpr .ra)).gpr .s0 = _
  rw [RegUpd.gpr_write, ite_eq_right (by decide)]
  exact g.s0

theorem gen_code_ct [InvLaw] (v : RoundImpl) : RelCT isa (Two GenStart) (genCode v) fun _ _ => True := by
  unfold genCode code
  refine relCT_alloc (R := fun _ _ => True) ?_
  simp only [seqs]
  refine (RelCT.seq (two_piece [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] alloc_start_pins (by taint_decide)
      entry_ready)
    (RelCT.seq (two_post ((frame_ct v).mono (fun _ _ h => h) fun _ _ _ => trivial) (frame_ready v))
      finish_ct)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocd, hsp]⟩

/-! ## The whole controller -/

/-- The point a run's loop starts at. -/
def pointOf (s : State) : GenPoint :=
  ⟨genOfState s, 0, (genProgress s).left, phaseWord (genProgress s).phase, (genProgress s).remaining,
    word s.mem (s.gpr .a7) 24, (genResult s).trace⟩

theorem start_self {s : State} (h : genPre s) : GenStart (pointOf s) s := by
  refine ⟨⟨h, rfl⟩, rfl, ⟨rfl, rfl, rfl, ?_⟩, rfl⟩
  simp only [pointOf, tailOf, List.drop_zero]
  rfl

/-- Byte `j < 8` of the doubleword at `a`. -/
theorem byte_of_readW (m : Mem) (a : Addr) {j : Nat} (hj : j < 8) :
    m (a + BitVec.ofNat 64 j) = (m.readW a 64).extractLsb' (8 * j) 8 := by
  rw [← Mem.extractLsb'_read m a (n := 8) hj]
  simp only [Mem.readW]
  rfl

theorem bytes_of_readW {m₁ m₂ : Mem} {a₁ a₂ : Addr} (h : m₁.readW a₁ 64 = m₂.readW a₂ 64) :
    Spec.Rsa.bytesAt m₁ a₁ 8 = Spec.Rsa.bytesAt m₂ a₂ 8 := by
  simp only [Spec.Rsa.bytesAt]
  refine List.ext_getElem (by simp) fun i h₁ _ => ?_
  have hi : i < 8 := by simpa using h₁
  simp only [List.getElem_map, List.getElem_range]
  rw [byte_of_readW m₁ a₁ hi, byte_of_readW m₂ a₂ hi, h]

theorem start_other {s t : State} (ht : genPre t) (hp : genPub s t) : GenStart (pointOf s) t := by
  obtain ⟨hsp, r3, -, r5, r6, r7, r8, r9, r10, hw, -, -, -, htr, hsy⟩ := hp
  simp only [Spec.Rsa.wordsAt, show List.range 7 = [0, 1, 2, 3, 4, 5, 6] from rfl, List.map_cons, List.map_nil,
    List.cons.injEq, and_true, Nat.reduceMul] at hw
  obtain ⟨w0, w1, -, w3, w4, w5, w6⟩ := hw
  rw [BitVec.add_zero, BitVec.add_zero] at w0
  have hd : genOfState t = genOfState s := by
    have hL : genLen t = genLen s := by
      show (t.mem.readW (t.gpr .a7 + 8) 64).toNat = (s.mem.readW (s.gpr .a7 + 8) 64).toNat
      exact congrArg BitVec.toNat w1.symm
    have he : genE t = genE s := (bytes_of_readW w6).symm
    simp only [genOfState, hL, he, ← r3, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10, ← hsp, ← hsy]
  have hprog : (genProgress t).left = (genProgress s).left ∧
      phaseWord (genProgress t).phase = phaseWord (genProgress s).phase ∧
      (genProgress t).remaining = (genProgress s).remaining := by
    refine ⟨?_, ?_, ?_⟩
    · show (t.mem.readW (t.gpr .a7 + BitVec.ofNat 64 40) 64).toNat =
        (s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 40) 64).toNat
      rw [w5]
    · show phaseWord (if (t.mem.readW (t.gpr .a7 + BitVec.ofNat 64 32) 64).toNat = 0 then .p else .q _) =
        phaseWord (if (s.mem.readW (s.gpr .a7 + BitVec.ofNat 64 32) 64).toNat = 0 then .p else .q _)
      rw [w4]
      split <;> rfl
    · show (t.mem.readW (t.gpr .a7) 64).toNat = (s.mem.readW (s.gpr .a7) 64).toNat
      rw [w0]
  refine ⟨⟨ht, hd⟩, rfl, ⟨hprog.1, hprog.2.1, hprog.2.2, ?_⟩, ?_⟩
  · show (tailOf (genOfState s) t 0 (genProgress t)).trace = (genResult s).trace
    rw [← hd, htr]
    simp only [tailOf, List.drop_zero]
    rfl
  · show word t.mem (genOfState s).stp 24 = word s.mem (s.gpr .a7) 24
    rw [← hd]
    exact w3.symm

theorem gen_constantTime [InvLaw] (v : RoundImpl) :
    ConstantTime isa genContract.pre genContract.pub (genCode v) := by
  refine RelCT.constantTime ((gen_code_ct v).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨pointOf s, start_self hs, start_other ht hp, hp.1⟩

end VG.Proof.RsaKeyGen.RISCV64.Generate
