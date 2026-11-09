module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Generate.Correct
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Generate.Implies
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Verified
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Verified
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.CT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTFrames
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.CTLeaf
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Loop
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.CTStep
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.EntropyRequest
import VerifiedGarbage.Spec.RsaKeyGen.GenerationAgrees
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.CTLeaf
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Frame
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Loop
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.CTStep
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Spec.RsaKeyGen.Contract
meta import VerifiedGarbage.Proof.RsaKeyGen.Contract
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.CT
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTFrames
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.EntropyRequest
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Generate.Correct
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Generate.Implies

/-! # The controller's timing, and the verified key search (ARMv7)

Two runs of the loop at one point, the calls' and the blocks' timing, the
whole controller's, and `Verified`.
-/

@[expose] public section

/-! ## Where two runs of the loop are (ARMv7)

As on AArch64 (`Proof/RsaKeyGen/AArch64/Generate/CTPoint.lean`): two runs at
the same point (`GenCTL`) agree on the public data, the octets consumed, the
progress' public words (the generations left, the phase's word and the
counted candidates left), the state's request word and the trace still to
come, which each run's own key search from there gives. The trace's first
entry is the prime search's status, consumption, octets left and trace,
and, after `q`'s, the key's status: what each step does follows from it.
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Impl.RsaKeyGen.Arm.Generate
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

/-- A run's progress `st` from `o`, at the point. -/
def AtPoint (q : GenPoint) (o : State) (st : KeyProgress) : Prop :=
  st.left = q.left ∧ phaseWord st.phase = q.ph ∧ st.remaining = q.remaining ∧
    (tailOf q.inputs o q.used st).trace = q.trace

/-- A loop state at the point. -/
def GenCTL (q : GenPoint) (s : State) : Prop :=
  ∃ o st, AtPoint q o st ∧ GenLive q.inputs o q.used st s ∧ s.mem.readW (off q.inputs.st 24) 64 = q.req

abbrev GenPoint.status (q : GenPoint) : Nat := traceStatus q.trace
abbrev GenPoint.cand (q : GenPoint) : Nat := traceUsed q.trace
abbrev GenPoint.key (q : GenPoint) : Nat := traceKey q.trace

/-- Whether the key search goes on past the point's step. -/
def GenPoint.continues (q : GenPoint) : Prop :=
  (q.status = 3 ∧ ¬q.left < 2) ∨ (q.status = 1 ∧ q.cand ≠ 0 ∧ (q.ph = 0 ∨ q.key = 2))

instance (q : GenPoint) : Decidable q.continues := by unfold GenPoint.continues; infer_instance

/-- The point past the step, when the key search goes on. -/
def GenPoint.next (q : GenPoint) : GenPoint :=
  ⟨q.inputs, q.used + q.cand, if q.status = 3 then q.left - 1 else q.left,
    if q.status = 1 ∧ q.ph = 0 then 1 else 0, limitOf q.inputs.L q.inputs.eB, BitVec.ofNat 64 0,
    q.trace.drop (traceEntry q.trace + if q.status = 1 ∧ q.ph ≠ 0 then 2 else 0)⟩

section

variable {q : GenPoint} {o s : State} {st : KeyProgress}

theorem AtPoint.entry (h : AtPoint q o st) :
    ∃ rest, q.trace = primeEntry (rOf q.inputs o q.used st) ++ rest := by
  obtain ⟨rest, hr⟩ := keySearch_trace (L := q.inputs.L) (eB := q.inputs.eB) st ((genRand o).drop q.used)
  exact ⟨rest, h.2.2.2.symm.trans hr⟩

theorem AtPoint.status (h : AtPoint q o st) : (rOf q.inputs o q.used st).status = q.status := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [GenPoint.status, hr, (primeEntry_facts _ rest).1]

theorem AtPoint.cand (h : AtPoint q o st) : (rOf q.inputs o q.used st).used = q.cand := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [GenPoint.cand, hr, (primeEntry_facts _ rest).2.1]

theorem AtPoint.available (h : AtPoint q o st) :
    (rOf q.inputs o q.used st).available = traceAvailable q.trace := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [hr, (primeEntry_facts _ rest).2.2.1]

theorem AtPoint.prime (h : AtPoint q o st) : (rOf q.inputs o q.used st).trace = tracePrime q.trace := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [hr, (primeEntry_facts _ rest).2.2.2.1]

theorem AtPoint.entryLen (h : AtPoint q o st) :
    (primeEntry (rOf q.inputs o q.used st)).length = traceEntry q.trace := by
  obtain ⟨rest, hr⟩ := h.entry
  rw [hr, (primeEntry_facts _ rest).2.2.2.2]

/-- After `q`'s search accepted a prime, the key's status. -/
theorem AtPoint.keyStatus (h : AtPoint q o st)
    (hle : q.used + (rOf q.inputs o q.used st).used ≤ q.inputs.randLen)
    (hrl : (genRand o).length = q.inputs.randLen) {c : Nat}
    {pB : List Byte} (ho : (rOf q.inputs o q.used st).outcome = .accepted c)
    (hpos : 0 < (rOf q.inputs o q.used st).used) (hph : st.phase = .q pB) :
    keyResultStatus (keyFromPrimes (16 * q.inputs.L) (Spec.Rsa.os2ip q.inputs.eB) (Spec.Rsa.os2ip pB)
      (Spec.Rsa.os2ip (Spec.Rsa.i2osp c q.inputs.L))) = q.key := by
  have hrest : (rOf q.inputs o q.used st).used ≤ ((genRand o).drop q.used).length := by
    rw [List.length_drop, hrl]; omega
  obtain ⟨rest, hr⟩ := keySearch_trace_key (L := q.inputs.L) (eB := q.inputs.eB) ho (drop_lt hpos hrest) hph
  rw [GenPoint.key, ← h.2.2.2, tailOf, hr, primeEntry_key]

theorem keyResultStatus_two (k : Except Failure Key ⊕ Unit) : keyResultStatus k = 2 ↔ k = .inr () := by
  rcases k with (k | k) | ⟨⟩ <;> simp [keyResultStatus]

theorem continues_iff (h : AtPoint q o st) (hl : GenFrame q.inputs o q.used st s) :
    ContSpec q.inputs o q.used st ↔ q.continues := by
  have hs := h.status
  have hc := h.cand
  have hleft := h.1
  have hph := h.2.1
  unfold ContSpec GenPoint.continues
  rw [← hs, ← hc, ← hleft, ← hph]
  cases ho : (rOf q.inputs o q.used st).outcome with
  | entropy k a => simp [rOf_status, ho, Spec.Entropy.Outcome.status]
  | exhausted => simp [rOf_status, ho, Spec.Entropy.Outcome.status]
  | accepted c =>
    have hs1 : (rOf q.inputs o q.used st).status = 1 := by rw [rOf_status, ho]; rfl
    rw [hs1]
    by_cases h0 : (rOf q.inputs o q.used st).used = 0
    · simp [h0]
    · cases hp : st.phase with
      | p => simp [h0, phaseWord]
      | q pB =>
        have hk := h.keyStatus hl.rOf_used_le hl.genRand_length ho (by omega) hp
        rw [← hk]
        simp [h0, phaseWord, keyResultStatus_two]

end

/-- After an iteration: the next point and the loop's condition, or its end. -/
def GenCTStep (q : GenPoint) (t : State) : Prop :=
  (q.continues ∧ isa.eval .eq t = some true ∧ GenCTL q.next t) ∨
    (¬q.continues ∧ isa.eval .eq t = some false ∧ ∃ o final, GenDone q.inputs o final t)

theorem next_point {q : GenPoint} {o t : State} {st : KeyProgress} {final : KeySearchResult}
    (h : AtPoint q o st) (hc : ContPost q.inputs o final q.used st t) : GenCTL q.next t := by
  obtain ⟨st', e, ⟨hlive, -⟩, -, hreq, hrem, htail, hnext⟩ := hc
  have hs := h.status
  have hcd := h.cand
  obtain ⟨hleft, hph, -, htr⟩ := h
  refine ⟨o, st', ⟨?_, ?_, ?_, ?_⟩, by rw [GenPoint.next, ← hcd]; exact hlive, hreq⟩
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

theorem gen_ct_step (sname : String) (c : Search.Cand) (name : String) {kc : Prog isa}
    (hv : Verified target kc (Proof.RsaKeyGen.keyContract abi 56)) (hks : FrameStack.armStack kc ≤ 56)
    (q : GenPoint) (s : State) (h : GenCTL q s) :
    WP isa (iteration (.call sname (Impl.RsaKeyGen.Arm.Search.code c.call)) (.call name kc)) s (GenCTStep q) := by
  obtain ⟨o, st, ha, hl, -⟩ := h
  have hi : GenIter q.inputs o ((tailOf q.inputs o q.used st).consume q.used []) q.used st s := ⟨hl, [], rfl⟩
  unfold iteration
  refine WP.seq (WP.mono (hl.toGenFrame.search_run sname c hl.key.other) fun t hs => ?_)
  refine WP.seq (WP.mono (classify_ok name hv hks hi hs) fun u hc => ?_)
  rcases hc with ⟨hcs, hct⟩ | ⟨hcs, hd⟩
  · have hn := next_point ha hct
    obtain ⟨o', st', ha', hl', hr'⟩ := hn
    refine WP.mono (Search.cmp_ok (c := 4) (n := 4) hl'.r11 (by decide) (by decide)) fun x ⟨⟨hx, hmem⟩, k⟩ =>
      .inl ⟨(continues_iff ha hl.toGenFrame).mp hcs, hx, o', st', ha', ?_, by rw [hmem]; exact hr'⟩
    exact ⟨hl'.toGenFrame.keep k hmem, (k.gpr .r11 (by decide)).trans hl'.r11, by rw [hmem]; exact hl'.key.low,
      by rw [hmem]; exact hl'.key.high, fun pB h => by rw [hmem]; exact hl'.key.other pB h⟩
  · have hlt := keyStatus_lt' ((tailOf q.inputs o q.used st).consume q.used [])
    refine WP.mono (Search.cmp_ok (c := 4) hd.2.1 (by omega) (by decide)) fun x ⟨⟨hx, hmem⟩, k⟩ =>
      .inr ⟨fun h => hcs ((continues_iff ha hl.toGenFrame).mpr h), by rw [hx, decide_eq_false (by omega)],
        o, _, hd.keep k hmem⟩

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## The calls' timing (ARMv7)

The taint analysis tracks registers only: the controller's registers
`r4`–`r10` are the public data's in every state (`regsOf`), so code whose
addresses are among them is checked with them public. The prime search's
and the key's arguments are the same in two runs at a point, and so is what
their contracts let their timing depend on: the search's status,
consumption, request and trace, and the key's status, all from the point's
trace.
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.Ffdh.Arm.KeySearch (Two Pins two_taint two_post two_piece two_ite two_map alloc_ct)
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Proof.RsaKeyGen.Arm (slot writeSlots slotValue)
open VG.Impl.RsaKeyGen.Arm.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-! ## The controller's registers -/

/-- The controller's registers but `r8` and `r11`, for the public data `p`. -/
def regsOf (p : GenPublic) (s : State) : Prop :=
  s.gpr .r4 = p.kp ∧ s.gpr .r5 = BitVec.ofNat 32 p.L ∧ s.gpr .r6 = p.up ∧ s.gpr .r7 = p.rp ∧
    s.gpr .r9 = p.stp ∧ s.gpr .r10 = BitVec.ofNat 32 (limitOf p.L p.eB)

theorem GenFrame.regsOf {p : GenPublic} {o s : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p o used st s) : regsOf p s := ⟨h.r4, h.r5, h.r6, h.r7, h.r9, h.r10⟩

abbrev pubRegs : List Reg := [.r4, .r5, .r6, .r7, .r9, .r10]

theorem regs_pins {α : Type} {Φ : α → State → Prop} (f : α → GenPublic) (hΦ : ∀ a s, Φ a s → regsOf (f a) s) :
    Pins Φ pubRegs := by
  intro a s t h₁ h₂ r hr
  obtain ⟨a4, a5, a6, a7, a9, a10⟩ := hΦ a s h₁
  obtain ⟨b4, b5, b6, b7, b9, b10⟩ := hΦ a t h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [a4.trans b4.symm, a5.trans b5.symm, a6.trans b6.symm, a7.trans b7.symm, a9.trans b9.symm,
    a10.trans b10.symm]

/-- Code the taint analysis checks with the controller's registers public. -/
theorem regs_ct {α : Type} {Φ : α → State → Prop} {c : Prog isa} (f : α → GenPublic)
    (hΦ : ∀ a s, Φ a s → regsOf (f a) s) {hc : VG.Taint.Hint VG.Arm.Taint.T}
    (h : (taint.check (Taint.ofRegs pubRegs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_taint pubRegs (regs_pins f hΦ) h

/-- As `regs_ct`, with `lr` public too. -/
theorem regs_lr_ct {α : Type} {Φ : α → State → Prop} {c : Prog isa} (f : α → GenPublic) (g : α → BitVec 32)
    (hΦ : ∀ a s, Φ a s → regsOf (f a) s ∧ s.gpr .lr = g a) {hc : VG.Taint.Hint VG.Arm.Taint.T}
    (h : (taint.check (Taint.ofRegs (.lr :: pubRegs)) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True := by
  refine two_taint (.lr :: pubRegs) ?_ h
  intro a s t h₁ h₂ r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact (hΦ a s h₁).2.trans (hΦ a t h₂).2.symm
  · exact regs_pins f (fun a s h => (hΦ a s h).1) a s t h₁ h₂ r hr

theorem regs_allocated {p : GenPublic} {s : State} (h : regsOf p s) (n : Nat) : regsOf p (allocated n s) := h

theorem outOf_ph {p : GenPublic} {st₁ st₂ : KeyProgress} (h : phaseWord st₁.phase = phaseWord st₂.phase) :
    outOf p st₁ = outOf p st₂ := by
  unfold outOf; rw [h]

theorem plenOf_ph {p : GenPublic} {st₁ st₂ : KeyProgress} (h : phaseWord st₁.phase = phaseWord st₂.phase) :
    plenOf p st₁ = plenOf p st₂ := by
  unfold plenOf; rw [h]

theorem sReads_ph {p : GenPublic} {used : Nat} {st₁ st₂ : KeyProgress}
    (h : phaseWord st₁.phase = phaseWord st₂.phase) : sReads p used st₁ = sReads p used st₂ := by
  unfold sReads rP; rw [plenOf_ph h]

theorem sWrites_ph {p : GenPublic} {st₁ st₂ : KeyProgress}
    (h : phaseWord st₁.phase = phaseWord st₂.phase) : sWrites p st₁ = sWrites p st₂ := by
  unfold sWrites rO; rw [outOf_ph h]

/-! ## The prime search -/

/-- The search's entry, before the call. -/
def CallSCT (q : GenPoint) (u : State) : Prop :=
  ∃ o st s, AtPoint q o st ∧ GenLive q.inputs o q.used st s ∧
    s.mem.readW (off q.inputs.st 24) 64 = q.req ∧ GenFrame.SearchReady q.inputs o s q.used st u

theorem callS_words {p : GenPublic} {o s u : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p o used st s) (hr : GenFrame.SearchReady p o s used st u) :
    Spec.Rsa.wordsAt (callS p used st u).mem (State.addr (stackArg (callS p used st u) 7)) 4 =
      [BitVec.ofNat 64 st.remaining, BitVec.ofNat 64 p.L, BitVec.ofNat 64 (primeEntropy p.L),
        s.mem.readW (off p.st 24) 64] := by
  rw [h.sa7 hr]
  simp only [Spec.Rsa.wordsAt, show List.range 4 = [0, 1, 2, 3] from rfl, List.map_cons, List.map_nil,
    Nat.reduceMul, State.withRegions_mem, State.callEntry_mem]
  have w (d : Nat) (hd : d + 8 ≤ 56) := h.state_word hr (d := d) hd
  simp only [off] at w
  rw [w 0 (by decide), w 8 (by decide), w 16 (by decide), w 24 (by decide)]
  have h0 := h.state.remaining
  have h1 := h.state.len
  have h2 := h.state.cap
  simp only [off] at h0 h1 h2
  rw [h0, h1, h2]

theorem search_call_ct (name : String) (c : Search.Cand) :
    RelCT isa (Two CallSCT) (.call name (Impl.RsaKeyGen.Arm.Search.code c.call)) (fun _ _ => True) := by
  intro u₁ u₂ t₁ t₂ v₁ v₂ ⟨q, h₁, h₂, hsp⟩ e₁ e₂
  obtain ⟨o₀, st₀, s₀, a₀, -, -, -⟩ := id h₁
  have ct : RelCT isa (fun a b => CallSCT q a ∧ CallSCT q b ∧ a.sp = b.sp)
      (.call name (Impl.RsaKeyGen.Arm.Search.code c.call)) (fun _ _ => True) := by
    refine VG.Arm.RelCT.call (Search.search_correct c) (Search.search_constantTime c)
      (sReads q.inputs q.used st₀) (sWrites q.inputs st₀) ?_
    rintro a b ⟨⟨o₁, st₁, s₁, a₁, l₁, w₁, r₁⟩, ⟨o₂, st₂, s₂, a₂, l₂, w₂, r₂⟩, sp⟩
    have p₁ : phaseWord st₁.phase = phaseWord st₀.phase := a₁.2.1.trans a₀.2.1.symm
    have p₂ : phaseWord st₂.phase = phaseWord st₀.phase := a₂.2.1.trans a₀.2.1.symm
    have g₁ := l₁.toGenFrame
    have g₂ := l₂.toGenFrame
    rw [← sReads_ph p₁, ← sWrites_ph p₁]
    have pre₁ := g₁.callS_pre r₁
    have cov₁ := g₁.search_covers r₁
    have p₁₂ := p₁.trans p₂.symm
    refine ⟨pre₁, ?_, ?_, cov₁.1, cov₁.2,
      by rw [sReads_ph p₁₂, sWrites_ph p₁₂]; exact (g₂.search_covers r₂).1,
      by rw [sWrites_ph p₁₂]; exact (g₂.search_covers r₂).2⟩
    · rw [sReads_ph p₁₂, sWrites_ph p₁₂]; exact g₂.callS_pre r₂
    have hres₁ := g₁.callS_result r₁ l₁.key.other
    have hres₂ := g₂.callS_result r₂ l₂.key.other
    have hb := (show callS q.inputs q.used st₁ b = callS q.inputs q.used st₂ b by
      simp only [callS, sReads_ph p₁₂, sWrites_ph p₁₂])
    change Search.searchPub (callS q.inputs q.used st₁ a) (callS q.inputs q.used st₁ b)
    rw [hb]
    obtain ⟨d0, d1, d2, d3⟩ := r₁.regs
    obtain ⟨f0, f1, f2, f3⟩ := r₂.regs
    refine ⟨by simp only [State.withRegions_sp, State.callEntry_sp, sp], ?_, ?_, ?_, ?_, fun j hj => ?_,
      (g₁.callS_e r₁).trans (g₂.callS_e r₂).symm, ?_, ?_, ?_, ?_, ?_⟩
    · rw [callS_gpr (by decide), callS_gpr (by decide), d0, f0, outOf_ph p₁₂]
    · rw [callS_gpr (by decide), callS_gpr (by decide), d1, f1]
    · rw [callS_gpr (by decide), callS_gpr (by decide), d2, f2]
    · rw [callS_gpr (by decide), callS_gpr (by decide), d3, f3]
    · rw [g₁.stArg r₁ hj, g₂.stArg r₂ hj]
      unfold callArgs
      rw [plenOf_ph p₁₂]
      match j, hj with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
      | 3, _ => rfl
      | 4, _ => rfl
      | 5, _ => rfl
      | 6, _ => rfl
      | 7, _ => rfl
    · rw [callS_words g₁ r₁, callS_words g₂ r₂, a₁.2.2.1, a₂.2.2.1, w₁, w₂]
    · rw [hres₁, hres₂, a₁.status, a₂.status]
    · rw [hres₁, hres₂, a₁.cand, a₂.cand]
    · rw [g₁.callS_len r₁, g₂.callS_len r₂, hres₁, hres₂]
      exact Entropy.requested_congr (a₁.status.trans a₂.status.symm) (a₁.available.trans a₂.available.symm)
    · rw [hres₁, hres₂, a₁.prime, a₂.prime]
  exact ct _ _ _ _ _ _ ⟨h₁, h₂, hsp⟩ e₁ e₂

/-- A loop state at the point, past the allocation of the search's frame. -/
def AllocSCT (q : GenPoint) (u : State) : Prop := ∃ s, GenCTL q s ∧ u = allocated 32 s

/-- Past the frame's base in `lr`. -/
def LrSCT (q : GenPoint) (u : State) : Prop := regsOf q.inputs u ∧ u.gpr .lr = q.inputs.S2

theorem search_run_ct (name : String) (c : Search.Cand) :
    RelCT isa (Two GenCTL) (searchRun (.call name (Impl.RsaKeyGen.Arm.Search.code c.call))) (fun _ _ => True) := by
  unfold searchRun
  refine alloc_ct (R := fun _ _ => True) ?_
  have hb : RelCT isa (Two AllocSCT) (.block searchArgs) fun _ _ => True := by
    unfold searchArgs
    rw [show ∀ (i : Instr) (l : List Instr), i :: l = [i] ++ l from fun _ _ => rfl]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := LrSCT) [] (fun _ _ _ _ _ _ h => nomatch h)
      (by taint_decide) fun q u ⟨s, ⟨_, _, _, hl, _⟩, e⟩ => ?_) (regs_lr_ct (fun q => q.inputs) (fun q => q.inputs.S2)
        (fun q u h => h) (by taint_decide)))
    subst e
    have hsp := hl.toGenFrame.alloc_sp
    refine WP.mono (withRest_all [.lr] (c := .block [.addSp .lr 0]) (Q := fun t => t.gpr .lr = q.inputs.S2)
      (by ffrun [hsp, BitVec.add_zero]) (by rfl) (by rfl)) fun t ⟨hlr, k⟩ => ⟨?_, hlr⟩
    obtain ⟨a4, a5, a6, a7, a9, a10⟩ := regs_allocated hl.toGenFrame.regsOf 32
    exact ⟨(k.gpr _ (by decide)).trans a4, (k.gpr _ (by decide)).trans a5, (k.gpr _ (by decide)).trans a6,
      (k.gpr _ (by decide)).trans a7, (k.gpr _ (by decide)).trans a9, (k.gpr _ (by decide)).trans a10⟩
  have ha : RelCT isa (Two AllocSCT) (.block searchArgs) (Two CallSCT) :=
    two_post hb
      fun q u ⟨s, ⟨o, st, ha, hl, hw⟩, e⟩ => by
        subst e
        exact WP.mono hl.toGenFrame.searchArgs_ok fun _ ⟨hr, _⟩ => ⟨o, st, s, ha, hl, hw, hr⟩
  refine (RelCT.seq ha (search_call_ct name c)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocated, hsp]⟩

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## The key's call is constant time (ARMv7)

At a point after `q`'s search accepted a prime, both runs call the key with
the same arguments and the same `e`, and the key's status is the point's.
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.Ffdh.Arm.KeySearch (Two Pins two_taint two_post two_piece two_ite two_map alloc_ct)
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

theorem keyStatus_keyOp (L : Nat) (eB pB qB : List Byte) :
    keyStatus (keyOp L eB pB qB) = keyResultStatus (keyFromPrimes (16 * L) (Spec.Rsa.os2ip eB)
      (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip qB)) := by
  unfold keyOp
  split <;> rename_i h <;> rw [h] <;> rfl

/-- The key's inputs at its entry: `e`, and `p` and `q` from the key's buffer. -/
theorem callK_inputs {p : GenPublic} {o s u : State} {used : Nat} {st : KeyProgress} (h : GenFrame p o used st s)
    (hr : KeyReady p o s u) :
    (stackArg (callK p u) 1).toNat = p.L ∧
    Spec.Rsa.bytesAt u.mem (BitVec.setWidth 64 (stackArg (callK p u) 10)) (stackArg (callK p u) 11).toNat = p.eB ∧
    Spec.Rsa.bytesAt u.mem (BitVec.setWidth 64 (stackArg (callK p u) 0)) p.L =
      Spec.Rsa.bytesAt s.mem (p.slot 4) p.L ∧
    Spec.Rsa.bytesAt u.mem (BitVec.setWidth 64 (stackArg (callK p u) 2)) p.L =
      Spec.Rsa.bytesAt s.mem (p.slot 5) p.L := by
  have hL := h.L_le
  have a0 : stackArg (callK p u) 0 = p.kp + BitVec.ofNat 32 (4 * p.L) := h.kArg hr (by decide)
  have a1 : stackArg (callK p u) 1 = BitVec.ofNat 32 p.L := h.kArg hr (by decide)
  have a2 : stackArg (callK p u) 2 = p.kp + BitVec.ofNat 32 (5 * p.L) := h.kArg hr (by decide)
  have a10 : stackArg (callK p u) 10 = p.stp + BitVec.ofNat 32 48 := h.kArg hr (by decide)
  have a11 : stackArg (callK p u) 11 = BitVec.ofNat 32 8 := h.kArg hr (by decide)
  have fa := h.frame_kargs hr
  have hst := h.input.cfacts.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, -, sT, -, -⟩ := hst
  have kb (j : Nat) (hj : j * p.L + p.L ≤ 9 * p.L) :
      Spec.Rsa.bytesAt u.mem (p.slot j) p.L = Spec.Rsa.bytesAt s.mem (p.slot j) p.L :=
    bytes_kept fa (fun r hr' => by
      obtain rfl := List.mem_singleton.mp hr'
      exact (sK.sub_left h.a3Stack).symm.sub_left (GenFrame.kSubK hj)) (by omega)
  refine ⟨by rw [a1, h.tL], ?_, ?_, ?_⟩
  · rw [a10, a11, show (BitVec.ofNat 32 8).toNat = 8 from rfl,
      show BitVec.setWidth 64 (p.stp + BitVec.ofNat 32 48) = off p.st 48 from congrArg Region.base h.eE,
      bytes_kept fa (fun r hr' => by
        obtain rfl := List.mem_singleton.mp hr'
        exact (sT.sub_left h.a3Stack).symm.sub_left (Offset.sub_base _ (by decide))) (by decide)]
    exact h.state.e
  · rw [a0, show BitVec.setWidth 64 (p.kp + BitVec.ofNat 32 (4 * p.L)) = p.slot 4 from kAddr h (by omega), kb 4 (by omega)]
  · rw [a2, show BitVec.setWidth 64 (p.kp + BitVec.ofNat 32 (5 * p.L)) = p.slot 5 from kAddr h (by omega), kb 5 (by omega)]

/-- After `q`'s search accepted a prime, at the point: the key's state. -/
def KeyCT (q : GenPoint) (u : State) : Prop :=
  ∃ o st final c pB, AtPoint q o st ∧ Mid q.inputs o final q.used st u ∧
    (rOf q.inputs o q.used st).outcome = .accepted c ∧ 0 < (rOf q.inputs o q.used st).used ∧ st.phase = .q pB

/-- The key's status, from the point. -/
theorem KeyCT.status {q : GenPoint} {u : State} (h : KeyCT q u) : keyStatus (keyOf q.inputs u.mem) = q.key := by
  obtain ⟨o, st, final, c, pB, ha, hm, ho, hpos, hph⟩ := h
  have hs4 := hm.slot4
  have hs5 := hm.slot5
  rw [hph] at hs4 hs5
  simp only [outBytes, ho] at hs5
  simp only [keyOf, hs4, hs5, keyStatus_keyOp]
  exact ha.keyStatus hm.frame.used_le hm.frame.genRand_length ho hpos hph

/-- The key's entry, before the call. -/
def CallKCT (q : GenPoint) (u : State) : Prop :=
  ∃ o st final c pB s, AtPoint q o st ∧ Mid q.inputs o final q.used st s ∧
    (rOf q.inputs o q.used st).outcome = .accepted c ∧ 0 < (rOf q.inputs o q.used st).used ∧
    st.phase = .q pB ∧ KeyReady q.inputs o s u

theorem key_call_ct (name : String) {kc : Prog isa}
    (hv : Verified target kc (Proof.RsaKeyGen.keyContract abi 56)) :
    RelCT isa (Two CallKCT) (.call name kc) (fun _ _ => True) := by
  intro u₁ u₂ t₁ t₂ v₁ v₂ ⟨q, h₁, h₂, hsp⟩ e₁ e₂
  have ct : RelCT isa (fun a b => CallKCT q a ∧ CallKCT q b ∧ a.sp = b.sp) (.call name kc) (fun _ _ => True) := by
    refine VG.Arm.RelCT.call hv.1 hv.2.1 (kRd q.inputs) (kWr q.inputs) ?_
    rintro a b ⟨⟨o₁, st₁, f₁, c₁, pB₁, s₁, a₁, m₁, ho₁, hp₁, hph₁, r₁⟩,
      ⟨o₂, st₂, f₂, c₂, pB₂, s₂, a₂, m₂, ho₂, hp₂, hph₂, r₂⟩, sp⟩
    have g₁ := m₁.frame
    have g₂ := m₂.frame
    have k₁ : KeyCT q s₁ := ⟨o₁, st₁, f₁, c₁, pB₁, a₁, m₁, ho₁, hp₁, hph₁⟩
    have k₂ : KeyCT q s₂ := ⟨o₂, st₂, f₂, c₂, pB₂, a₂, m₂, ho₂, hp₂, hph₂⟩
    refine ⟨pre_of_cin (g₁.callK_cin r₁), pre_of_cin (g₂.callK_cin r₂), ?_, (g₁.key_covers r₁).1,
      (g₁.key_covers r₁).2, (g₂.key_covers r₂).1, (g₂.key_covers r₂).2⟩
    sig_pub [Proof.RsaKeyGen.keyContract, Proof.RsaKeyGen.keySig, abi, argRegs, reduceClassify, Loc.val]
    obtain ⟨l₁, e₁, p₁, q₁⟩ := callK_inputs g₁ r₁
    obtain ⟨l₂, e₂, p₂, q₂⟩ := callK_inputs g₂ r₂
    have st₁ := k₁.status
    have st₂ := k₂.status
    have arg (j : Nat) (hj : j < 14) : stackArg (callK q.inputs a) j = stackArg (callK q.inputs b) j := by
      rw [g₁.kArg r₁ hj, g₂.kArg r₂ hj]
      unfold keyVals keyVals1 keyVals2 keyVals3
      match j, hj with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
      | 3, _ => rfl
      | 4, _ => rfl
      | 5, _ => rfl
      | 6, _ => rfl
      | 7, _ => rfl
      | 8, _ => rfl
      | 9, _ => rfl
      | 10, _ => rfl
      | 11, _ => rfl
      | 12, _ => rfl
      | 13, _ => rfl
    refine ⟨sp, ?_, by rw [r₁.r0, r₂.r0], by rw [r₁.r1, r₂.r1], by rw [r₁.r2, r₂.r2], by rw [r₁.r3, r₂.r3], ?_⟩
    · rw [l₁, e₁, p₁, q₁, l₂, e₂, p₂, q₂]
      simp only [keyOf] at st₁ st₂
      rw [st₁, st₂]
    · exact ⟨arg 0 (by decide), arg 1 (by decide), arg 2 (by decide), arg 3 (by decide), arg 4 (by decide),
        arg 5 (by decide), arg 6 (by decide), arg 7 (by decide), arg 8 (by decide), arg 9 (by decide),
        arg 10 (by decide), arg 11 (by decide), arg 12 (by decide), arg 13 (by decide)⟩
  exact ct _ _ _ _ _ _ ⟨h₁, h₂, hsp⟩ e₁ e₂

/-- At the point, past the allocation of the key's frame. -/
def AllocKCT (q : GenPoint) (u : State) : Prop := ∃ s, KeyCT q s ∧ u = allocated 56 s

/-- Past the frame's base in `lr`. -/
def LrKCT (q : GenPoint) (u : State) : Prop := regsOf q.inputs u ∧ u.gpr .lr = q.inputs.S3

theorem KeyCT.regs {q : GenPoint} {u : State} (h : KeyCT q u) : regsOf q.inputs u :=
  let ⟨_, _, _, _, _, _, hm, _⟩ := h; hm.frame.regsOf

theorem key_run_ct (name : String) {kc : Prog isa}
    (hv : Verified target kc (Proof.RsaKeyGen.keyContract abi 56)) :
    RelCT isa (Two KeyCT) (keyRun (.call name kc)) (fun _ _ => True) := by
  unfold keyRun
  refine alloc_ct (R := fun _ _ => True) ?_
  have hb : RelCT isa (Two AllocKCT) (.block keyArgs) fun _ _ => True := by
    unfold keyArgs
    rw [show ∀ (i : Instr) (l : List Instr), i :: l = [i] ++ l from fun _ _ => rfl]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := LrKCT) [] (fun _ _ _ _ _ _ h => nomatch h)
      (by taint_decide) fun q u ⟨s, hk, e⟩ => ?_) (regs_lr_ct (fun q => q.inputs) (fun q => q.inputs.S3)
        (fun q u h => h) (by taint_decide)))
    subst e
    obtain ⟨_, _, _, _, _, _, hm, _⟩ := id hk
    have hsp := hm.frame.alloc56_sp
    refine WP.mono (withRest_all [.lr] (c := .block [.addSp .lr 0]) (Q := fun t => t.gpr .lr = q.inputs.S3)
      (by ffrun [hsp, BitVec.add_zero]) (by rfl) (by rfl)) fun t ⟨hlr, k⟩ => ⟨?_, hlr⟩
    obtain ⟨a4, a5, a6, a7, a9, a10⟩ := regs_allocated hk.regs 56
    exact ⟨(k.gpr _ (by decide)).trans a4, (k.gpr _ (by decide)).trans a5, (k.gpr _ (by decide)).trans a6,
      (k.gpr _ (by decide)).trans a7, (k.gpr _ (by decide)).trans a9, (k.gpr _ (by decide)).trans a10⟩
  have ha : RelCT isa (Two AllocKCT) (.block keyArgs) (Two CallKCT) :=
    two_post hb fun q u ⟨s, hs, e⟩ => by
      subst e
      obtain ⟨o, st, final, c, pB, a, hm, ho, hpos, hph⟩ := id hs
      exact WP.mono hm.frame.keyArgs_ok fun _ ⟨hr, _⟩ => ⟨o, st, final, c, pB, s, a, hm, ho, hpos, hph, hr⟩
  refine (RelCT.seq ha (key_call_ct name hv)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocated, hsp]⟩

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## The outcome's branches are constant time (ARMv7)

Every branch of `classify` and `afterKey` tests what the point fixes: the
search's status and consumption, the generations left, the phase and the
key's status. Every block between them has its addresses among the
controller's public registers.
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.Ffdh.Arm.KeySearch (Two Pins two_taint two_post two_piece two_ite two_map two_mono alloc_ct)
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-- A branch on a fact `F` of the point. -/
theorem fact_ite {Ψ : GenPoint → State → Prop} {F : GenPoint → Prop} [DecidablePred F] {th el : Prog isa}
    {Q : State → State → Prop} (ht : RelCT isa (Two fun q u => Ψ q u ∧ F q) th Q)
    (he : RelCT isa (Two fun q u => Ψ q u ∧ ¬F q) el Q) :
    RelCT isa (Two fun q u => Ψ q u ∧ isa.eval .eq u = some (decide (F q))) (.ite .eq th el) Q :=
  two_ite (fun q s₁ s₂ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (ht.mono (fun _ _ h => two_mono (fun q u ⟨⟨hu, he⟩, ht⟩ => ⟨hu, by
      rw [he] at ht; exact of_decide_eq_true (Option.some.inj ht)⟩) h) fun _ _ h => h)
    (he.mono (fun _ _ h => two_mono (fun q u ⟨⟨hu, he⟩, ht⟩ => ⟨hu, by
      rw [he] at ht; exact of_decide_eq_false (Option.some.inj ht)⟩) h) fun _ _ h => h)

/-- After the search and its head, at the point. -/
def MidCT (q : GenPoint) (u : State) : Prop :=
  ∃ o st final, AtPoint q o st ∧ Mid q.inputs o final q.used st u ∧
    u.gpr .r0 = BitVec.ofNat 32 (rOf q.inputs o q.used st).status ∧
    u.gpr .r12 = BitVec.ofNat 32 (rOf q.inputs o q.used st).used

theorem MidCT.regs {q : GenPoint} {u : State} (h : MidCT q u) : regsOf q.inputs u :=
  let ⟨_, _, _, _, hm, _⟩ := h; hm.frame.regsOf

/-- A state with the controller's registers: what the leaves need. -/
def RegsCT (q : GenPoint) (u : State) : Prop := regsOf q.inputs u

theorem leaf_ct {Φ : GenPoint → State → Prop} {c : Prog isa} (hΦ : ∀ q u, Φ q u → regsOf q.inputs u)
    {hc : VG.Taint.Hint VG.Arm.Taint.T} (h : (taint.check (Taint.ofRegs pubRegs) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  regs_ct (fun q => q.inputs) hΦ h

theorem status_ne {q : GenPoint} {o : State} {st : KeyProgress} (ha : AtPoint q o st) (h0 : ¬q.status = 0)
    (h3 : ¬q.status = 3) : ∃ c, (rOf q.inputs o q.used st).outcome = .accepted c := by
  rcases status_cases (rOf q.inputs o q.used st) with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, c, ho⟩
  · exact absurd (ha.status ▸ e) h0
  · exact absurd (ha.status ▸ e) h3
  · exact ⟨c, ho⟩

/-- After the search and its head, at the point, without its registers. -/
def MidF (q : GenPoint) (u : State) : Prop :=
  ∃ o st final, AtPoint q o st ∧ Mid q.inputs o final q.used st u

theorem MidF.regs {q : GenPoint} {u : State} (h : MidF q u) : regsOf q.inputs u :=
  let ⟨_, _, _, _, hm⟩ := h; hm.frame.regsOf

theorem regs_keep {p : GenPublic} {u t : State} (h : regsOf p u) {ws : List Reg} (k : Rest ws u t)
    (hws : ∀ r ∈ pubRegs, r ∉ ws := by decide) : regsOf p t := by
  obtain ⟨a4, a5, a6, a7, a9, a10⟩ := h
  exact ⟨(k.gpr _ (hws _ (by simp))).trans a4, (k.gpr _ (hws _ (by simp))).trans a5,
    (k.gpr _ (hws _ (by simp))).trans a6, (k.gpr _ (hws _ (by simp))).trans a7,
    (k.gpr _ (hws _ (by simp))).trans a9, (k.gpr _ (hws _ (by simp))).trans a10⟩

/-! ## After the key -/

/-- After the key, at the point. -/
def AfterKCT (q : GenPoint) (v : State) : Prop :=
  regsOf q.inputs v ∧ v.gpr .r0 = BitVec.ofNat 32 q.key ∧ q.key < 4

theorem cmp_key {X : GenPoint → Prop} (k : Nat) (hk : k < 256) {hc : VG.Taint.Hint VG.Arm.Taint.T}
    (ht : (taint.check (Taint.ofRegs pubRegs) (.block [.cmp .r0 (.imm (BitVec.ofNat 32 k))]) hc).isSome = true) :
    RelCT isa (Two fun q u => AfterKCT q u ∧ X q) (.block [.cmp .r0 (.imm (BitVec.ofNat 32 k))])
      (Two fun q u => (AfterKCT q u ∧ X q) ∧ isa.eval .eq u = some (decide (q.key = k))) :=
  two_post (leaf_ct (fun q u h => h.1.1) ht) fun q u ⟨⟨hr, h0, h4⟩, hx⟩ =>
    WP.mono (Search.cmp_ok h0 (by omega) hk) fun t ⟨⟨he, _⟩, kt⟩ =>
      ⟨⟨⟨regs_keep hr kt, (kt.gpr _ (by decide)).trans h0, h4⟩, hx⟩, he⟩

theorem afterKey_ct : RelCT isa (Two AfterKCT) afterKey fun _ _ => True := by
  unfold afterKey
  have h1 := cmp_key (X := fun _ => True) 1 (by decide) (by taint_decide)
  refine RelCT.seq (h1.mono (fun _ _ h => two_mono (fun _ _ h => ⟨h, trivial⟩) h) fun _ _ h => h) ?_
  refine fact_ite (Ψ := fun q u => AfterKCT q u ∧ True) (F := fun q => q.key = 1)
    (leaf_ct (fun q u h => h.1.1.1) (by taint_decide)) ?_
  refine RelCT.seq ((cmp_key (X := fun q => ¬q.key = 1) 2 (by decide) (by taint_decide)).mono
    (fun _ _ h => two_mono (fun _ _ h => ⟨h.1.1, h.2⟩) h) fun _ _ h => h) ?_
  exact fact_ite (Ψ := fun q u => AfterKCT q u ∧ ¬q.key = 1) (F := fun q => q.key = 2)
    (leaf_ct (fun q u h => h.1.1.1) (by taint_decide)) (leaf_ct (fun q u h => h.1.1.1) (by taint_decide))

/-- The key's branch: the key, and its status's. -/
theorem keyBranch_ct (name : String) {kc : Prog isa}
    (hv : Verified target kc (Proof.RsaKeyGen.keyContract abi 56)) (hks : FrameStack.armStack kc ≤ 56) :
    RelCT isa (Two KeyCT) (.seq (keyRun (.call name kc)) afterKey) fun _ _ => True := by
  refine RelCT.seq (two_post (key_run_ct name hv) fun q u hk => ?_) afterKey_ct
  have hst := hk.status
  obtain ⟨o, st, final, c, pB, a, hm, ho, hpos, hph⟩ := hk
  refine WP.mono (hm.frame.key_run name hv hks) fun v hv' => ⟨hv'.frame.regsOf, ?_, ?_⟩
  · rw [← hst, ← hv'.status]; exact (ofNat_toNat32 _).symm
  · rw [← hst]; exact keyStatus_lt _

/-! ## A prime accepted -/

/-- A prime accepted having read some octets, at the point. -/
def AccCT (q : GenPoint) (u : State) : Prop :=
  MidF q u ∧ ¬q.status = 0 ∧ ¬q.status = 3 ∧ ¬q.cand = 0

theorem accepted_ct (name : String) {kc : Prog isa}
    (hv : Verified target kc (Proof.RsaKeyGen.keyContract abi 56)) (hks : FrameStack.armStack kc ≤ 56) :
    RelCT isa (Two AccCT) (accepted (.call name kc)) fun _ _ => True := by
  unfold accepted
  refine RelCT.seq (two_post (Ψ := fun q u => AccCT q u ∧ isa.eval .eq u = some (decide (q.ph = 0)))
    (leaf_ct (fun q u h => h.1.regs) (by taint_decide)) fun q u ⟨⟨o, st, final, a, hm⟩, h0, h3, hc⟩ => ?_) ?_
  · have h := hm.frame
    have hw := h.wr
    have aT : State.addr (q.inputs.stp + BitVec.ofNat 32 32) = off q.inputs.st 32 :=
      VG.Arm.addr_add (by have := h.facts.nT; omega)
    have hp1 := phaseWord_le st.phase
    refine WP.mono (withRest_all [.r12] (c := .block [.ldr .r12 .r9 32, .cmp .r12 (.imm 0)])
      (Q := fun t => isa.eval .eq t = some (decide (phaseWord st.phase = 0)) ∧ t.mem = u.mem) ?_ (by rfl) (by rfl))
      fun t ⟨⟨he, htm⟩, kt⟩ => ⟨⟨⟨o, st, final, a, hm.keep kt htm⟩, h0, h3, hc⟩, by rw [he, a.2.1]⟩
    ffrun [h.r9, aT, h.state_rd hw (u := u) (d := 32) (by decide), low_half h.state.phase]
    exact congrArg some (Search.sub_eq_beq (by omega) (by decide))
  refine fact_ite (Ψ := AccCT) (F := fun q => q.ph = 0) (leaf_ct (fun q u h => h.1.1.regs) (by taint_decide))
    ((keyBranch_ct name hv hks).mono (fun _ _ h => two_mono (fun q u ⟨⟨⟨o, st, final, a, hm⟩, h0, h3, hc⟩, hph⟩ => ?_) h)
      fun _ _ h => h)
  obtain ⟨c, ho⟩ := status_ne a h0 h3
  obtain ⟨pB, hpB⟩ : ∃ pB, st.phase = .q pB := by
    cases e : st.phase with
    | p => have := a.2.1; rw [e] at this; exact absurd this.symm hph
    | q pB => exact ⟨pB, rfl⟩
  exact ⟨o, st, final, c, pB, a, hm, ho, by rw [a.cand]; omega, hpB⟩



end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## The controller's loop is constant time (ARMv7)

An iteration, from two loop states at the same point, has the same trace in
both runs (`iteration_ct`), and both go on to the point past it or stop
(`gen_ct_step`); each point that goes on consumes more of the tape or a
generation, so the loop rule's measure falls.
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.Ffdh.Arm.KeySearch (Two Pins two_taint two_post two_piece two_ite two_map two_mono alloc_ct)
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

theorem exhausted_ct : RelCT isa (Two MidF) exhaustedGen fun _ _ => True := by
  unfold exhaustedGen
  refine RelCT.seq (two_post (Ψ := fun q u => MidF q u ∧ isa.eval .eq u = some (decide (q.left < 2)))
    (leaf_ct (fun q u h => h.regs) (by taint_decide)) fun q u ⟨o, st, final, a, hm⟩ =>
      WP.mono hm.frame.gen_flag fun t ⟨⟨he, htm⟩, kt⟩ => ⟨⟨o, st, final, a, hm.keep kt htm⟩, by rw [he, a.1]⟩) ?_
  exact fact_ite (Ψ := MidF) (F := fun q => q.left < 2) (leaf_ct (fun q u h => h.1.regs) (by taint_decide))
    (leaf_ct (fun q u h => h.1.regs) (by taint_decide))

theorem MidCT.keep {q : GenPoint} {u t : State} (h : MidCT q u) (k : Rest [] u t) (hm : t.mem = u.mem) : MidCT q t :=
  let ⟨o, st, final, a, hmid, h0, h12⟩ := h
  ⟨o, st, final, a, hmid.keep k hm, (k.gpr _ (by decide)).trans h0, (k.gpr _ (by decide)).trans h12⟩

/-- After the search, at the point. -/
def AfterCT (q : GenPoint) (t : State) : Prop :=
  ∃ o st s, AtPoint q o st ∧ GenLive q.inputs o q.used st s ∧ AfterSearch q.inputs o q.used st s t

theorem classify_ct (name : String) {kc : Prog isa}
    (hv : Verified target kc (Proof.RsaKeyGen.keyContract abi 56)) (hks : FrameStack.armStack kc ≤ 56) :
    RelCT isa (Two AfterCT) (Impl.RsaKeyGen.Arm.Generate.classify (.call name kc)) fun _ _ => True := by
  unfold Impl.RsaKeyGen.Arm.Generate.classify
  refine RelCT.seq (two_post (Ψ := fun q u => MidCT q u ∧ isa.eval .eq u = some (decide (q.status = 0)))
    (leaf_ct (fun q u ⟨_, _, _, _, _, ha⟩ => ha.frame.regsOf) (by taint_decide))
    fun q t ⟨o, st, s, a, hl, ha⟩ => ?_) ?_
  · refine WP.mono (GenFrame.after_head (final := (tailOf q.inputs o q.used st).consume q.used []) hl ⟨[], rfl⟩ ha)
      fun u ⟨he, h0, h12, hm⟩ => ⟨⟨o, st, _, a, hm, h0, h12⟩, by rw [he, a.status]⟩
  refine fact_ite (Ψ := MidCT) (F := fun q => q.status = 0) (leaf_ct (fun q u h => h.1.regs) (by taint_decide)) ?_
  refine RelCT.seq (two_post (Ψ := fun q u => (MidCT q u ∧ ¬q.status = 0) ∧
      isa.eval .eq u = some (decide (q.status = 3)))
    (leaf_ct (fun q u h => h.1.regs) (by taint_decide)) fun q u ⟨hmc, hs0⟩ => ?_) ?_
  · obtain ⟨o, st, final, a, hm, h0, h12⟩ := id hmc
    have hs32 : (rOf q.inputs o q.used st).status < 2 ^ 32 := by
      unfold Spec.Entropy.Result.status Spec.Entropy.Outcome.status; split <;> decide
    exact WP.mono (Search.cmp_ok (c := 3) h0 hs32 (by decide)) fun t ⟨⟨he, htm⟩, kt⟩ =>
      ⟨⟨hmc.keep kt htm, hs0⟩, by rw [he, a.status]⟩
  refine fact_ite (Ψ := fun q u => MidCT q u ∧ ¬q.status = 0) (F := fun q => q.status = 3)
    (exhausted_ct.mono (fun _ _ h => two_mono (fun q u ⟨⟨⟨o, st, final, a, hm, _⟩, _⟩, _⟩ => ⟨o, st, final, a, hm⟩) h)
      fun _ _ h => h) ?_
  refine RelCT.seq (two_post (Ψ := fun q u => ((MidCT q u ∧ ¬q.status = 0) ∧ ¬q.status = 3) ∧
      isa.eval .eq u = some (decide (q.cand = 0)))
    (leaf_ct (fun q u h => h.1.1.regs) (by taint_decide)) fun q u ⟨⟨hmc, hs0⟩, hs3⟩ => ?_) ?_
  · obtain ⟨o, st, final, a, hm, h0, h12⟩ := id hmc
    have hu32 : (rOf q.inputs o q.used st).used < 2 ^ 32 := by
      have := hm.used_le; have := hm.frame.randLen_lt; omega
    exact WP.mono (Search.cmp0_ok h12 hu32) fun t ⟨⟨he, htm⟩, kt⟩ =>
      ⟨⟨⟨hmc.keep kt htm, hs0⟩, hs3⟩, by rw [he, a.cand]⟩
  refine fact_ite (Ψ := fun q u => (MidCT q u ∧ ¬q.status = 0) ∧ ¬q.status = 3) (F := fun q => q.cand = 0)
    (leaf_ct (fun q u h => h.1.1.1.regs) (by taint_decide)) ?_
  exact (accepted_ct name hv hks).mono (fun _ _ h => two_mono
    (fun q u ⟨⟨⟨⟨o, st, final, a, hm, _⟩, h0⟩, h3⟩, hc⟩ => ⟨⟨o, st, final, a, hm⟩, h0, h3, hc⟩) h) fun _ _ h => h

theorem iteration_ct (sname : String) (c : Search.Cand) (name : String) {kc : Prog isa}
    (hv : Verified target kc (Proof.RsaKeyGen.keyContract abi 56)) (hks : FrameStack.armStack kc ≤ 56) :
    RelCT isa (Two GenCTL) (iteration (.call sname (Impl.RsaKeyGen.Arm.Search.code c.call)) (.call name kc))
      fun _ _ => True := by
  unfold iteration
  refine RelCT.seq (two_post (Ψ := AfterCT) (search_run_ct sname c) fun q s ⟨o, st, a, hl, _⟩ =>
    WP.mono (hl.toGenFrame.search_run sname c hl.key.other) fun t ht => ⟨o, st, s, a, hl, ht⟩) ?_
  exact RelCT.seq (classify_ct name hv hks) (Search.quiet_ct (by taint_decide))

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## The controller is constant time (ARMv7)

Two runs with the same public arguments (`genPub`) have the same public data
and start at the same point: the progress' public words, the request word
and the key search's trace. The entry and the zeros at the key's buffer have
their addresses among the public registers, the loop goes on from point to
point (`iteration_ct`, `gen_ct_step`), and the results and the restored
registers are stored at public addresses.
-/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm VG.Proof.Mont
open VG.Proof.Ffdh.Arm.KeySearch (Two Pins two_taint two_post two_piece two_ite two_map two_mono alloc_ct)
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-- The first point of a run from `o`. -/
def startOf (p : GenPublic) (o : State) : GenPoint :=
  ⟨p, 0, (genProgress o).left, phaseWord (genProgress o).phase, (genProgress o).remaining,
    o.mem.readW (off p.st 24) 64, (genResult o).trace⟩

/-- A run's state after the push. -/
def StartCT (q : GenPoint) (s : State) : Prop :=
  ∃ o, s = pushed pushRegs o ∧ GenInput q.inputs o ∧ startOf q.inputs o = q

/-- After the load of the state's pointer. -/
def Start' (q : GenPoint) (s : State) : Prop := s.gpr .r9 = q.inputs.stp

theorem start_load (q : GenPoint) (s : State) (h : StartCT q s) :
    WP isa (.block [arg .r9 0 3]) s (Start' q) := by
  obtain ⟨o, rfl, hi, -⟩ := h
  have hroom : 40 ≤ o.sp.toNat := Nat.le_trans (by decide) hi.1.1
  have top := hi.1.2.1
  have a52 : State.addr (o.sp - BitVec.ofNat 32 40 + BitVec.ofNat 32 (pushBytes + 0 + 4 * 3)) = stackArgAddr o 3 := by
    rw [show pushBytes + 0 + 4 * 3 = 40 + 4 * 3 from rfl, sub_add_ofNat]; rfl
  have r52 : InRegions (o.rd ++ ⟨State.addr (o.sp - BitVec.ofNat 32 40), 40⟩ :: o.wr) (stackArgAddr o 3) 4 := by
    refine ⟨inArgs o, List.mem_append_left _ (by rw [hi.rd]; simp [inReads]), ?_⟩
    have e : stackArgAddr o 3 = stackArgAddr o 0 + BitVec.ofNat 64 12 := by
      simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
      exact VG.Arm.addr_add (by omega)
    rw [e]; exact Offset.contains_base _ (by decide) (by decide)
  have v52 : (pushed pushRegs o).mem.readW (stackArgAddr o 3) 32 = q.inputs.stp := by
    rw [hi.arg_frame (push_frame hi) (by decide), ← hi.2]; rfl
  have c : pushBytes + 0 + 4 * 3 < 4096 := by decide
  refine WP.mono (withRest_all [.r9] (Q := fun t => t.gpr .r9 = q.inputs.stp) ?_ (by rfl) (by rfl)) fun t ⟨h9, _⟩ => h9
  unfold arg
  ffrun [pushed_gpr, pushed_sp, pushed_rd, pushed_wr, a52, r52, v52, c, show 4 * pushRegs.length = 40 from rfl]

/-- After the entry, at the first point. -/
def EnteredCT (q : GenPoint) (s : State) : Prop :=
  ∃ o, GenInput q.inputs o ∧ startOf q.inputs o = q ∧ GenFrame q.inputs o 0 (genProgress o) s ∧
    s.gpr .r11 = 4 ∧ s.mem = (pushed pushRegs o).mem

theorem entry_ct : RelCT isa (Two StartCT) (.block entry) (Two EnteredCT) := by
  refine two_post ?_ fun q s ⟨o, hs, hi, hq⟩ => ?_
  · change RelCT isa _ (.block ([arg .r9 0 3] ++ entry.drop 1)) _
    refine RelCT.block_append (RelCT.seq (Search.ldrSp_ct (Ψ := Start') start_load) (two_taint [.r9] ?_
      (by taint_decide)))
    intro q s t h₁ h₂ r hr
    obtain rfl := List.mem_singleton.mp hr
    exact h₁.trans h₂.symm
  · subst hs
    exact WP.mono (entry_ok hi) fun t ⟨g, h11, hm⟩ => ⟨o, hi, hq, g, h11, hm⟩

/-- The key's buffer's `p` on entry is the progress' `p`. -/
theorem entry_other {p : GenPublic} {o s : State} (hi : GenInput p o) (hm : s.mem = (pushed pushRegs o).mem) :
    ∀ pB, (genProgress o).phase = .q pB → Spec.Rsa.bytesAt s.mem (p.slot 4) p.L = pB := by
  have room : 256 ≤ o.sp.toNat := hi.1.1
  have hroom : 40 ≤ o.sp.toNat := by omega
  have cf := hi.cfacts
  have f := hi.facts
  have hst := cf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, -, -, -, -⟩ := hst
  have hL : 32 ≤ p.L ∧ p.L ≤ 512 := by have hv := f.valid; unfold primeLenValid at hv; omega
  intro pB hpB
  have e : pB = Spec.Rsa.bytesAt o.mem (p.slot 4) p.L := by
    simp only [genProgress, keyProgressAt] at hpB
    split at hpB
    · cases hpB
    · injection hpB with h; rw [← h, ← hi.2]; rfl
  have hsub : Region.Sub (FrameStack.belowA o.sp 40) (cStack p) := by
    change Region.Sub ⟨State.addr (o.sp - BitVec.ofNat 32 40), 40⟩ _
    rw [FrameStack.addr_sub' hroom, ← hi.sp_eq]; exact Offset.sub_below _ (by decide) (by decide)
  rw [hm, e]
  exact bytes_kept (FrameStack.pushed_frameA (rs := pushRegs) hroom) (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact (sK.sub_left hsub).symm.sub_left (Offset.sub_base _ (by omega))) (by omega)

theorem clear_ct : RelCT isa (Two EnteredCT) clearAround (Two GenCTL) := by
  refine two_post (leaf_ct (fun q s ⟨_, _, _, g, _⟩ => g.regsOf) (by taint_decide)) fun q s ⟨o, hi, hq, g, h11, hm⟩ => ?_
  have hu : q.used = 0 := by rw [← hq]; rfl
  refine WP.mono (clearAround_ok g h11 (entry_other hi hm)) fun t ⟨hl, hf⟩ => ⟨o, genProgress o, ?_, hu ▸ hl, ?_⟩
  · rw [← hq]
    refine ⟨rfl, rfl, rfl, ?_⟩
    have hp : q.inputs = genOfState o := hi.2.symm
    simp only [startOf, tailOf, List.drop_zero, hp]
    rfl
  · have room : 256 ≤ o.sp.toNat := hi.1.1
    have hroom : 40 ≤ o.sp.toNat := by omega
    have cf := hi.cfacts
    have hst := cf.stack
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
    obtain ⟨-, -, -, sT, -, -⟩ := hst
    have hsub : Region.Sub (FrameStack.belowA o.sp 40) (cStack q.inputs) := by
      change Region.Sub ⟨State.addr (o.sp - BitVec.ofNat 32 40), 40⟩ _
      rw [FrameStack.addr_sub' hroom, ← hi.sp_eq]; exact Offset.sub_below _ (by decide) (by decide)
    have c24 : (cT q.inputs).Contains (off q.inputs.st 24) (64 / 8) := Offset.contains_base _ (by decide) (by decide)
    rw [hf.readW c24 (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact (cf.kT.sub_left (GenFrame.kSubK (by omega))).symm) (by decide), hm,
      (FrameStack.pushed_frameA (rs := pushRegs) hroom).readW c24 (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr; exact (sT.sub_left hsub).symm) (by decide), ← hq]
    rfl

/-! ## The loop -/

/-- A finished run. -/
def DoneCT (q : GenPoint) (s : State) : Prop := ∃ o final, GenDone q.inputs o final s

/-- What each step that goes on lowers. -/
def GenPoint.measure (q : GenPoint) : Nat := (q.inputs.randLen - q.used) * 2 ^ 64 + q.left

theorem next_lt {q : GenPoint} (hc : q.continues) {s : State} (h : GenCTL q.next s) :
    q.next.measure < q.measure := by
  obtain ⟨o, st, a, hl, -⟩ := h
  have hle := hl.used_le
  simp only [GenPoint.next] at hle
  unfold GenPoint.measure GenPoint.next
  simp only
  rcases hc with ⟨h3, hl2⟩ | ⟨h1, hc0, -⟩
  · simp only [h3, ↓reduceIte]
    have : (q.inputs.randLen - (q.used + q.cand)) * 2 ^ 64 ≤ (q.inputs.randLen - q.used) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · simp only [show ¬q.status = 3 by omega, ↓reduceIte]
    have hmul : (q.inputs.randLen - (q.used + q.cand) + 1) * 2 ^ 64 ≤ (q.inputs.randLen - q.used) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega

/-- Pairs of loop states at the same point, its measure `n`. -/
def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q : GenPoint, n = q.measure ∧ GenCTL q s ∧ GenCTL q t ∧ s.sp = t.sp

theorem iteration_pair (sname : String) (c : Search.Cand) (name : String) {kc : Prog isa}
    (hv : Verified target kc (Proof.RsaKeyGen.keyContract abi 56)) (hks : FrameStack.armStack kc ≤ 56) (n : Nat) :
    RelCT isa (LoopPair n) (iteration (.call sname (Impl.RsaKeyGen.Arm.Search.code c.call)) (.call name kc))
      fun s t => isa.eval .eq s = isa.eval .eq t ∧ (isa.eval .eq s = some false → Two DoneCT s t) ∧
        (isa.eval .eq s = some true → ∃ m < n, LoopPair m s t) := by
  have wp (q : GenPoint) (s : State) (h : n = q.measure ∧ GenCTL q s) :
      WP isa (iteration (.call sname (Impl.RsaKeyGen.Arm.Search.code c.call)) (.call name kc)) s
        fun t => n = q.measure ∧ GenCTStep q t :=
    WP.mono (gen_ct_step sname c name hv hks q s h.2) fun _ r => ⟨h.1, r⟩
  have ct := two_post ((iteration_ct sname c name hv hks).mono
    (fun _ _ ⟨q, hs, ht, sp⟩ => ⟨q, hs.2, ht.2, sp⟩) (fun _ _ h => h)) wp
  refine ct.mono (fun _ _ ⟨q, m, hs, ht, sp⟩ => ⟨q, ⟨m, hs⟩, ⟨m, ht⟩, sp⟩) ?_
  rintro s t ⟨q, ⟨m, hs⟩, ⟨_, ht⟩, sp⟩
  by_cases e : q.continues
  · obtain ⟨-, hes, hls⟩ := hs.resolve_right fun h => h.1 e
    obtain ⟨-, het, hlt⟩ := ht.resolve_right fun h => h.1 e
    refine ⟨hes.trans het.symm, (fun h => by rw [hes] at h; cases h), fun _ => ⟨q.next.measure, ?_, q.next, rfl, hls, hlt, sp⟩⟩
    rw [m]; exact next_lt e hls
  · obtain ⟨-, hes, ds⟩ := hs.resolve_left fun h => e h.1
    obtain ⟨-, het, dt⟩ := ht.resolve_left fun h => e h.1
    obtain ⟨o₁, f₁, d₁⟩ := ds
    obtain ⟨o₂, f₂, d₂⟩ := dt
    exact ⟨hes.trans het.symm, fun _ => ⟨q, ⟨o₁, f₁, d₁⟩, ⟨o₂, f₂, d₂⟩, sp⟩, (fun h => by rw [hes] at h; cases h)⟩

theorem loop_ct (sname : String) (c : Search.Cand) (name : String) {kc : Prog isa}
    (hv : Verified target kc (Proof.RsaKeyGen.keyContract abi 56)) (hks : FrameStack.armStack kc ≤ 56) :
    RelCT isa (Two GenCTL)
      (.loop (iteration (.call sname (Impl.RsaKeyGen.Arm.Search.code c.call)) (.call name kc)) .eq) (Two DoneCT) := by
  intro s t ts tt u v ⟨q, hs, ht, sp⟩ es et
  exact RelCT.loop LoopPair (iteration_pair sname c name hv hks) q.measure s t ts tt u v ⟨q, rfl, hs, ht, sp⟩ es et

theorem finish_ct : RelCT isa (Two DoneCT) (.block finish) fun _ _ => True := by
  unfold finish
  refine RelCT.block_append (RelCT.seq (VG.Proof.Bignum.Arm.relCT_keep_sp
    (leaf_ct (fun q s ⟨_, _, hd⟩ => hd.1.regsOf) (by taint_decide)) fun _ _ ⟨_, _, _, sp⟩ => sp) ?_)
  exact (VG.Proof.Bignum.Arm.stackLoads_ct [(.r5, 4), (.r6, 8), (.r7, 12), (.r8, 16), (.r9, 20),
    (.r10, 24), (.r11, 28), (.lr, 36)]).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem body_ct (sname : String) (c : Search.Cand) (name : String) {kc : Prog isa}
    (hv : Verified target kc (Proof.RsaKeyGen.keyContract abi 56)) (hks : FrameStack.armStack kc ≤ 56) :
    RelCT isa (Two StartCT) (body (.call sname (Impl.RsaKeyGen.Arm.Search.code c.call)) (.call name kc))
      fun _ _ => True := by
  unfold body
  exact RelCT.seq entry_ct (RelCT.seq clear_ct (RelCT.seq (loop_ct sname c name hv hks) finish_ct))

/-! ## The public data of two runs -/

theorem byte_of_word (m : Mem) (a : Addr) {i : Nat} (hi : i < 8) :
    m (a + BitVec.ofNat 64 i) = (m.readW a 64).extractLsb' (8 * i) 8 := by
  rw [← Mem.extractLsb'_read m a (n := 8) hi]
  simp only [Mem.readW]
  rfl

theorem bytes_of_word {m m' : Mem} {a : Addr} (h : m.readW a 64 = m'.readW a 64) :
    Spec.Rsa.bytesAt m a 8 = Spec.Rsa.bytesAt m' a 8 := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [byte_of_word m a hi, byte_of_word m' a hi, h]

theorem word_of_words {m m' : Mem} {a a' : Addr} (h : Spec.Rsa.wordsAt m a 7 = Spec.Rsa.wordsAt m' a' 7)
    (i : Nat) (hi : i < 7) : m.readW (a + BitVec.ofNat 64 (8 * i)) 64 = m'.readW (a' + BitVec.ofNat 64 (8 * i)) 64 := by
  have := congrArg (·[i]?) h
  simpa [Spec.Rsa.wordsAt, hi] using this

theorem phaseWord_progress (m : Mem) (k st : Addr) (L : Nat) :
    phaseWord (keyProgressAt m k st L).phase = if (m.readW (st + 32) 64).toNat = 0 then 0 else 1 := by
  simp only [keyProgressAt]; split <;> rfl

theorem pub_same {s t : State} (h : genPub s t) : genOfState s = genOfState t := by
  obtain ⟨hsp, r0, r1, r2, r3, ha, hw, -⟩ := h
  have hstp : genStp s = genStp t := by simp only [genStp, ha 3 (by decide)]
  rw [← hstp] at hw
  have w1 := word_of_words hw 1 (by decide)
  have w6 := word_of_words hw 6 (by decide)
  simp only [Nat.reduceMul] at w1 w6
  unfold genOfState
  simp only [genLen, genE, ← hstp, hsp, r0, r2, r3, ha 0 (by decide), ha 1 (by decide), ha 2 (by decide),
    ha 3 (by decide)]
  rw [show genStp s + 8 = genStp s + BitVec.ofNat 64 8 from rfl, w1,
    show genStp s + 48 = genStp s + BitVec.ofNat 64 48 from rfl, bytes_of_word w6]

theorem start_same {s t : State} (h : genPub s t) :
    startOf (genOfState s) s = startOf (genOfState s) t := by
  have ht := h.2.2.2.2.2.2.2.2.2.2
  have hp := pub_same h
  obtain ⟨hsp, r0, r1, r2, r3, ha, hw, -⟩ := h
  have hstp : genStp s = genStp t := by simp only [genStp, ha 3 (by decide)]
  rw [← hstp] at hw
  have w0 := word_of_words hw 0 (by decide)
  have w3 := word_of_words hw 3 (by decide)
  have w4 := word_of_words hw 4 (by decide)
  have w5 := word_of_words hw 5 (by decide)
  simp only [Nat.reduceMul, Nat.mul_zero, BitVec.add_zero] at w0 w3 w4 w5
  have el (m : Mem) (k st : Addr) (L : Nat) : (keyProgressAt m k st L).left = (m.readW (st + 40) 64).toNat := rfl
  have er (m : Mem) (k st : Addr) (L : Nat) : (keyProgressAt m k st L).remaining = (m.readW st 64).toNat := rfl
  unfold startOf
  simp only [genProgress, el, er, phaseWord_progress, ← hstp, ht]
  rw [show genStp s + 40 = genStp s + BitVec.ofNat 64 40 from rfl, w5,
    show genStp s + 32 = genStp s + BitVec.ofNat 64 32 from rfl, w4, w0,
    show off (genOfState s).st 24 = genStp s + BitVec.ofNat 64 24 from rfl, w3]

theorem code_ct (sname : String) (c : Search.Cand) (name : String) {kc : Prog isa}
    (hv : Verified target kc (Proof.RsaKeyGen.keyContract abi 56)) (hks : FrameStack.armStack kc ≤ 56) :
    RelCT isa (fun s t => genPre s ∧ genPre t ∧ genPub s t)
      (code (.call sname (Impl.RsaKeyGen.Arm.Search.code c.call)) (.call name kc)) (fun _ _ => True) := by
  unfold code
  rw [show pushBytes = 4 * pushRegs.length from rfl]
  refine RelCT.frame (fun _ _ h => h.2.2.1) ?_
  rintro a b ta tb u v ⟨s, t, ⟨hs, ht, hp⟩, ea, eb⟩ e1 e2
  have rs : 256 ≤ s.sp.toNat := hs.1
  have rt : 256 ≤ t.sp.toNat := ht.1
  rw [push_pushed (by decide) (by simp only [List.length_cons, List.length_nil]; omega)] at ea eb
  cases ea
  cases eb
  have hpt := pub_same hp
  have hq := start_same hp
  exact body_ct sname c name hv hks _ _ ta tb u v
    ⟨startOf (genOfState s) s, ⟨s, rfl, ⟨hs, rfl⟩, rfl⟩, ⟨t, rfl, ⟨ht, hpt.symm⟩, hq.symm⟩,
      by simp only [pushed_sp, hp.1]⟩ e1 e2

theorem gen_constantTime (sname : String) (c : Search.Cand) (name : String) {kc : Prog isa}
    (hv : Verified target kc (Proof.RsaKeyGen.keyContract abi 56)) (hks : FrameStack.armStack kc ≤ 56) :
    ConstantTime isa genContract.pre genContract.pub
      (code (.call sname (Impl.RsaKeyGen.Arm.Search.code c.call)) (.call name kc)) :=
  RelCT.constantTime (code_ct sname c name hv hks)

end VG.Proof.RsaKeyGen.Arm.Generate

/-! ## The verified key search, for every arithmetic backend (ARMv7) -/

namespace VG.Proof.RsaKeyGen.Arm.Generate

open VG VG.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)
open VG.Impl.RsaKeyGen.Arm.Generate

/-- The key's 56 bytes: its push, and no frame inside it. -/
theorem key_stack : FrameStack.armStack Impl.RsaKeyGen.Arm.Key.code ≤ 56 := by decide +kernel

/-- The controller, calling the prime search over the round `v` and the key. -/
abbrev genCode [VG.Proof.Rsa.Arm.Keys.InvLaw] (v : RoundImpl) : Prog isa :=
  code (.call ("vg_rsa_prime_search" ++ v.suffix) (Search.searchCode v))
    (.call "vg_rsa_keygen_key" Impl.RsaKeyGen.Arm.Key.code)

theorem gen_correct [VG.Proof.Rsa.Arm.Keys.InvLaw] (v : RoundImpl) (s : State) (h : genContract.pre s) :
    ∃ tr t, Exec isa (genCode v) s tr t ∧ abiPreserved s t ∧ genContract.post s t := by
  obtain ⟨tr, t, he, hp, ha⟩ := gen_correct_ok _ (Search.Cand.ofRound v) _ Key.key_verified key_stack h
  exact ⟨tr, t, he, ha, hp⟩

/-- The controller, given the inverse's law (`InvLaw`, whose instance the
registration file imports). -/
theorem gen_verified [VG.Proof.Rsa.Arm.Keys.InvLaw] (v : RoundImpl) :
    Verified target (genCode v) (Spec.RsaKeyGen.keySearchContract abi stackUse) :=
  Verified.of_correct (gen_correct v)
    (gen_constantTime _ (Search.Cand.ofRound v) _ Key.key_verified key_stack) gen_implies

end VG.Proof.RsaKeyGen.Arm.Generate
