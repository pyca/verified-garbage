module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Step
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Entry
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Call
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.SearchSpec
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Step
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Entry
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Call
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.RsaKeyGen.SearchSpec
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.TaintBatch

-- separate module: its proofs build in parallel with the correctness ones, `Correct`

/-! # The search's timing depends on its public data and its trace (AArch64)

As on x86-64 (`Proof/RsaKeyGen/X86_64/Search/CT.lean`): two runs at the same
point (`SearchPoint`) agree on the public descriptor, the octets consumed,
the counted candidates left and the trace still to come. The next
candidate's leak is the trace's next entry, and with it what became of the
candidate: its status and the octets it consumed.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Search

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.AArch64 (movi ld)
open VG.Impl.RsaKeyGen.AArch64.Search
open VG.Spec.RsaKeyGen (PrimeSearchResult primeEntropy)

structure SearchPoint where
  inputs : SearchPublic
  used : Nat
  remaining : Nat
  trace : List Nat

def SearchCTL (q : SearchPoint) (s : State) : Prop :=
  ∃ original, SearchLive q.inputs original q.used q.remaining s ∧
    (tailOf q.inputs original q.used q.remaining).trace = q.trace

/-- Some loop state with the public descriptor `p`. -/
def SearchAny (p : SearchPublic) (s : State) : Prop :=
  ∃ original used remaining, SearchLive p original used remaining s

theorem SearchCTL.any {q : SearchPoint} {s : State} (h : SearchCTL q s) : SearchAny q.inputs s :=
  let ⟨original, h, _⟩ := h; ⟨original, _, _, h⟩

theorem search_any_pins : Pins SearchAny [.x19] := by
  intro p s t ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.x19.trans h₂.x19.symm

theorem search_ctl_pins : Pins SearchCTL [.x19] :=
  fun _ _ _ h₁ h₂ => search_any_pins _ _ _ h₁.any h₂.any

theorem no_pins {α : Type} {Φ : α → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ h => by cases h

private theorem leaf {α : Type} {Φ : α → State → Prop} {c : Prog isa} (f : α → SearchPublic)
    (hΦ : ∀ q s, Φ q s → SearchAny (f q) s) (hc : RelCT isa (Two SearchAny) c fun _ _ => True) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨f q, hΦ q _ h₁, hΦ q _ h₂, hsp⟩) fun _ _ h => h

/-- The next candidate's leak, from the trace. -/
def SearchPoint.leak (q : SearchPoint) : List Nat := (q.trace.drop 1).take (q.trace.headD 0)

theorem SearchCTL.leak {q : SearchPoint} {original : State}
    (ht : (tailOf q.inputs original q.used q.remaining).trace = q.trace) (hr : q.remaining ≠ 0) :
    Spec.RsaKeyGen.candidateLeak q.inputs.len q.inputs.eB (searchP original)
      ((searchRand original).drop q.used) = q.leak := by
  obtain ⟨rest, hrest⟩ := VG.Proof.RsaKeyGen.Search.search_trace (L := q.inputs.len) (eB := q.inputs.eB)
    (pB := searchP original) hr ((searchRand original).drop q.used)
  unfold tailOf at ht
  rw [hrest] at ht
  unfold SearchPoint.leak
  rw [← ht]
  simp [VG.Proof.RsaKeyGen.Search.entry]

/-- The candidate's status, from the point. -/
abbrev SearchPoint.status (q : SearchPoint) : Nat := Search.statusOfLeak q.leak

/-- The octets the candidate consumed, from the point. -/
abbrev SearchPoint.cand (q : SearchPoint) : Nat := Search.usedOfLeak q.inputs.len q.leak

theorem SearchCTL.status {q : SearchPoint} {original : State}
    (ht : (tailOf q.inputs original q.used q.remaining).trace = q.trace) (hr : q.remaining ≠ 0) :
    candStatus q.inputs original q.used = q.status := by
  rw [candStatus, VG.Proof.RsaKeyGen.Search.status_of_leak, SearchCTL.leak ht hr]

theorem SearchCTL.used {q : SearchPoint} {original s : State}
    (hl : SearchLive q.inputs original q.used q.remaining s)
    (ht : (tailOf q.inputs original q.used q.remaining).trace = q.trace) (hr : q.remaining ≠ 0) :
    candUsed q.inputs original q.used = q.cand := by
  have hu := VG.Proof.RsaKeyGen.Search.used_of_leak (L := q.inputs.len) (eB := q.inputs.eB)
    (pB := searchP original) ((searchRand original).drop q.used)
  rw [SearchCTL.leak ht hr, List.length_drop, hl.rand_length] at hu
  exact hu

/-! ## Giving up -/

/-- Before the zeroing's loop: its pointer and count. -/
def SearchZeroCT (p : SearchPublic) (s : State) : Prop :=
  SearchAny p s ∧ s.gpr .x1 = p.op + BitVec.ofNat 64 0 ∧ s.gpr .x2 = BitVec.ofNat 64 p.len

private theorem zero_header (p : SearchPublic) (s : State) (h : SearchAny p s) :
    WP isa (.block [ldf .x1 5, ldf .x2 6, movi .x3 0]) s (SearchZeroCT p) := by
  obtain ⟨original, used, k, h⟩ := h
  have hk := h.slot (j := 6) (v := BitVec.ofNat 64 p.len) (by simp [SearchPublic.headers])
  have hp := h.slot (j := 5) (v := p.op) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hk hp
  refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => (t.gpr .x1 = p.op + BitVec.ofNat 64 0 ∧
    t.gpr .x2 = BitVec.ofNat 64 p.len) ∧ t.mem = s.mem) ?_ (by decide) (by decide) (by decide +kernel))
    fun _ ⟨⟨hr, hm⟩, k⟩ => ⟨⟨original, used, _, h.keep k hm⟩, hr⟩
  brun [ldf, h.x19, hp, hk, h.frame_ld' 40 (by decide), h.frame_ld' 48 (by decide),
    imm64 (show 0 < 65536 by decide)]

theorem search_zero_ct : RelCT isa (Two SearchAny) zeroOut (fun _ _ => True) := by
  unfold zeroOut
  refine RelCT.seq (two_piece [.x19] search_any_pins (by taint_decide) zero_header) ?_
  exact two_taint [.x1, .x2] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.trans h₂.2.2.symm]) (by taint_decide)

private theorem terminal_ready (p : SearchPublic) (s : State) (h : SearchAny p s) :
    WP isa (.block (terminal 3)) s (SearchAny p) := by
  obtain ⟨original, used, k, h⟩ := h
  exact WP.mono (search_terminal h (k := 3) (.inr rfl)) fun _ ⟨hm, kt⟩ =>
    ⟨original, used, 0, h.terminated 3 hm kt⟩

theorem search_exhausted_ct : RelCT isa (Two SearchAny) exhausted (fun _ _ => True) := by
  unfold exhausted
  exact RelCT.seq (two_piece [.x19] search_any_pins (by taint_decide) terminal_ready) search_zero_ct

theorem search_accept_ct : RelCT isa (Two SearchAny) (.block accept) (fun _ _ => True) :=
  two_taint [.x19] search_any_pins (by taint_decide)

theorem search_request_ct : RelCT isa (Two SearchAny) (.block request) (fun _ _ => True) :=
  two_taint [.x19] search_any_pins (by taint_decide)

/-! ## After the candidate -/

/-- A loop state at the point, before its candidate. -/
def SearchAt (q : SearchPoint) (s : State) : Prop :=
  ∃ original, SearchLive q.inputs original q.used q.remaining s

theorem SearchAt.any {q : SearchPoint} {s : State} (h : SearchAt q s) : SearchAny q.inputs s :=
  let ⟨original, h⟩ := h; ⟨original, _, _, h⟩

/-- A loop state at the point, after its candidate. -/
def CandCT (q : SearchPoint) (s : State) : Prop :=
  ∃ original, SearchLive q.inputs original q.used q.remaining s ∧
    CandPost q.inputs (searchP original) (searchRand original) q.used s ∧
    (tailOf q.inputs original q.used q.remaining).trace = q.trace ∧ q.remaining ≠ 0

theorem CandCT.at {q : SearchPoint} {s : State} (h : CandCT q s) : SearchAt q s :=
  let ⟨o, h, _⟩ := h; ⟨o, h⟩

theorem cand_ct_pins : Pins CandCT [.x19] := fun q _ _ h₁ h₂ =>
  search_any_pins q.inputs _ _ h₁.at.any h₂.at.any

theorem status_lt' (q : SearchPoint) {s : State} (h : CandCT q s) : q.status < 4 := by
  obtain ⟨o, -, -, ht, hr⟩ := h
  rw [← SearchCTL.status ht hr]
  exact status_lt _ _ _

/-- After the status and the pointer to `used` are loaded. -/
def HeadCT (q : SearchPoint) (t : State) : Prop :=
  CandCT q t ∧ t.gpr .x11 = q.inputs.up ∧ t.gpr .x9 = BitVec.ofNat 64 q.status

private theorem head_first (q : SearchPoint) (s : State) (h : CandCT q s) :
    WP isa (.block [.addImm .w .x9 .x0 0, ldf .x11 7]) s (HeadCT q) := by
  have hst := status_lt' q h
  obtain ⟨original, h, hp, ht, hr⟩ := h
  have hv7 := h.slot (j := 7) (v := q.inputs.up) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv7
  have h0 : (s.gpr .x0).setWidth 32 = BitVec.ofNat 32 q.status := by
    apply BitVec.eq_of_toNat_eq
    rw [hp.1, BitVec.toNat_ofNat, ← SearchCTL.status ht hr, Nat.mod_eq_of_lt (by
      rw [SearchCTL.status ht hr]; omega)]
  refine WP.mono (WP.keep [.x9, .x11] (Q := fun t =>
    (t.gpr .x11 = q.inputs.up ∧ t.gpr .x9 = BitVec.ofNat 64 q.status) ∧ t.mem = s.mem) ?_
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨⟨h11, h9⟩, hm⟩, k⟩ => ?_
  · brun [ldf, h.x19, hv7, h.frame_ld' 56 (by decide),
      VG.Proof.RsaKeyGen.AArch64.exec_addImm_w (show 0 < 4096 by decide), h0]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · exact ⟨⟨original, h.keep k hm, hp.keep hm (by rw [k.gpr .x0 (by decide)]), ht, hr⟩, h11, h9⟩

theorem head_pins : Pins HeadCT [.x11] := by
  intro q s t h₁ h₂ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.2.1.trans h₂.2.1.symm

/-- The status in `x9`, the octets consumed in `x10`, and whether the status
is 1. -/
def GuardCT (q : SearchPoint) (t : State) : Prop :=
  CandCT q t ∧ t.gpr .x9 = BitVec.ofNat 64 q.status ∧ t.gpr .x10 = BitVec.ofNat 64 q.cand ∧
    isa.eval (.zero .x .x12) t = some (decide (q.status = 1))

private theorem head_second (q : SearchPoint) (s : State) (h : HeadCT q s) :
    WP isa (.block [ld .x10 .x11, .subImm .x .x12 .x9 1]) s (GuardCT q) := by
  have hst := status_lt' q h.1
  obtain ⟨⟨original, h, hp, ht, hr⟩, h11, h9⟩ := h
  have hu : InRegions (s.rd ++ s.wr) q.inputs.up 8 := by
    refine ⟨inUsed original, List.mem_append_right _ ?_, ?_⟩
    · rw [h.wr, h.input.1.2.2.2.1]; exact List.mem_cons_of_mem _ (by simp [inWrites])
    · rw [← h.input.2]; simp only [inUsed, searchOfState, Region.Contains, BitVec.sub_self, BitVec.toNat_zero,
        Nat.zero_add]; decide
  have hw : s.mem.readW q.inputs.up 64 = BitVec.ofNat 64 q.cand := by
    have := hp.2.2
    change [word s.mem q.inputs.up 0] = _ at this
    simp only [Bignum.word, off, BitVec.add_zero, List.cons.injEq, and_true] at this
    rw [this, ← SearchCTL.used h ht hr]
    rfl
  refine WP.mono (WP.keep [.x10, .x12] (Q := fun t =>
    (t.gpr .x10 = BitVec.ofNat 64 q.cand ∧ isa.eval (.zero .x .x12) t = some (decide (q.status = 1))) ∧
      t.mem = s.mem) ?_
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨⟨h10, he⟩, hm⟩, k⟩ =>
      ⟨⟨original, h.keep k hm, hp.keep hm (by rw [k.gpr .x0 (by decide)]), ht, hr⟩,
        (k.gpr .x9 (by decide)).trans h9, h10, he⟩
  brun [ld, h11, h9, hu, hw, BitVec.add_zero]
  have : ∀ st < 4, ((BitVec.ofNat 64 st - BitVec.ofNat 64 1) == 0) = decide (st = 1) := by decide
  simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq, this _ hst]

/-- The short tape's test, at the point. -/
def ShortCT (q : SearchPoint) (t : State) : Prop :=
  SearchAt q t ∧ isa.eval (.zero .x .x12) t =
    some (decide (q.inputs.randLen - q.used < primeEntropy q.inputs.len))

private theorem short_ready (q : SearchPoint) (s : State) (h : SearchAt q s) :
    WP isa (.block [ldf .x10 13, ldf .x11 2, .subs .x .x12 .x10 .x11, movi .x13 0, movi .x14 1,
      .csel .x .x12 .x14 .x13]) s (ShortCT q) := by
  obtain ⟨o, hl⟩ := h
  exact WP.mono (short_guard hl) fun t ⟨⟨⟨_, _, hm⟩, k⟩, he⟩ => ⟨⟨o, hl.keep k hm⟩, he⟩

theorem search_short_ct : RelCT isa (Two SearchAt) short (fun _ _ => True) := by
  unfold short
  refine RelCT.seq (two_piece [.x19] (fun q _ _ h₁ h₂ => search_any_pins q.inputs _ _ h₁.any h₂.any)
    (by taint_decide) short_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact leaf SearchPoint.inputs (fun _ _ h => h.1.1.any) search_request_ct
  · exact leaf SearchPoint.inputs (fun _ _ h => h.1.1.any) search_exhausted_ct

/-- Past the candidate's octets, at the point: whether its status was 2. -/
def Reject3 (q : SearchPoint) (t : State) : Prop :=
  t.gpr .x19 = q.inputs.F ∧ isa.eval (.zero .x .x13) t = some (decide (q.status = 2))

private theorem advance_ready (q : SearchPoint) (s : State)
    (h : GuardCT q s ∧ isa.eval (.zero .x .x12) s = some false ∧ isa.eval (.zero .x .x9) s = some false ∧
      isa.eval (.zero .x .x10) s = some false) :
    WP isa (.block advance) s (Reject3 q) := by
  obtain ⟨⟨hc, h9, h10, -⟩, -, -, -⟩ := h
  have hst := status_lt' q hc
  obtain ⟨o, hl, -, -, -⟩ := hc
  refine WP.mono (advance_ok hl h10) fun t ⟨⟨_, he⟩, kt⟩ => ⟨(kt.gpr .x19 (by decide)).trans hl.x19, ?_⟩
  rw [he, h9]
  have : ∀ st < 4, ((BitVec.ofNat 64 st - BitVec.ofNat 64 2) == 0) = decide (st = 2) := by decide
  rw [this _ hst]

theorem search_reject_ct : RelCT isa (Two fun q s => GuardCT q s ∧ isa.eval (.zero .x .x12) s = some false ∧
    isa.eval (.zero .x .x9) s = some false) reject (fun _ _ => True) := by
  unfold reject
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.1.2.2.1, h₂.1.2.2.1]) ?_ ?_
  · exact leaf SearchPoint.inputs (fun _ _ h => h.1.1.1.at.any) search_exhausted_ct
  · refine RelCT.seq (two_piece (Ψ := Reject3) [.x19] (fun q _ _ h₁ h₂ =>
      cand_ct_pins q _ _ h₁.1.1.1 h₂.1.1.1) (by taint_decide)
      (fun q s h => advance_ready q s ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩)) ?_
    refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
    · exact two_taint [] no_pins (by taint_decide)
    · exact two_taint [.x19] (fun _ _ _ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr
        subst r
        exact h₁.1.1.trans h₂.1.1.symm) (by taint_decide)

theorem search_classify_ct : RelCT isa (Two CandCT) classify (fun _ _ => True) := by
  unfold classify
  change RelCT isa (Two CandCT) (.seq (.block ([.addImm .w .x9 .x0 0, ldf .x11 7] ++
    [ld .x10 .x11, .subImm .x .x12 .x9 1])) _) _
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (two_piece [.x19] cand_ct_pins (by taint_decide) head_first)
    (two_piece [.x11] head_pins (by taint_decide) head_second))) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm)
    (leaf SearchPoint.inputs (fun _ _ h => h.1.1.at.any) search_accept_ct) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.1.2.1, h₂.1.2.1]) ?_ ?_
  · exact (search_short_ct.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.1.1.1.at, h₂.1.1.1.at, hsp⟩)
      fun _ _ h => h)
  · exact (search_reject_ct.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, ⟨h₁.1.1, h₁.1.2, h₁.2⟩,
      ⟨h₂.1.1, h₂.1.2, h₂.2⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.RsaKeyGen.AArch64.Search
