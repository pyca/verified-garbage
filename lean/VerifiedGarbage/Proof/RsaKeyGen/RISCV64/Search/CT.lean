module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Step
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Entry
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Call
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.SearchSpec
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Step
meta import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Entry
meta import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Search.Call
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.RsaKeyGen.SearchSpec
meta import VerifiedGarbage.Proof.RsaKeyGen.InitWords
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Syms
meta import VerifiedGarbage.Proof.Framework.Offset

-- separate module: its proofs build in parallel with the correctness ones, `Correct`

/-! # The search's timing depends on its public data and its trace (RISC-V)

As on PPC64LE (`Proof/RsaKeyGen/PPC64LE/Search/CT.lean`): two runs at the
same point (`SearchPoint`) agree on the public descriptor, the octets
consumed, the counted candidates left, the trace still to come and the
table's address. The next candidate's leak is the trace's next entry, and
with it what became of the candidate: its status and the octets it consumed.
The taint analysis treats memory as secret, so the addresses loaded from the
frame are pinned from the functional proofs.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Search

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.RISCV64 VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)
open VG.Impl.RsaKeyGen.RISCV64.Search
open VG.Proof.RsaKeyGen.RISCV64.Cand (CIn TabOk KRel KR pubOf)
open VG.Spec.RsaKeyGen (PrimeSearchResult primeEntropy)

theorem two_piece {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) : RelCT isa (Two Φ) c (Two Ψ) :=
  two_post (two_taint rs hpin h) hw

theorem two_map {α β : Type} {Φ : α → State → Prop} {Φ' : β → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (g : α → β) (h : ∀ a s, Φ a s → Φ' (g a) s) (hct : RelCT isa (Two Φ') c Q) :
    RelCT isa (Two Φ) c Q :=
  hct.mono (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨g a, h _ _ h₁, h _ _ h₂, hsp⟩) fun _ _ h => h

/-- A branch whose condition `Φ a` fixes. -/
theorem two_ite {α : Type} {Φ : α → State → Prop} {cond : isa.Cond} {th el : Prog isa}
    {Q : State → State → Prop}
    (hc : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → isa.eval cond s₁ = isa.eval cond s₂)
    (ht : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some true) th Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some false) el Q) :
    RelCT isa (Two Φ) (.ite cond th el) Q := by
  refine RelCT.ite (fun _ _ ⟨a, h₁, h₂, _⟩ => hc a _ _ h₁ h₂) (ht.mono ?_ fun _ _ h => h)
    (he.mono ?_ fun _ _ h => h)
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, ⟨h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩, hsp⟩
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, ⟨h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩, hsp⟩

structure SearchPoint where
  inputs : SearchPublic
  used : Nat
  remaining : Nat
  trace : List Nat
  tab : Addr

def SearchCTL (q : SearchPoint) (s : State) : Prop :=
  ∃ original, SearchLive q.inputs original q.used q.remaining s ∧
    (tailOf q.inputs original q.used q.remaining).trace = q.trace ∧ tabAddr original = q.tab

/-- Some loop state with the public descriptor `p`. -/
def SearchAny (p : SearchPublic) (s : State) : Prop :=
  ∃ original used remaining, SearchLive p original used remaining s

theorem SearchCTL.any {q : SearchPoint} {s : State} (h : SearchCTL q s) : SearchAny q.inputs s :=
  let ⟨original, h, _⟩ := h; ⟨original, _, _, h⟩

theorem search_any_pins : Pins SearchAny [.s0] := by
  intro p s t ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.s0.trans h₂.s0.symm

theorem search_ctl_pins : Pins SearchCTL [.s0] :=
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
  SearchAny p s ∧ s.gpr .a1 = p.op ∧ s.gpr .a2 = BitVec.ofNat 64 p.len

private theorem zero_header (p : SearchPublic) (s : State) (h : SearchAny p s) :
    WP isa (.block [ldf .a1 5, ldf .a2 6, .li .a3 0]) s (SearchZeroCT p) := by
  obtain ⟨original, used, k, h⟩ := h
  have hk := h.slot (j := 6) (v := BitVec.ofNat 64 p.len) (by simp [SearchPublic.headers])
  have hp := h.slot (j := 5) (v := p.op) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hk hp
  refine WP.mono (WP.keepS [.a1, .a2, .a3] (Q := fun t => (t.gpr .a1 = p.op ∧
    t.gpr .a2 = BitVec.ofNat 64 p.len) ∧ t.mem = s.mem) ?_ (by decide +kernel))
    fun _ ⟨⟨⟨hr, hm⟩, k⟩, hy⟩ => ⟨⟨original, used, _, h.keep k hm hy⟩, hr⟩
  brun [ldf, h.s0, hp, hk, exec_li, h.frame_ld' 40 (by decide), h.frame_ld' 48 (by decide),
    h.frame_al' 40 (by decide) (by decide), h.frame_al' 48 (by decide) (by decide)]

theorem search_zero_ct : RelCT isa (Two SearchAny) zeroOut (fun _ _ => True) := by
  unfold zeroOut
  refine RelCT.seq (two_piece [.s0] search_any_pins (by taint_decide) zero_header) ?_
  exact two_taint [.a1, .a2] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.trans h₂.2.2.symm]) (by taint_decide)

private theorem terminal_ready (p : SearchPublic) (s : State) (h : SearchAny p s) :
    WP isa (.block (terminal 3)) s (SearchAny p) := by
  obtain ⟨original, used, k, h⟩ := h
  exact VG.RISCV64.WP.mono_syms (search_terminal h (k := 3) (.inr rfl)) fun _ ⟨hm, kt⟩ hy =>
    ⟨original, used, 0, h.terminated 3 hm hy kt⟩

theorem search_exhausted_ct : RelCT isa (Two SearchAny) exhausted (fun _ _ => True) := by
  unfold exhausted
  exact RelCT.seq (two_piece [.s0] search_any_pins (by taint_decide) terminal_ready) search_zero_ct

theorem search_accept_ct : RelCT isa (Two SearchAny) (.block accept) (fun _ _ => True) :=
  two_taint [.s0] search_any_pins (by taint_decide)

theorem search_request_ct : RelCT isa (Two SearchAny) (.block request) (fun _ _ => True) :=
  two_taint [.s0] search_any_pins (by taint_decide)

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

theorem cand_ct_pins : Pins CandCT [.s0] := fun q _ _ h₁ h₂ =>
  search_any_pins q.inputs _ _ h₁.at.any h₂.at.any

theorem status_lt' (q : SearchPoint) {s : State} (h : CandCT q s) : q.status < 4 := by
  obtain ⟨o, -, -, ht, hr⟩ := h
  rw [← SearchCTL.status ht hr]
  exact status_lt _ _ _

/-- After the status and the pointer to `used` are loaded. -/
def HeadCT (q : SearchPoint) (t : State) : Prop :=
  CandCT q t ∧ t.gpr .t3 = q.inputs.up ∧ t.gpr .t1 = BitVec.ofNat 64 q.status

private theorem head_first (q : SearchPoint) (s : State) (h : CandCT q s) :
    WP isa (.block [.shift .sll .d .t1 .a0 32, .shift .srl .d .t1 .t1 32, ldf .t3 7]) s (HeadCT q) := by
  obtain ⟨original, h, hp, ht, hr⟩ := h
  have hv7 := h.slot (j := 7) (v := q.inputs.up) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv7
  have h0 := low32 (hp.1.trans (SearchCTL.status ht hr))
  refine WP.mono (WP.keepS [.t1, .t3] (Q := fun t =>
    (t.gpr .t3 = q.inputs.up ∧ t.gpr .t1 = BitVec.ofNat 64 q.status) ∧ t.mem = s.mem) ?_
    (by decide +kernel)) fun t ⟨⟨⟨⟨h11, h9⟩, hm⟩, k⟩, hy⟩ => ?_
  · brun [ldf, h.s0, hv7, h.frame_ld' 56 (by decide), h.frame_al' 56 (by decide) (by decide), h0]
  · exact ⟨⟨original, h.keep k hm hy, hp.keep hm (by rw [k.gpr .a0 (by decide)]), ht, hr⟩, h11, h9⟩

theorem head_pins : Pins HeadCT [.t3] := by
  intro q s t h₁ h₂ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.2.1.trans h₂.2.1.symm

/-- The status in `t1`, the octets consumed in `t2`, and whether the status
is 1. -/
def GuardCT (q : SearchPoint) (t : State) : Prop :=
  CandCT q t ∧ t.gpr .t1 = BitVec.ofNat 64 q.status ∧ t.gpr .t2 = BitVec.ofNat 64 q.cand ∧
    isa.eval (.zero .t4) t = some (decide (q.status = 1))

private theorem head_second (q : SearchPoint) (s : State) (h : HeadCT q s) :
    WP isa (.block [.load .d .t2 .t3 0, .addi .t4 .t1 (-1)]) s (GuardCT q) := by
  have hst := status_lt' q h.1
  obtain ⟨⟨original, h, hp, ht, hr⟩, h11, h9⟩ := h
  have hu : InRegions (s.rd ++ s.wr) (q.inputs.up + BitVec.ofNat 64 0) 8 := by
    refine ⟨inUsed original, List.mem_append_right _ ?_, ?_⟩
    · rw [h.wr, h.input.wr_eq]; exact List.mem_cons_of_mem _ (by simp [inWrites])
    · rw [← h.input.2]; simp only [inUsed, searchOfState, Region.Contains, BitVec.add_zero, BitVec.sub_self,
        BitVec.toNat_zero, Nat.zero_add]; decide
  have hua : (q.inputs.up + BitVec.ofNat 64 0).toNat % 8 = 0 := by
    rw [BitVec.add_zero, ← h.input.2]; exact h.input.used_al
  have hw : s.mem.readW (q.inputs.up + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 q.cand := by
    have := hp.2.2
    change [word s.mem q.inputs.up 0] = _ at this
    simp only [Bignum.word, off, List.cons.injEq, and_true] at this
    rw [this, ← SearchCTL.used h ht hr]
    rfl
  refine WP.mono (WP.keepS [.t2, .t4] (Q := fun t =>
    (t.gpr .t2 = BitVec.ofNat 64 q.cand ∧ isa.eval (.zero .t4) t = some (decide (q.status = 1))) ∧
      t.mem = s.mem) ?_
    (by decide +kernel)) fun t ⟨⟨⟨⟨h10, he⟩, hm⟩, k⟩, hy⟩ =>
      ⟨⟨original, h.keep k hm hy, hp.keep hm (by rw [k.gpr .a0 (by decide)]), ht, hr⟩,
        (k.gpr .t1 (by decide)).trans h9, h10, he⟩
  brun [h11, h9, hu, hua, hw]
  refine (eval_zero _ _).trans ?_
  have : ∀ st < 4, ((BitVec.ofNat 64 st - BitVec.ofNat 64 1) == 0) = decide (st = 1) := by decide
  simp only [RegUpd.gpr_write_self, this _ hst]

/-- The short tape's test, at the point. -/
def ShortCT (q : SearchPoint) (t : State) : Prop :=
  SearchAt q t ∧ isa.eval (.zero .t4) t =
    some (decide (primeEntropy q.inputs.len ≤ q.inputs.randLen - q.used))

private theorem short_ready (q : SearchPoint) (s : State) (h : SearchAt q s) :
    WP isa (.block [ldf .t2 13, ldf .t3 2, .sltu .t4 .t2 .t3]) s (ShortCT q) := by
  obtain ⟨o, hl⟩ := h
  exact WP.mono (short_guard hl) fun t ⟨⟨⟨⟨_, _, hm⟩, k⟩, hy⟩, he⟩ => ⟨⟨o, hl.keep k hm hy⟩, he⟩

theorem search_short_ct : RelCT isa (Two SearchAt) short (fun _ _ => True) := by
  unfold short
  refine RelCT.seq (two_piece [.s0] (fun q _ _ h₁ h₂ => search_any_pins q.inputs _ _ h₁.any h₂.any)
    (by taint_decide) short_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact leaf SearchPoint.inputs (fun _ _ h => h.1.1.any) search_exhausted_ct
  · exact leaf SearchPoint.inputs (fun _ _ h => h.1.1.any) search_request_ct

/-- Past the candidate's octets, at the point: whether its status was 2. -/
def Reject3 (q : SearchPoint) (t : State) : Prop :=
  t.gpr .s0 = q.inputs.F ∧ isa.eval (.zero .t5) t = some (decide (q.status = 2))

private theorem advance_ready (q : SearchPoint) (s : State)
    (h : GuardCT q s ∧ isa.eval (.zero .t4) s = some false ∧ isa.eval (.zero .t1) s = some false ∧
      isa.eval (.zero .t2) s = some false) :
    WP isa (.block advance) s (Reject3 q) := by
  obtain ⟨⟨hc, h9, h10, -⟩, -, -, -⟩ := h
  have hst := status_lt' q hc
  obtain ⟨o, hl, -, -, -⟩ := hc
  refine WP.mono (advance_ok hl h10) fun t ⟨⟨_, he⟩, kt⟩ => ⟨(kt.gpr .s0 (by decide)).trans hl.s0, ?_⟩
  rw [he, h9]
  have : ∀ st < 4, ((BitVec.ofNat 64 st - BitVec.ofNat 64 2) == 0) = decide (st = 2) := by decide
  rw [this _ hst]

theorem search_reject_ct : RelCT isa (Two fun q s => GuardCT q s ∧ isa.eval (.zero .t4) s = some false ∧
    isa.eval (.zero .t1) s = some false) reject (fun _ _ => True) := by
  unfold reject
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.1.2.2.1, h₂.1.2.2.1]) ?_ ?_
  · exact leaf SearchPoint.inputs (fun _ _ h => h.1.1.1.at.any) search_exhausted_ct
  · refine RelCT.seq (two_piece (Ψ := Reject3) [.s0] (fun q _ _ h₁ h₂ =>
      cand_ct_pins q _ _ h₁.1.1.1 h₂.1.1.1) (by taint_decide)
      (fun q s h => advance_ready q s ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩)) ?_
    refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
    · exact two_taint [] no_pins (by taint_decide)
    · exact two_taint [.s0] (fun _ _ _ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr
        subst r
        exact h₁.1.1.trans h₂.1.1.symm) (by taint_decide)

theorem search_classify_ct : RelCT isa (Two CandCT) classify (fun _ _ => True) := by
  unfold classify
  change RelCT isa (Two CandCT) (.seq (.block ([.shift .sll .d .t1 .a0 32, .shift .srl .d .t1 .t1 32, ldf .t3 7] ++
    [.load .d .t2 .t3 0, .addi .t4 .t1 (-1)])) _) _
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (two_piece [.s0] cand_ct_pins (by taint_decide) head_first)
    (two_piece [.t3] head_pins (by taint_decide) head_second))) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm)
    (leaf SearchPoint.inputs (fun _ _ h => h.1.1.at.any) search_accept_ct) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.1.2.1, h₂.1.2.1]) ?_ ?_
  · exact (search_short_ct.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.1.1.1.at, h₂.1.1.1.at, hsp⟩)
      fun _ _ h => h)
  · exact (search_reject_ct.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, ⟨h₁.1.1, h₁.1.2, h₁.2⟩,
      ⟨h₂.1.1, h₂.1.2, h₂.2⟩, hsp⟩) fun _ _ h => h)

/-! ## The candidate's call -/

/-- Allocating and freeing a frame leaks nothing, as in the DSA proofs
(`Proof/Dsa/RISCV64/GKCTSample.lean`). -/
theorem relCT_alloc {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocd bytes s ∧ b = allocd bytes t) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocd bytes a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := alloc_eq ps
      have eb := alloc_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      exact ⟨rfl, trivial⟩

/-- The candidate's contract, with what its timing may depend on. -/
def candKP : Contract isa where
  pre s := CIn s ∧ TabOk s
  post := candK.post
  pub s₁ s₂ := pubOf s₁ = pubOf s₂ ∧ s₁.sp = s₂.sp

theorem cand_constantTime (c : Cand) : ConstantTime isa candKP.pre candKP.pub c.code :=
  RelCT.constantTime (c.ct.mono (fun s₁ _ ⟨⟨c₁, t₁⟩, ⟨c₂, t₂⟩, hp, hsp⟩ =>
    ⟨(pubOf s₁, s₁.sp), ⟨⟨c₁, t₁, rfl⟩, rfl⟩, ⟨⟨c₂, t₂, hp.symm⟩, hsp.symm⟩, hsp⟩) fun _ _ h => h)

/-- A loop state at the point that calls a candidate. -/
def ReadyCT (q : SearchPoint) (s : State) : Prop := SearchCTL q s ∧ q.remaining ≠ 0

def AllocCT (q : SearchPoint) (u : State) : Prop := ∃ s, ReadyCT q s ∧ u = allocd 32 s

theorem alloc_pins : Pins AllocCT [.s0] := by
  rintro q _ _ ⟨a, ⟨h₁, _⟩, rfl⟩ ⟨b, ⟨h₂, _⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact search_ctl_pins q _ _ h₁ h₂ .s0 (by simp)

/-- The candidate's entry, before the call. -/
def CallCT (q : SearchPoint) (v : State) : Prop :=
  ∃ o s, SearchLive q.inputs o q.used q.remaining s ∧ (tailOf q.inputs o q.used q.remaining).trace = q.trace ∧
    q.remaining ≠ 0 ∧ tabAddr o = q.tab ∧ CallRegs q.inputs q.used v ∧ v.mem = callMem q.inputs q.used s ∧
    Keep argRegsW (allocd 32 s) v ∧ v.sp = callSp q.inputs ∧ v.syms = s.syms

private theorem arguments_ready (q : SearchPoint) (u : State) (h : AllocCT q u) :
    WP isa (.block arguments) u (CallCT q) := by
  obtain ⟨s, ⟨⟨original, h, ht, htab⟩, hr⟩, rfl⟩ := h
  exact WP.mono (search_arguments_ok h) fun _ ⟨⟨⟨ha, hm⟩, k⟩, hsp, hy⟩ =>
    ⟨original, s, h, ht, hr, htab, ha, hm, k, hsp, hy⟩

/-- What the candidate's timing may depend on, from the point. -/
theorem call_pubOf {q : SearchPoint} {v : State} (h : CallCT q v) :
    pubOf (callState q.inputs q.used q.tab v) =
      ⟨[q.inputs.op, BitVec.ofNat 64 q.inputs.len, q.inputs.up, q.inputs.ep, BitVec.ofNat 64 q.inputs.elen,
        q.inputs.pp, BitVec.ofNat 64 q.inputs.plen, q.inputs.rp + BitVec.ofNat 64 q.used],
        [BitVec.ofNat 64 (q.inputs.randLen - q.used), q.inputs.B, BitVec.ofNat 64 (q.inputs.Z / 8)],
        q.tab, q.inputs.eB, q.leak⟩ := by
  obtain ⟨o, s, hl, ht, hr, htab, ha, hm', kv, hu, hyv⟩ := h
  have hf := hl.callFacts
  have hy : v.syms = o.syms := hyv.trans hl.syms
  obtain ⟨he, hpb, hrand⟩ := call_inputs hl hm'
  obtain ⟨a0, a1, a2⟩ := call_args hu hm'
  obtain ⟨r3, r4, r5, r6, r7, r8, r9, r10⟩ := ha
  have tl := toNat_ofNat_lt hf.len64
  have te : (BitVec.ofNat 64 q.inputs.elen).toNat = q.inputs.elen := toNat_ofNat_lt (by have := hf.e8; omega)
  have tp := toNat_ofNat_lt hf.plen64
  have tr : (BitVec.ofNat 64 (q.inputs.randLen - q.used)).toNat = q.inputs.randLen - q.used :=
    toNat_ofNat_lt (by have := hf.rand64; omega)
  simp only [pubOf, argRegs, List.map_cons, List.map_nil, Cand.stackArgs_three, Cand.eB, Cand.pB, Cand.rB,
    Cand.oL, Cand.rL, call_gpr (by decide : Reg.a0 ∉ linkRegs), call_gpr (by decide : Reg.a1 ∉ linkRegs),
    call_gpr (by decide : Reg.a2 ∉ linkRegs), call_gpr (by decide : Reg.a3 ∉ linkRegs),
    call_gpr (by decide : Reg.a4 ∉ linkRegs), call_gpr (by decide : Reg.a5 ∉ linkRegs),
    call_gpr (by decide : Reg.a6 ∉ linkRegs), call_gpr (by decide : Reg.a7 ∉ linkRegs), call_stackArg,
    call_syms, hy, a0, a1, a2, r3, r4, r5, r6, r7, r8, r9, r10, tl, te, tp, tr, State.withRegions_mem,
    State.callEntry_mem, he, hpb, hrand]
  rw [SearchCTL.leak ht hr, ← htab]

theorem search_call_ct (c : Cand) : RelCT isa (Two CallCT) c.call (fun _ _ => True) := by
  refine RelCT.callEx (k := candKP) (fun s' ⟨h₁, h₂⟩ => c.correct s' h₁ h₂) (cand_constantTime c)
    fun v₁ v₂ ⟨q, h₁, h₂, _⟩ => ?_
  have hp₁ := call_pubOf h₁
  have hp₂ := call_pubOf h₂
  have pre (v : State) (h : CallCT q v) :
      CIn (callState q.inputs q.used q.tab v) ∧ TabOk (callState q.inputs q.used q.tab v) ∧
      Covers (callReads q.inputs q.used q.tab ++ callWrites q.inputs) (v.rd ++ v.wr) ∧
      Covers (callWrites q.inputs) v.wr ∧ v.sp = callSp q.inputs := by
    obtain ⟨o, s, hl, -, -, htab, ha, hm', kv, hu, hyv⟩ := h
    have hy : v.syms = o.syms := hyv.trans hl.syms
    have krd : v.rd = (allocd 32 s).rd := kv.2.1
    have kwr : v.wr = (allocd 32 s).wr := kv.2.2
    rw [← htab]
    exact ⟨call_cin hl.callFacts hu ha hm', call_tab hl hm' hy hu ha, call_covers_reads hl krd kwr,
      call_covers_writes hl kwr, hu⟩
  obtain ⟨c₁, t₁, cr₁, cw₁, u₁⟩ := pre v₁ h₁
  obtain ⟨c₂, t₂, cr₂, cw₂, u₂⟩ := pre v₂ h₂
  refine ⟨_, _, _, _, ⟨c₁, t₁⟩, ⟨c₂, t₂⟩, ⟨hp₁.trans hp₂.symm, ?_⟩, cr₁, cw₁, cr₂, cw₂⟩
  simp only [State.withRegions_sp, State.callEntry_sp, u₁, u₂]

theorem search_candidate_run_ct (c : Cand) :
    RelCT isa (Two ReadyCT) (candidateRun c.call) (fun _ _ => True) := by
  unfold candidateRun
  apply relCT_alloc
  refine (RelCT.seq (two_piece [.s0] alloc_pins (by taint_decide) arguments_ready)
    (search_call_ct c)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocd, hsp]⟩

private theorem cand_ready (c : Cand) (q : SearchPoint) (s : State) (h : ReadyCT q s) :
    WP isa (candidateRun c.call) s (CandCT q) :=
  let ⟨⟨o, hl, ht, _⟩, hr⟩ := h
  WP.mono (search_candidate_run c hl) fun _ ⟨hl', hc⟩ => ⟨o, hl', hc, ht, hr⟩

/-! ## An iteration -/

/-- Whether the search goes on past the point's candidate. -/
def SearchPoint.continues (q : SearchPoint) : Prop :=
  q.remaining ≠ 0 ∧ (q.status = 2 ∨ q.status = 3) ∧ q.cand ≠ 0

/-- The point past the candidate, when the search goes on. -/
def SearchPoint.next (q : SearchPoint) : SearchPoint :=
  ⟨q.inputs, q.used + q.cand, if q.status = 2 then q.remaining else q.remaining - 1,
    q.trace.drop (q.leak.length + 1), q.tab⟩

theorem continues_iff {q : SearchPoint} {original s : State}
    (hl : SearchLive q.inputs original q.used q.remaining s)
    (ht : (tailOf q.inputs original q.used q.remaining).trace = q.trace) :
    Continues q.inputs original q.used q.remaining ↔ q.continues := by
  by_cases hr : q.remaining = 0
  · simp [Continues, SearchPoint.continues, hr]
  · rw [Continues, SearchPoint.continues, SearchCTL.status ht hr, SearchCTL.used hl ht hr]

theorem ctl_next {q : SearchPoint} {original s t : State} {final : PrimeSearchResult}
    (hl : SearchLive q.inputs original q.used q.remaining s)
    (ht : (tailOf q.inputs original q.used q.remaining).trace = q.trace) (htab : tabAddr original = q.tab)
    (hc : ContinuePost q.inputs original final q.used q.remaining t) : SearchCTL q.next t := by
  obtain ⟨hr, u, k, -, hi, hu, hk, htail⟩ := hc
  have hs := SearchCTL.status ht hr
  have hcu := SearchCTL.used hl ht hr
  have hu' : q.next.used = u := by simp only [SearchPoint.next]; omega
  have hk' : q.next.remaining = k := by
    simp only [SearchPoint.next]
    rcases hk with ⟨rfl, h2⟩ | ⟨rfl, h3⟩
    · rw [hs] at h2; simp [h2]
    · rw [hs] at h3; simp [h3]
  refine ⟨original, ?_, ?_, htab⟩
  · rw [hu', hk']; exact hi.1
  · have htr := congrArg Spec.Entropy.Result.trace htail
    rw [ht] at htr
    simp only [Spec.Entropy.Result.consume] at htr
    have hL := SearchCTL.leak ht hr
    show _ = q.trace.drop (q.leak.length + 1)
    rw [hu', hk', htr, VG.Proof.RsaKeyGen.Search.entry, hL]
    simp
    rfl

/-- After an iteration: the next point and the loop's condition, or its end. -/
def SearchCTStep (q : SearchPoint) (t : State) : Prop :=
  (q.continues ∧ isa.eval (.zero .t1) t = some true ∧ SearchCTL q.next t) ∨
    (¬q.continues ∧ isa.eval (.zero .t1) t = some false)

theorem search_ct_step (c : Cand) (q : SearchPoint) (s : State) (h : SearchCTL q s) :
    WP isa (iteration c.call) s (SearchCTStep q) := by
  obtain ⟨o, hl, ht, htab⟩ := h
  refine WP.mono (search_iteration c (final := (tailOf q.inputs o q.used q.remaining).consume q.used [])
    ⟨hl, [], rfl⟩) fun t hs => ?_
  rcases hs with ⟨he, hc⟩ | ⟨he, hn, -⟩
  · exact .inl ⟨(continues_iff hl ht).mp hc.continues, he, ctl_next hl ht htab hc⟩
  · exact .inr ⟨fun h => hn ((continues_iff hl ht).mpr h), he⟩

/-- The loop state with the guard's flag. -/
def GuardK (q : SearchPoint) (s : State) : Prop :=
  SearchCTL q s ∧ isa.eval (.zero .t1) s = some (decide (q.remaining = 0))

private theorem guard_ready (q : SearchPoint) (s : State) (h : SearchCTL q s) :
    WP isa (.block [ldf .t1 0]) s (GuardK q) := by
  obtain ⟨o, hl, ht, htab⟩ := h
  exact WP.mono (iter_guard hl) fun t ⟨⟨⟨he, hm⟩, k⟩, hy⟩ => ⟨⟨o, hl.keep k hm hy, ht, htab⟩, he⟩

/-- The branch leaves `s0` at the frame. -/
theorem search_branch (c : Cand) {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    {used remaining : Nat} (h : SearchIter p original final used remaining s)
    (he : isa.eval (.zero .t1) s = some (decide (remaining = 0))) :
    WP isa (.ite (.zero .t1) exhausted (.seq (candidateRun c.call) classify)) s
      fun t => t.gpr .s0 = p.F := by
  refine WP.ite _ he (fun hz => ?_) (fun hz => ?_)
  · have hz := of_decide_eq_true hz
    subst hz
    obtain ⟨hl, tr, hfinal⟩ := h
    unfold tailOf at hfinal
    rw [VG.Proof.RsaKeyGen.Search.search_zero] at hfinal
    exact WP.mono (search_exhausted hl (result := final) (by rw [hfinal]; rfl)) fun t hd => hd.s0
  · have hz := of_decide_eq_false hz
    refine WP.seq (WP.mono (search_candidate_run c h.1) fun t ⟨ht, hc⟩ => ?_)
    refine WP.mono (search_classify ⟨ht, h.2⟩ hc hz) fun _ hp => ?_
    rcases hp with ⟨-, -, _, _, -, ⟨hi, -⟩, -⟩ | ⟨-, -, hd⟩
    exacts [hi.s0, hd.s0]

private theorem ready_of_guard {q : SearchPoint} {s : State}
    (h : GuardK q s ∧ isa.eval (.zero .t1) s = some false) : ReadyCT q s := by
  refine ⟨h.1.1, fun h0 => ?_⟩
  have := h.1.2.symm.trans h.2
  simp [h0] at this

private theorem branch_ct (c : Cand) :
    RelCT isa (Two GuardK) (.ite (.zero .t1) exhausted (.seq (candidateRun c.call) classify))
      (fun _ _ => True) := by
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact leaf SearchPoint.inputs (fun _ _ h => h.1.1.any) search_exhausted_ct
  · refine RelCT.seq ((two_post (search_candidate_run_ct c) (cand_ready c)).mono
      (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, ready_of_guard h₁, ready_of_guard h₂, hsp⟩) fun _ _ h => h) ?_
    exact search_classify_ct

theorem search_iteration_ct (c : Cand) :
    RelCT isa (Two SearchCTL) (iteration c.call) (fun _ _ => True) := by
  unfold iteration
  refine RelCT.seq (two_piece [.s0] search_ctl_pins (by taint_decide) guard_ready) ?_
  exact RelCT.seq (two_post (branch_ct c) (Ψ := fun q t => t.gpr .s0 = q.inputs.F)
      fun q u h => let ⟨⟨_, hl, _⟩, he⟩ := h; search_branch c ⟨hl, [], rfl⟩ he)
    (two_taint [.s0] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact h₁.trans h₂.symm) (by taint_decide))

/-! ## The loop -/

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q : SearchPoint, n = q.inputs.randLen - q.used + 1 ∧ SearchCTL q s ∧ SearchCTL q t ∧ s.sp = t.sp

private theorem iteration_pair (c : Cand) (n : Nat) :
    RelCT isa (LoopPair n) (iteration c.call) fun s t =>
      isa.eval (.zero .t1) s = isa.eval (.zero .t1) t ∧
      (isa.eval (.zero .t1) s = some false → True) ∧
      (isa.eval (.zero .t1) s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (q : SearchPoint) (s : State) (h : n = q.inputs.randLen - q.used + 1 ∧ SearchCTL q s) :
      WP isa (iteration c.call) s fun t => n = q.inputs.randLen - q.used + 1 ∧ SearchCTStep q t :=
    WP.mono (search_ct_step c q s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((search_iteration_ct c).mono
    (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.2, h₂.2, hsp⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂, hsp⟩ => ⟨q, ⟨hn, h₁⟩, ⟨hn, h₂⟩, hsp⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, ⟨_, h₂⟩, -⟩
  rcases h₁ with ⟨hb, e₁, c₁⟩ | ⟨hb, e₁⟩ <;> rcases h₂ with ⟨hb', e₂, c₂⟩ | ⟨hb', e₂⟩
  · refine ⟨e₁.trans e₂.symm, fun _ => trivial, fun _ => ⟨_, ?_, q.next, rfl, c₁, c₂, ?_⟩⟩
    · obtain ⟨o, hl, _⟩ := c₁
      have hle := hl.used_le
      have hcand := hb.2.2
      simp only [SearchPoint.next] at hle ⊢
      omega
    · obtain ⟨_, hl₁, _⟩ := c₁
      obtain ⟨_, hl₂, _⟩ := c₂
      exact hl₁.sp.trans hl₂.sp.symm
  · exact absurd hb hb'
  · exact absurd hb' hb
  · exact ⟨e₁.trans e₂.symm, fun _ => trivial, fun h => by rw [e₁] at h; cases h⟩

theorem search_loop_ct (c : Cand) :
    RelCT isa (Two SearchCTL) (.loop (iteration c.call) (.zero .t1)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht, hsp⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration c.call) (c := .zero .t1)
    (Q := fun _ _ => True) LoopPair (iteration_pair c) (q.inputs.randLen - q.used + 1)
    _ _ _ _ _ _ ⟨q, rfl, hs, ht, hsp⟩ he₁ he₂

/-! ## The frame saving `ra` -/

/-- A frame saving `ra` around a body proven with the permissions outside
it (as `WP.frameRegAny` runs it) leaks what the body does there, as on
PPC64LE (`relCT_pushR0`). -/
theorem relCT_pushRa {body : Prog isa} {P : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp)
    (hwp : ∀ a b, P a b → (∃ t s', Exec isa body (framed .ra a) t s') ∧
      (∃ t s', Exec isa body (framed .ra b) t s'))
    (hct : RelCT isa (fun x y => ∃ a b, P a b ∧ x = framed .ra a ∧ y = framed .ra b) body
      fun _ _ => True) :
    RelCT isa P (.frame (.push .ra) body (.pop .ra)) fun a b => a.sp = b.sp := by
  refine RelCT.frame (R := fun _ _ => True) hsp ?_
  have widen : ∀ a, ∀ {t s'}, Exec isa body (framed .ra a) t s' →
      Exec isa body (pushed .ra a) t (s'.withRegions a.rd (⟨a.sp - 16, 16⟩ :: a.wr)) := by
    intro a t s' e
    have := Exec.widen e (rd := a.rd) (wr := ⟨a.sp - 16, 16⟩ :: a.wr)
      (Covers.of_mem fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact List.mem_append_left _ hr
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr))
      (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr)
    exact this
  rintro x y tx ty x' y' ⟨a, b, hab, rfl, rfl⟩ ex ey
  obtain ⟨⟨ta, sa, ea⟩, ⟨tb, sb, eb⟩⟩ := hwp a b hab
  obtain ⟨rfl, -⟩ := Exec.det ex (widen a ea)
  obtain ⟨rfl, -⟩ := Exec.det ey (widen b eb)
  exact ⟨(hct _ _ _ _ _ _ ⟨a, b, hab, rfl, rfl⟩ ea eb).1, trivial⟩

/-! ## Entry and return -/

/-- A run's entry, with its public descriptor, its result's trace and the
table's address. -/
def SearchStart (a : SearchPublic × List Nat × Addr) (s : State) : Prop :=
  SearchInput a.1 s ∧ (searchResult s).trace = a.2.1 ∧ tabAddr s = a.2.2

/-- A run's entry, past the frame's allocation. -/
def AllocStart (a : SearchPublic × List Nat × Addr) (u : State) : Prop :=
  ∃ s, SearchStart a s ∧ u = allocd 160 s

/-- The frame's base and the state's pointer, past the loads of the stack
arguments. -/
def LoadPins (p : SearchPublic) (t : State) : Prop := t.gpr .t6 = p.F ∧ t.gpr .t3 = p.stp

private theorem load_pins (a : SearchPublic × List Nat × Addr) (u : State) (h : AllocStart a u) :
    WP isa (.block (entry.take 5)) u (LoadPins a.1) := by
  obtain ⟨s, ⟨hi, -⟩, rfl⟩ := h
  have hsp := alloc_sp hi
  have hF : a.1.F = s.sp - BitVec.ofNat 64 160 := by show a.1.sp - _ = _; rw [hi.sp_eq]
  have ha (k : Nat) (hk : k < 4) :
      InRegions ((allocd 160 s).rd ++ (allocd 160 s).wr) (a.1.F + BitVec.ofNat 64 (160 + 8 * k)) 8 := by
    rw [hF, arg_addr]
    obtain ⟨r, hr, hc⟩ := input_args hi k hk
    refine ⟨r, ?_, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hv : s.mem.readW (a.1.F + BitVec.ofNat 64 (160 + 8 * 3)) 64 = a.1.stp := by
    rw [hF, arg_addr, ← hi.2]; rfl
  have hal (k : Nat) (hk : k < 4) : (a.1.F + BitVec.ofNat 64 (160 + 8 * k)).toNat % 8 = 0 := by
    rw [hF, arg_addr]
    have h16 : s.sp.toNat % 16 = 0 := by have := hi.sp16; rwa [hi.sp_eq] at this
    have ht : s.sp.toNat + 32 ≤ 2 ^ 64 := by have := hi.top; rwa [hi.sp_eq] at this
    have e : (s.sp + BitVec.ofNat 64 (8 * k)).toNat = s.sp.toNat + 8 * k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [e]; omega
  have a0 := ha 0 (by decide)
  have a1 := ha 1 (by decide)
  have a2 := ha 2 (by decide)
  have a3 := ha 3 (by decide)
  have l0 := hal 0 (by decide)
  have l1 := hal 1 (by decide)
  have l2 := hal 2 (by decide)
  have l3 := hal 3 (by decide)
  have hmem : (allocd 160 s).mem = s.mem := rfl
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at a0 a1 a2 a3 l0 l1 l2 l3 hv
  have ea : ∀ t : State, exec (.addSp .t6 0) t = some (t.write .t6 (t.sp + BitVec.ofNat 64 0)) := by
    intro t; simp [exec]
  have hz : a.1.F + BitVec.ofNat 64 0 = a.1.F := BitVec.add_zero _
  unfold entry LoadPins
  simp only [List.take_succ_cons, List.take_zero]
  brun [ea, hsp, hz, hmem, a0, a1, a2, a3, l0, l1, l2, l3, hv]

/-- After the entry: the frame's words written. -/
def Entered (a : SearchPublic × List Nat × Addr) (t : State) : Prop :=
  ∃ s, SearchStart a s ∧ t.gpr .s0 = a.1.F ∧ t.mem = writeFrame s.mem a.1.F (entryValues s) ∧
    Keep entryRegs (allocd 160 s) t ∧ t.sp = a.1.F ∧ t.syms = s.syms

private theorem entry_ready (a : SearchPublic × List Nat × Addr) (u : State) (h : AllocStart a u) :
    WP isa (.block entry) u (Entered a) := by
  obtain ⟨s, hs, rfl⟩ := h
  exact VG.RISCV64.WP.mono_syms (entry_ok hs.1) fun _ ⟨⟨⟨hx, hm⟩, k⟩, hsp⟩ hy => ⟨s, hs, hx, hm, k, hsp, hy⟩

theorem search_entry_ct : RelCT isa (Two AllocStart) (.block entry) (fun _ _ => True) := by
  change RelCT isa (Two AllocStart) (.block (entry.take 5 ++ entry.drop 5)) _
  refine RelCT.block_append (RelCT.seq (two_piece [] no_pins (by taint_decide) load_pins) ?_)
  exact two_taint [.t6, .t3] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

theorem tail_initial {p : SearchPublic} {s : State} (h : SearchInput p s) :
    tailOf p s 0 p.remaining = searchResult s := by
  rw [← h.2]
  simp only [searchResult, tailOf, searchOfState, List.drop_zero]

/-- The point the loop starts at. -/
def initialPoint (a : SearchPublic × List Nat × Addr) : SearchPoint := ⟨a.1, 0, a.1.remaining, a.2.1, a.2.2⟩

private theorem entered_ctl {a : SearchPublic × List Nat × Addr} {t : State} (h : Entered a t) :
    SearchCTL (initialPoint a) (framed .ra t) := by
  obtain ⟨s, ⟨hi, ht, htab⟩, hx, hm, k, hsp, hy⟩ := h
  exact ⟨s, search_start hi hx hm k hsp hy, by
    show (tailOf a.1 s 0 a.1.remaining).trace = a.2.1
    rw [tail_initial hi, ht], htab⟩

/-- A loop's end. -/
def DoneCT (p : SearchPublic) (s : State) : Prop := ∃ original r, SearchDone p original r s

private theorem frame_ct (c : Cand) : RelCT isa (Two Entered)
    (.frame (.push .ra) (.loop (iteration c.call) (.zero .t1)) (.pop .ra)) fun a b => a.sp = b.sp := by
  refine relCT_pushRa (fun _ _ ⟨_, _, _, hsp⟩ => hsp) (fun x y ⟨a, h₁, h₂, _⟩ => ?_) ?_
  · obtain ⟨o₁, hl₁, -⟩ := entered_ctl h₁
    obtain ⟨o₂, hl₂, -⟩ := entered_ctl h₂
    obtain ⟨t, s', e, -⟩ := search_loop c (final := (tailOf a.1 o₁ 0 a.1.remaining).consume 0 [])
      ⟨hl₁, [], rfl⟩
    obtain ⟨t', s'', e', -⟩ := search_loop c (final := (tailOf a.1 o₂ 0 a.1.remaining).consume 0 [])
      ⟨hl₂, [], rfl⟩
    exact ⟨⟨t, s', e⟩, ⟨t', s'', e'⟩⟩
  · refine (search_loop_ct c).mono ?_ fun _ _ h => h
    rintro _ _ ⟨x, y, ⟨a, h₁, h₂, hsp⟩, rfl, rfl⟩
    exact ⟨initialPoint a, entered_ctl h₁, entered_ctl h₂, by simp only [framed, hsp]⟩

private theorem search_ct (c : Cand) : RelCT isa (Two Entered) (search c.call) (fun _ _ => True) := by
  unfold search
  exact (frame_ct c).mono (fun _ _ h => h) fun _ _ _ => trivial

private theorem search_ready (c : Cand) (a : SearchPublic × List Nat × Addr) (t : State) (h : Entered a t) :
    WP isa (search c.call) t (DoneCT a.1) := by
  obtain ⟨s, ⟨hi, -⟩, hx, hm, k, hsp, hy⟩ := h
  exact WP.mono (search_body c hi hx hm k hsp hy) fun _ ⟨hd, _, _⟩ => ⟨s, _, hd⟩

private theorem finish_pointers (p : SearchPublic) (s : State) (h : DoneCT p s) :
    WP isa (.block (finish.take 9)) s fun t => t.gpr .t0 = p.stp ∧ t.gpr .t5 = p.up := by
  obtain ⟨o, r, h⟩ := h
  have scr := h.input.frame_scr h.wr
  have hl : ∀ d, d + 8 ≤ 160 → InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 d) 8 := fun d hd =>
    let ⟨r, hr, hc⟩ := scr.st (n := 8) hd; ⟨r, List.mem_append_right _ hr, hc⟩
  have hal : ∀ d, d + 8 ≤ 160 → d % 8 = 0 → (p.F + BitVec.ofNat 64 d).toNat % 8 = 0 :=
    fun _ hd h8 => scr.al8 hd h8
  have w7 := h.usedPtr
  have w18 := h.stp
  simp only [Bignum.word, off, Nat.reduceMul] at w7 w18
  unfold finish
  simp only [List.take_succ_cons, List.take_zero]
  brun [ldf, h.s0, hl 0 (by decide), hl 8 (by decide), hl 16 (by decide),
    hl 24 (by decide), hl 32 (by decide), hl 56 (by decide), hl 128 (by decide), hl 136 (by decide),
    hl 144 (by decide), hal 0 (by decide) (by decide), hal 8 (by decide) (by decide),
    hal 16 (by decide) (by decide), hal 24 (by decide) (by decide), hal 32 (by decide) (by decide),
    hal 56 (by decide) (by decide), hal 128 (by decide) (by decide), hal 136 (by decide) (by decide),
    hal 144 (by decide) (by decide), w7, w18]

theorem search_finish_ct : RelCT isa (Two DoneCT) (.block finish) (fun _ _ => True) := by
  change RelCT isa (Two DoneCT) (.block (finish.take 9 ++ finish.drop 9)) _
  refine RelCT.block_append (RelCT.seq (two_piece [.s0] ?_ (by taint_decide) finish_pointers) ?_)
  · intro p s t ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.s0.trans h₂.s0.symm
  · exact two_taint [.t0, .t5] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

/-! ## The whole search -/

theorem search_code_ct (c : Cand) :
    RelCT isa (Two SearchStart) (code c.call) (fun _ _ => True) := by
  unfold code
  apply relCT_alloc
  refine (RelCT.seq (two_post search_entry_ct entry_ready)
    (RelCT.seq (two_post (search_ct c) (search_ready c))
      (two_map Prod.fst (fun _ _ h => h) search_finish_ct))).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨a, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨a, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocd, hsp]⟩

private theorem search_public_descriptor {s t : State} (h : searchPub s t) : searchOfState s = searchOfState t := by
  obtain ⟨hsp, r3, r4, r5, r6, r7, r8, r9, r10, ha, he, hw, -⟩ := h
  change [word s.mem (stackArg s 3) 0, word s.mem (stackArg s 3) 8, word s.mem (stackArg s 3) 16,
    word s.mem (stackArg s 3) 24] = [word t.mem (stackArg t 3) 0, word t.mem (stackArg t 3) 8,
      word t.mem (stackArg t 3) 16, word t.mem (stackArg t 3) 24] at hw
  have h0 : s.mem.readW (stackArg s 3) 64 = t.mem.readW (stackArg t 3) 64 := by
    simpa only [Bignum.word, off, BitVec.add_zero] using (List.cons.inj hw).1
  unfold searchOfState
  rw [searchRemaining, searchRemaining, searchLen, searchLen, h0, he, hsp, r3, r4, r5, r6, r7, r8, r9, r10,
    ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide)]

theorem search_constantTime (c : Cand) :
    ConstantTime isa searchContract.pre searchContract.pub (code c.call) := by
  refine RelCT.constantTime ((search_code_ct c).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  have hd := search_public_descriptor hp
  obtain ⟨hsp, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htr, hsy⟩ := hp
  exact ⟨(searchOfState s, (searchResult s).trace, tabAddr s), ⟨⟨hs, rfl⟩, rfl, rfl⟩,
    ⟨⟨ht, hd.symm⟩, htr.symm, hsy.symm⟩, hsp⟩

end VG.Proof.RsaKeyGen.RISCV64.Search
