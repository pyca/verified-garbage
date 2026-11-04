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

/-! ## The candidate's call -/

/-- A loop state at the point that calls a candidate. -/
def ReadyCT (q : SearchPoint) (s : State) : Prop := SearchCTL q s ∧ q.remaining ≠ 0

/-- The candidate's entry, before the call. -/
def CallCT (q : SearchPoint) (u : State) : Prop :=
  ∃ original s, SearchLive q.inputs original q.used q.remaining s ∧
    (tailOf q.inputs original q.used q.remaining).trace = q.trace ∧ q.remaining ≠ 0 ∧
    CallRegs q.inputs q.used u ∧ u.mem = writeFrame s.mem (callSp q.inputs) (callValues q.inputs q.used) ∧
    Keep argRegsW (allocated 32 s) u

theorem CallCT.sp {q : SearchPoint} {u : State} (h : CallCT q u) : u.sp = callSp q.inputs := by
  obtain ⟨o, s, hl, -, -, -, -, k⟩ := h
  exact k.sp.trans (alloc_call_sp hl)

/-- What the candidate's timing may depend on, from the point. -/
theorem call_leak {q : SearchPoint} {u : State} (h : CallCT q u) :
    VG.Proof.RsaKeyGen.AArch64.candLeak (callState q.inputs q.used u) =
      q.inputs.eB.map (·.toNat) ++ q.leak := by
  have hu := h.sp
  obtain ⟨o, s, hl, ht, hr, ha, hm, -⟩ := h
  have hf := hl.callFacts
  obtain ⟨he, hpb, hrand⟩ := call_inputs hl hm
  obtain ⟨a0, -, -⟩ := call_args hu hm
  obtain ⟨-, r1, -, r3, r4, r5, r6, r7⟩ := ha
  have tl := toNat_ofNat_lt hf.len64
  have te : (BitVec.ofNat 64 q.inputs.elen).toNat = q.inputs.elen := toNat_ofNat_lt (by have := hf.e8; omega)
  have tp := toNat_ofNat_lt hf.plen64
  have tr : (BitVec.ofNat 64 (q.inputs.randLen - q.used)).toNat = q.inputs.randLen - q.used :=
    toNat_ofNat_lt (by have := hf.rand64; omega)
  simp only [VG.Proof.RsaKeyGen.AArch64.candLeak, call_gpr (by decide : Reg.x1 ∉ linkRegs),
    call_gpr (by decide : Reg.x3 ∉ linkRegs), call_gpr (by decide : Reg.x4 ∉ linkRegs),
    call_gpr (by decide : Reg.x5 ∉ linkRegs), call_gpr (by decide : Reg.x6 ∉ linkRegs),
    call_gpr (by decide : Reg.x7 ∉ linkRegs), call_stackArg, r1, r3, r4, r5, r6, r7, a0, tl, te, tp, tr,
    State.withRegions_mem, State.callEntry_mem, he, hpb, hrand]
  rw [SearchCTL.leak ht hr]

theorem search_call_ct (c : Cand) : RelCT isa (Two CallCT) c.call (fun _ _ => True) := by
  refine RelCT.callEx c.correct c.ct fun u₁ u₂ ⟨q, h₁, h₂, _⟩ => ?_
  have hu₁ := h₁.sp
  have hu₂ := h₂.sp
  have hl₁ := call_leak h₁
  have hl₂ := call_leak h₂
  obtain ⟨o₁, s₁, l₁, -, -, a₁, m₁, k₁⟩ := h₁
  obtain ⟨o₂, s₂, l₂, -, -, a₂, m₂, k₂⟩ := h₂
  obtain ⟨b0, b1, b2⟩ := call_args hu₁ m₁
  obtain ⟨c0, c1, c2⟩ := call_args hu₂ m₂
  refine ⟨callReads q.inputs q.used, callWrites q.inputs, callReads q.inputs q.used, callWrites q.inputs,
    call_cand_pre l₁.callFacts hu₁ a₁ m₁, call_cand_pre l₂.callFacts hu₂ a₂ m₂, ?_,
    call_covers_reads l₁ k₁.rd k₁.wr, call_covers_writes l₁ k₁.wr,
    call_covers_reads l₂ k₂.rd k₂.wr, call_covers_writes l₂ k₂.wr⟩
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7⟩ := a₁
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := a₂
  refine ⟨fun r hr => ?_, ?_, fun i hi => ?_, hl₁.trans hl₂.symm⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [call_gpr (by decide), call_gpr (by decide)]
    exacts [d0.trans e0.symm, d1.trans e1.symm, d2.trans e2.symm, d3.trans e3.symm, d4.trans e4.symm,
      d5.trans e5.symm, d6.trans e6.symm, d7.trans e7.symm]
  · simp only [State.withRegions_sp, State.callEntry_sp, hu₁, hu₂]
  · rw [call_stackArg, call_stackArg]
    match i, hi with
    | 0, _ => exact b0.trans c0.symm
    | 1, _ => exact b1.trans c1.symm
    | 2, _ => exact b2.trans c2.symm

def AllocCT (q : SearchPoint) (u : State) : Prop := ∃ s, ReadyCT q s ∧ u = allocated 32 s

theorem alloc_pins : Pins AllocCT [.x19] := by
  rintro q _ _ ⟨a, ⟨h₁, _⟩, rfl⟩ ⟨b, ⟨h₂, _⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact search_ctl_pins q _ _ h₁ h₂ .x19 (by simp)

private theorem arguments_ready (q : SearchPoint) (u : State) (h : AllocCT q u) :
    WP isa (.block arguments) u (CallCT q) := by
  obtain ⟨s, ⟨⟨original, h, ht⟩, hr⟩, rfl⟩ := h
  exact WP.mono (search_arguments_ok h) fun _ ⟨⟨ha, hm⟩, k⟩ => ⟨original, s, h, ht, hr, ha, hm, k⟩

theorem search_candidate_run_ct (c : Cand) :
    RelCT isa (Two ReadyCT) (candidateRun c.call) (fun _ _ => True) := by
  unfold candidateRun
  apply RelCT.alloc
  refine (RelCT.seq (two_piece [.x19] alloc_pins (by taint_decide) arguments_ready)
    (search_call_ct c)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocated, hsp]⟩

private theorem cand_ready (c : Cand) (q : SearchPoint) (s : State) (h : ReadyCT q s) :
    WP isa (candidateRun c.call) s (CandCT q) :=
  let ⟨⟨o, hl, ht⟩, hr⟩ := h
  WP.mono (search_candidate_run c hl) fun _ ⟨hl', hc⟩ => ⟨o, hl', hc, ht, hr⟩

/-! ## An iteration -/

/-- Whether the search goes on past the point's candidate. -/
def SearchPoint.continues (q : SearchPoint) : Prop :=
  q.remaining ≠ 0 ∧ (q.status = 2 ∨ q.status = 3) ∧ q.cand ≠ 0

/-- The point past the candidate, when the search goes on. -/
def SearchPoint.next (q : SearchPoint) : SearchPoint :=
  ⟨q.inputs, q.used + q.cand, if q.status = 2 then q.remaining else q.remaining - 1,
    q.trace.drop (q.leak.length + 1)⟩

theorem continues_iff {q : SearchPoint} {original s : State}
    (hl : SearchLive q.inputs original q.used q.remaining s)
    (ht : (tailOf q.inputs original q.used q.remaining).trace = q.trace) :
    Continues q.inputs original q.used q.remaining ↔ q.continues := by
  by_cases hr : q.remaining = 0
  · simp [Continues, SearchPoint.continues, hr]
  · rw [Continues, SearchPoint.continues, SearchCTL.status ht hr, SearchCTL.used hl ht hr]

theorem ctl_next {q : SearchPoint} {original s t : State} {final : PrimeSearchResult}
    (hl : SearchLive q.inputs original q.used q.remaining s)
    (ht : (tailOf q.inputs original q.used q.remaining).trace = q.trace)
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
  refine ⟨original, ?_, ?_⟩
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
  (q.continues ∧ isa.eval (.zero .x .x9) t = some true ∧ SearchCTL q.next t) ∨
    (¬q.continues ∧ isa.eval (.zero .x .x9) t = some false)

theorem search_ct_step (c : Cand) (q : SearchPoint) (s : State) (h : SearchCTL q s) :
    WP isa (iteration c.call) s (SearchCTStep q) := by
  obtain ⟨o, hl, ht⟩ := h
  refine WP.mono (search_iteration c (final := (tailOf q.inputs o q.used q.remaining).consume q.used [])
    ⟨hl, [], rfl⟩) fun t hs => ?_
  rcases hs with ⟨he, hc⟩ | ⟨he, hn, -⟩
  · exact .inl ⟨(continues_iff hl ht).mp hc.continues, he, ctl_next hl ht hc⟩
  · exact .inr ⟨fun h => hn ((continues_iff hl ht).mpr h), he⟩

/-- The loop state with the guard's flag. -/
def GuardK (q : SearchPoint) (s : State) : Prop :=
  SearchCTL q s ∧ isa.eval (.zero .x .x9) s = some (decide (q.remaining = 0))

private theorem guard_ready (q : SearchPoint) (s : State) (h : SearchCTL q s) :
    WP isa (.block [ldf .x9 0]) s (GuardK q) := by
  obtain ⟨o, hl, ht⟩ := h
  exact WP.mono (iter_guard hl) fun t ⟨⟨he, hm⟩, k⟩ => ⟨⟨o, hl.keep k hm, ht⟩, he⟩

/-- The branch leaves `x19` at the frame. -/
theorem search_branch (c : Cand) {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    {used remaining : Nat} (h : SearchIter p original final used remaining s)
    (he : isa.eval (.zero .x .x9) s = some (decide (remaining = 0))) :
    WP isa (.ite (.zero .x .x9) exhausted (.seq (candidateRun c.call) classify)) s
      fun t => t.gpr .x19 = p.F := by
  refine WP.ite _ he (fun hz => ?_) (fun hz => ?_)
  · have hz := of_decide_eq_true hz
    subst hz
    obtain ⟨hl, tr, hfinal⟩ := h
    unfold tailOf at hfinal
    rw [VG.Proof.RsaKeyGen.Search.search_zero] at hfinal
    exact WP.mono (search_exhausted hl (result := final) (by rw [hfinal]; rfl)) fun t hd => hd.x19
  · have hz := of_decide_eq_false hz
    refine WP.seq (WP.mono (search_candidate_run c h.1) fun t ⟨ht, hc⟩ => ?_)
    refine WP.mono (search_classify ⟨ht, h.2⟩ hc hz) fun _ hp => ?_
    rcases hp with ⟨-, -, _, _, -, ⟨hi, -⟩, -⟩ | ⟨-, -, hd⟩
    exacts [hi.x19, hd.x19]

private theorem ready_of_guard {q : SearchPoint} {s : State}
    (h : GuardK q s ∧ isa.eval (.zero .x .x9) s = some false) : ReadyCT q s := by
  refine ⟨h.1.1, fun h0 => ?_⟩
  have := h.1.2.symm.trans h.2
  simp [h0] at this

private theorem branch_ct (c : Cand) :
    RelCT isa (Two GuardK) (.ite (.zero .x .x9) exhausted (.seq (candidateRun c.call) classify))
      (fun _ _ => True) := by
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact leaf SearchPoint.inputs (fun _ _ h => h.1.1.any) search_exhausted_ct
  · refine RelCT.seq ((two_post (search_candidate_run_ct c) (cand_ready c)).mono
      (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, ready_of_guard h₁, ready_of_guard h₂, hsp⟩) fun _ _ h => h) ?_
    exact search_classify_ct

theorem search_iteration_ct (c : Cand) :
    RelCT isa (Two SearchCTL) (iteration c.call) (fun _ _ => True) := by
  unfold iteration
  refine RelCT.seq (two_piece [.x19] search_ctl_pins (by taint_decide) guard_ready) ?_
  exact RelCT.seq (two_post (branch_ct c) (Ψ := fun q t => t.gpr .x19 = q.inputs.F)
      fun q u h => let ⟨⟨_, hl, _⟩, he⟩ := h; search_branch c ⟨hl, [], rfl⟩ he)
    (two_taint [.x19] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact h₁.trans h₂.symm) (by taint_decide))

/-! ## The loop -/

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q : SearchPoint, n = q.inputs.randLen - q.used + 1 ∧ SearchCTL q s ∧ SearchCTL q t ∧ s.sp = t.sp

private theorem iteration_pair (c : Cand) (n : Nat) :
    RelCT isa (LoopPair n) (iteration c.call) fun s t =>
      isa.eval (.zero .x .x9) s = isa.eval (.zero .x .x9) t ∧
      (isa.eval (.zero .x .x9) s = some false → True) ∧
      (isa.eval (.zero .x .x9) s = some true → ∃ m < n, LoopPair m s t) := by
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
    RelCT isa (Two SearchCTL) (.loop (iteration c.call) (.zero .x .x9)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht, hsp⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration c.call) (c := .zero .x .x9)
    (Q := fun _ _ => True) LoopPair (iteration_pair c) (q.inputs.randLen - q.used + 1)
    _ _ _ _ _ _ ⟨q, rfl, hs, ht, hsp⟩ he₁ he₂

end VG.Proof.RsaKeyGen.AArch64.Search
