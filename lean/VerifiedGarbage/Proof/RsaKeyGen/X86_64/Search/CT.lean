module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Step
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Entry
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Call
import VerifiedGarbage.Proof.RsaKeyGen.SearchSpec
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCode
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCTCode
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Step
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Entry
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Call
meta import VerifiedGarbage.Proof.RsaKeyGen.SearchSpec
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Omega

-- separate module: its proofs build in parallel with the correctness ones, `Correct`

/-! # The search's timing depends on its public data and its trace

Two runs at the same point (`SearchPoint`) agree on the public descriptor,
the octets consumed, the counted candidates left and the trace still to come,
which each run's own search from there gives. The next candidate's leak is
the trace's next entry, and with it what became of the candidate: its status
and the octets it consumed.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Search

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64
open VG.Impl.RsaKeyGen.X86_64.Search
open VG.Spec.RsaKeyGen (PrimeSearchResult)

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

theorem search_any_pins : Pins SearchAny [.r12, .rsp] := by
  intro p s t ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [h₁.r12.trans h₂.r12.symm, h₁.rsp.trans h₂.rsp.symm]

theorem search_ctl_pins : Pins SearchCTL [.r12, .rsp] :=
  fun _ _ _ h₁ h₂ => search_any_pins _ _ _ h₁.any h₂.any

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

/-! ## Giving up -/

def SearchZeroCT (p : SearchPublic) (s : State) : Prop := SearchAny p s ∧ s.gpr .rdi = p.F

private theorem zero_header (p : SearchPublic) (s : State) (h : SearchZeroCT p s) :
    WP isa (.block [.mov .rsi (.mem (VG.Impl.Bignum.X86_64.hdr 5)), .mov .rcx (.mem (VG.Impl.Bignum.X86_64.hdr 6)),
      .mov32 .rax (.imm 0)]) s
      fun t => t.gpr .rsi = p.op ∧ t.gpr .rcx = BitVec.ofNat 64 p.len := by
  obtain ⟨⟨original, used, remaining, h⟩, hd⟩ := h
  obtain ⟨hl, -, -⟩ := h.frame_in (t := s) rfl
  have hp := h.slot (j := 5) (v := p.op) (by simp [SearchPublic.headers])
  have hk := h.slot (j := 6) (v := BitVec.ofNat 64 p.len) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hp hk
  xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, hdrOff, off, BitVec.ofInt_natCast, Nat.reduceMul,
    hd, hp, hk, hl 40 (by decide), hl 48 (by decide)]

theorem search_zero_ct : RelCT isa (Two SearchZeroCT) (VG.Impl.Rsa.X86_64.Keys.zeroOut 5 6)
    (fun _ _ => True) := by
  unfold VG.Impl.Rsa.X86_64.Keys.zeroOut
  refine RelCT.seq (two_piece [.rdi] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.2.trans h₂.2.symm) (by taint_decide) zero_header) ?_
  exact two_taint [.rsi, .rcx] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

private theorem exhausted_prefix (p : SearchPublic) (s : State) (h : SearchAny p s) :
    WP isa (.block (terminal 3 ++ ([.mov .rdi (.reg .r12)] : List Instr))) s (SearchZeroCT p) := by
  obtain ⟨original, used, remaining, h⟩ := h
  rw [WP.block_append_iff]
  refine WP.mono (search_terminal h 3) fun t ⟨hm, kt⟩ => ?_
  have ht := h.terminated 3 hm kt
  refine WP.mono (WP.keep [.rdi] (Q := fun u =>
    u.gpr .rdi = p.F ∧ u.mem = t.mem) (by xrun [ht.r12]) rfl)
    fun u ⟨⟨hd, hm'⟩, k⟩ => ⟨⟨original, used, 0, ht.keep k hm' (by decide)⟩, hd⟩

theorem search_exhausted_ct : RelCT isa (Two SearchAny) exhausted (fun _ _ => True) := by
  unfold exhausted
  exact RelCT.seq (two_piece [.r12, .rsp] search_any_pins (by taint_decide) exhausted_prefix) search_zero_ct

/-! ## After the candidate -/

/-- A loop state at the point, before its candidate. -/
def SearchAt (q : SearchPoint) (s : State) : Prop :=
  ∃ original, SearchLive q.inputs original q.used q.remaining s

theorem search_at_pins : Pins SearchAt [.r12, .rsp] := fun q _ _ ⟨o₁, h₁⟩ ⟨o₂, h₂⟩ =>
  search_any_pins q.inputs _ _ ⟨o₁, _, _, h₁⟩ ⟨o₂, _, _, h₂⟩

/-- A loop state at the point, after its candidate. -/
def CandCT (q : SearchPoint) (s : State) : Prop :=
  ∃ original, SearchLive q.inputs original q.used q.remaining s ∧
    CandPost q.inputs (searchP original) (searchRand original) q.used s ∧
    (tailOf q.inputs original q.used q.remaining).trace = q.trace ∧ q.remaining ≠ 0

theorem CandCT.at {q : SearchPoint} {s : State} (h : CandCT q s) : SearchAt q s :=
  let ⟨o, h, _⟩ := h; ⟨o, h⟩

theorem cand_ct_pins : Pins CandCT [.r12, .rsp] := fun q _ _ h₁ h₂ => search_at_pins q _ _ h₁.at h₂.at

/-- The candidate's status, from the point. -/
abbrev SearchPoint.status (q : SearchPoint) : Nat := Search.statusOfLeak q.leak

/-- The octets the candidate consumed, from the point. -/
abbrev SearchPoint.cand (q : SearchPoint) : Nat := Search.usedOfLeak q.inputs.len q.leak

theorem CandCT.status {q : SearchPoint} {s : State} (h : CandCT q s) :
    ((s.gpr .rax).setWidth 32).toNat = q.status := by
  obtain ⟨o, -, hc, ht, hr⟩ := h
  rw [hc.1, VG.Proof.RsaKeyGen.Search.status_of_leak, SearchCTL.leak ht hr]

theorem CandCT.used {q : SearchPoint} {original s : State} (hl : SearchLive q.inputs original q.used q.remaining s)
    (ht : (tailOf q.inputs original q.used q.remaining).trace = q.trace) (hr : q.remaining ≠ 0) :
    candUsed q.inputs original q.used = q.cand := by
  have hu := VG.Proof.RsaKeyGen.Search.used_of_leak (L := q.inputs.len) (eB := q.inputs.eB)
    (pB := searchP original) ((searchRand original).drop q.used)
  rw [SearchCTL.leak ht hr, List.length_drop, hl.rand_length] at hu
  exact hu

theorem status_lt (q : SearchPoint) {s : State} (h : CandCT q s) : q.status < 4 := by
  obtain ⟨o, -, -, ht, hr⟩ := h
  rw [SearchPoint.status, ← SearchCTL.leak ht hr, ← VG.Proof.RsaKeyGen.Search.status_of_leak]
  unfold Spec.RsaKeyGen.candidateStatus; split <;> decide

/-! ## Accepting, asking for more, going on -/

/-- `used`'s pointer, from the frame. -/
theorem pin_up (p : SearchPublic) (s : State) (h : SearchAny p s) :
    WP isa (.block [.mov .rcx (.mem (field 7))]) s fun t => SearchAny p t ∧ t.gpr .rcx = p.up := by
  obtain ⟨original, used, remaining, h⟩ := h
  obtain ⟨hl, -, -⟩ := h.frame_in (t := s) rfl
  have h7 := h.slot (j := 7) (v := p.up) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h7
  refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = p.up ∧ t.mem = s.mem) (by
    xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, h.r12,
      hl 56 (by decide), h7]) rfl) fun t ⟨⟨hc, hm⟩, k⟩ => ⟨⟨original, used, remaining, h.keep k hm (by decide)⟩, hc⟩

theorem up_pins : Pins (fun p t => SearchAny p t ∧ t.gpr .rcx = p.up) [.r12, .rsp, .rcx] := by
  intro p s t h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact search_any_pins p s t h₁.1 h₂.1 .r12 (by simp)
  · exact search_any_pins p s t h₁.1 h₂.1 .rsp (by simp)
  · exact h₁.2.trans h₂.2.symm

theorem search_accept_ct : RelCT isa (Two SearchAny) (.block accept) (fun _ _ => True) := by
  change RelCT isa _ (.block ([.mov .rcx (.mem (field 7))] ++ ([.mov .rcx (.mem { base := .rcx })] ++
    [.mov .rax (.mem (field 16)), .alu .add .rax (.reg .rcx), .store (field 16) .rax] ++ terminal 1))) _
  exact RelCT.block_append (RelCT.seq (two_piece [.r12, .rsp] search_any_pins (by taint_decide) pin_up)
    (two_taint [.r12, .rsp, .rcx] up_pins (by taint_decide)))

theorem search_request_ct : RelCT isa (Two SearchAny) (.block request) (fun _ _ => True) :=
  two_taint [.r12, .rsp] search_any_pins (by taint_decide)

/-- The short tape's test, at the point. -/
def ShortCT (q : SearchPoint) (s : State) : Prop :=
  SearchAt q s ∧ eval .ae s = some (decide (Spec.RsaKeyGen.primeEntropy q.inputs.len ≤ q.inputs.randLen - q.used))

theorem search_short_ct : RelCT isa (Two SearchAt) short (fun _ _ => True) := by
  unfold short
  refine RelCT.seq (two_piece (Ψ := ShortCT) [.r12, .rsp] search_at_pins (by taint_decide)
    (fun q s ⟨o, h⟩ => WP.mono (short_guard h) fun t ⟨⟨_, he, hm⟩, k⟩ =>
      ⟨⟨o, h.keep k hm (by decide)⟩, he⟩)) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact two_map (fun q => q.inputs) (fun _ _ h => let ⟨o, h⟩ := h.1.1; ⟨o, _, _, h⟩) search_exhausted_ct
  · exact two_map (fun q => q.inputs) (fun _ _ h => let ⟨o, h⟩ := h.1.1; ⟨o, _, _, h⟩) search_request_ct

/-- The candidate's status in rax, at the point. -/
def RejectCT (q : SearchPoint) (s : State) : Prop := CandCT q s ∧ s.gpr .rax = BitVec.ofNat 64 q.status

def Reject1 (q : SearchPoint) (s : State) : Prop :=
  RejectCT q s ∧ s.gpr .rdx = BitVec.ofNat 64 q.status ∧ s.gpr .rcx = q.inputs.up

def Reject2 (q : SearchPoint) (s : State) : Prop :=
  s.gpr .r12 = q.inputs.F ∧ s.gpr .rsp = q.inputs.F ∧ s.gpr .rdx = BitVec.ofNat 64 q.status ∧
    eval .e s = some (decide (q.cand = 0)) ∧ SearchAny q.inputs s ∧ q.status < 4

def Reject3 (q : SearchPoint) (s : State) : Prop :=
  s.gpr .r12 = q.inputs.F ∧ s.gpr .rsp = q.inputs.F ∧ eval .e s = some (decide (q.status = 2))

theorem CandCT.keep {q : SearchPoint} {s t : State} (h : CandCT q s) {rs : List Reg} (k : Keep rs s t)
    (hm : t.mem = s.mem) (hr : (t.gpr .rax).setWidth 32 = (s.gpr .rax).setWidth 32)
    (hregs : ∀ reg ∈ calleeSaved, reg ∉ rs) : CandCT q t :=
  let ⟨o, hl, hc, ht, hr'⟩ := h
  ⟨o, hl.keep k hm hregs, hc.keep hm hr, ht, hr'⟩

private theorem reject1_ok (q : SearchPoint) (s : State) (h : RejectCT q s) :
    WP isa (.block [.mov .rdx (.reg .rax), .mov .rcx (.mem (field 7))]) s (Reject1 q) := by
  obtain ⟨⟨o, hl, hc, ht, hr⟩, hra⟩ := h
  obtain ⟨hld, -, -⟩ := hl.frame_in (t := s) rfl
  have h7 := hl.slot (j := 7) (v := q.inputs.up) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h7
  refine WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = s.gpr .rax ∧ t.gpr .rcx = q.inputs.up ∧
    t.mem = s.mem) (by
      xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, hl.r12,
        hld 56 (by decide), h7]) rfl) fun t ⟨⟨hdx, hcx, hm⟩, k⟩ => ?_
  have hrt : t.gpr .rax = s.gpr .rax := k.gpr (by decide)
  exact ⟨⟨CandCT.keep (q := q) ⟨o, hl, hc, ht, hr⟩ k hm (by rw [hrt]) (by decide), hrt.trans hra⟩,
    hdx.trans hra, hcx⟩

private theorem reject2_ok (q : SearchPoint) (s : State) (h : Reject1 q s) :
    WP isa (.block [.mov .rcx (.mem { base := .rcx }), .alu .test .rcx (.reg .rcx)]) s (Reject2 q) := by
  obtain ⟨⟨⟨o, hl, hc, ht, hr⟩, hra⟩, hdx, hcx⟩ := h
  have h4 := status_lt q (s := s) ⟨o, hl, hc, ht, hr⟩
  have hcu := CandCT.used hl ht hr
  have hf := hl.callFacts
  have hin : InRegions (s.rd ++ s.wr) q.inputs.up 8 := by
    refine ⟨inUsed o, List.mem_append_right _ ?_, ?_⟩
    · rw [hl.wr, hl.input.1.2.2.2.1]; exact List.mem_cons_of_mem _ (by simp [inWrites])
    · rw [← hl.input.2]; simp only [inUsed, searchOfState, Region.Contains, BitVec.sub_self, BitVec.toNat_zero,
        Nat.zero_add]; decide
  have hu : s.mem.readW q.inputs.up 64 = BitVec.ofNat 64 q.cand := by
    have := hc.2.2
    change [word s.mem q.inputs.up 0] = _ at this
    have h' := (List.cons.inj this).1
    simp only [Bignum.word, off, BitVec.add_zero] at h'
    rw [h', ← hcu]
    rfl
  have hz : (BitVec.ofNat 64 q.cand == 0) = decide (q.cand = 0) :=
    ofNat64_beq_zero (by
      have : candUsed q.inputs o q.used ≤ q.inputs.randLen := by unfold candUsed; split <;> omega
      have := hf.rand64; omega)
  refine WP.mono (WP.keep [.rcx] (Q := fun t => eval .e t = some (decide (q.cand = 0)) ∧ t.mem = s.mem) (by
      xrun [State.ea, BitVec.ofInt_ofNat, BitVec.add_zero, eval, hcx, hin, hu, BitVec.and_self, hz]) rfl)
    fun t ⟨⟨he, hm⟩, k⟩ => ⟨(k.gpr (by decide)).trans hl.r12, (k.gpr (by decide)).trans hl.rsp,
      (k.gpr (by decide)).trans hdx, he, ⟨o, _, _, hl.keep k hm (by decide)⟩, h4⟩

private theorem reject3_ok (q : SearchPoint) (s : State) (h : Reject2 q s ∧ eval .e s = some false) :
    WP isa (.block (advance ++ ([.alu .cmp .rdx (.imm 2)] : List Instr))) s (Reject3 q) := by
  obtain ⟨⟨hr12, hsp, hdx, -, ⟨o, u, k, hl⟩, h4⟩, -⟩ := h
  refine WP.mono (advance_ok hl (u := (s.gpr .rcx).toNat) (ofNat_toNat64 _).symm) fun t ⟨⟨_, he⟩, kt⟩ => ?_
  refine ⟨(kt.gpr (by decide)).trans hr12, (kt.gpr (by decide)).trans hsp, ?_⟩
  rw [he, hdx]
  congr 1
  rcases (show q.status = 0 ∨ q.status = 1 ∨ q.status = 2 ∨ q.status = 3 by omega) with h | h | h | h <;>
    rw [h] <;> decide

theorem search_reject_ct : RelCT isa (Two RejectCT) reject (fun _ _ => True) := by
  unfold reject
  change RelCT isa _ (.seq (.block ([.mov .rdx (.reg .rax), .mov .rcx (.mem (field 7))] ++
    [.mov .rcx (.mem { base := .rcx }), .alu .test .rcx (.reg .rcx)])) _) _
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (two_piece (Ψ := Reject1) [.r12, .rsp] (fun q _ _ h₁ h₂ => cand_ct_pins q _ _ h₁.1 h₂.1)
      (by taint_decide) reject1_ok)
    (two_piece (Ψ := Reject2) [.r12, .rsp, .rcx] (fun q _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact cand_ct_pins q _ _ h₁.1.1 h₂.1.1 .r12 (by simp)
      · exact cand_ct_pins q _ _ h₁.1.1 h₂.1.1 .rsp (by simp)
      · exact h₁.2.2.trans h₂.2.2.symm) (by taint_decide) reject2_ok))) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.1.trans h₂.2.2.2.1.symm) ?_ ?_
  · exact two_map (fun q => q.inputs) (fun _ _ h => h.1.2.2.2.2.1) search_exhausted_ct
  · refine RelCT.seq (two_piece (Ψ := Reject3) [.r12, .rsp] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.1.trans h₂.1.1.symm, h₁.1.2.1.trans h₂.1.2.1.symm]) (by taint_decide) reject3_ok) ?_
    refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm) ?_ ?_
    · exact two_taint [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide)
    · exact two_taint [.r12, .rsp] (fun _ _ _ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        exacts [h₁.1.1.trans h₂.1.1.symm, h₁.1.2.1.trans h₂.1.2.1.symm]) (by taint_decide)

def Classify1 (q : SearchPoint) (s : State) : Prop :=
  RejectCT q s ∧ eval .e s = some (decide (q.status = 1))

def Classify2 (q : SearchPoint) (s : State) : Prop :=
  RejectCT q s ∧ eval .e s = some (decide (q.status = 0))

private theorem classify1_ok (q : SearchPoint) (s : State) (h : CandCT q s) :
    WP isa (.block [.mov32 .rax (.reg .rax), .alu .cmp .rax (.imm 1)]) s (Classify1 q) := by
  have h4 := status_lt q h
  refine WP.mono (classify_head s h.status h4) fun t ⟨⟨hra, he, hm⟩, k⟩ => ?_
  have hlow : (t.gpr .rax).setWidth 32 = (s.gpr .rax).setWidth 32 := by
    rw [hra]; apply BitVec.eq_of_toNat_eq
    have hst' : (s.gpr .rax).toNat % 2 ^ 32 = q.status := by rw [← BitVec.toNat_setWidth]; exact h.status
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat, hst', Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  exact ⟨⟨h.keep k hm hlow (by decide), hra⟩, he⟩

private theorem classify2_ok (q : SearchPoint) (s : State) (h : Classify1 q s ∧ eval .e s = some false) :
    WP isa (.block [.alu .test .rax (.reg .rax)]) s (Classify2 q) := by
  obtain ⟨⟨⟨hc, hra⟩, -⟩, -⟩ := h
  refine WP.mono (test_rax s hra (status_lt q hc)) fun t ⟨⟨hrt, he, hm⟩, k⟩ =>
    ⟨⟨hc.keep k hm (by rw [hrt]) (by decide), hrt.trans hra⟩, he⟩

theorem search_classify_ct : RelCT isa (Two CandCT) classify (fun _ _ => True) := by
  unfold classify
  refine RelCT.seq (two_piece (Ψ := Classify1) [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil)
    (by taint_decide) classify1_ok) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact two_map (fun q => q.inputs) (fun _ _ h => let ⟨o, h⟩ := h.1.1.1.at; ⟨o, _, _, h⟩) search_accept_ct
  · refine RelCT.seq (two_piece (Ψ := Classify2) [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil)
      (by taint_decide) classify2_ok) ?_
    refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
    · exact (search_short_ct.mono (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, h₁.1.1.1.at, h₂.1.1.1.at⟩) fun _ _ h => h)
    · exact (search_reject_ct.mono (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, h₁.1.1, h₂.1.1⟩) fun _ _ h => h)

/-! ## The candidate's call -/

open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg frame_alloc_ct)

/-- A loop state at the point that calls a candidate. -/
def ReadyCT (q : SearchPoint) (s : State) : Prop := SearchCTL q s ∧ q.remaining ≠ 0

/-- The candidate's entry, before the call. -/
def CallCT (q : SearchPoint) (u : State) : Prop :=
  ∃ original s, SearchLive q.inputs original q.used q.remaining s ∧
    (tailOf q.inputs original q.used q.remaining).trace = q.trace ∧ q.remaining ≠ 0 ∧
    CallRegs q.inputs u ∧ u.mem = writeFrame s.mem (q.inputs.F - BitVec.ofNat 64 40) (callValues q.inputs q.used) ∧
    Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (allocated 40 s) u

theorem CallCT.rsp {q : SearchPoint} {u : State} (h : CallCT q u) :
    u.gpr .rsp = q.inputs.sp - BitVec.ofNat 64 200 := by
  obtain ⟨o, s, hl, -, -, -, -, k⟩ := h
  rw [k.gpr (by decide), allocated_rsp, hl.rsp, F_40]

/-- What the candidate's timing may depend on, from the point. -/
theorem call_leak {q : SearchPoint} {u : State} (h : CallCT q u) :
    candLeak (callState q.inputs q.used u) = q.inputs.eB.map (·.toNat) ++ q.leak := by
  have hu := h.rsp
  obtain ⟨o, s, hl, ht, hr, ha, hm, -⟩ := h
  have hf := hl.callFacts
  obtain ⟨he, hpb, hrand⟩ := call_inputs hl hm hu
  obtain ⟨a0, a1, a2, -, -⟩ := call_args (used := q.used) hu hm
  obtain ⟨-, hsi, -, hcx, h8, h9⟩ := ha
  have t8 : (BitVec.ofNat 64 q.inputs.elen).toNat = q.inputs.elen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hf.e8; omega)]
  have tl : (BitVec.ofNat 64 q.inputs.len).toNat = q.inputs.len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.len64]
  have tp : (BitVec.ofNat 64 q.inputs.plen).toNat = q.inputs.plen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.plen64]
  have tr : (BitVec.ofNat 64 (q.inputs.randLen - q.used)).toNat = q.inputs.randLen - q.used := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hf.rand64; omega)]
  simp only [candLeak, call_gpr (show Reg.rsi ≠ .rsp by decide), call_gpr (show Reg.rcx ≠ .rsp by decide),
    call_gpr (show Reg.r8 ≠ .rsp by decide), call_gpr (show Reg.r9 ≠ .rsp by decide),
    hsi, hcx, h8, h9, a0, a1, a2, t8, tl, tp, tr, he, hpb, hrand]
  rw [SearchCTL.leak ht hr]

theorem search_call_ct (v : RoundImpl) : RelCT isa (Two CallCT) (candidateCall v) (fun _ _ => True) := by
  have hmc : MmCalls v.mont v.mm := ⟨v.mmOk, v.mmInline⟩
  refine RelCT.callEx (k := sharedCandContract)
    (sharedCode_correct v.mont hmc (Kernel.called v) (sharedCandidate_mx v))
    (sharedCode_constantTime v.mont hmc (Kernel.called v)) fun u₁ u₂ ⟨q, h₁, h₂⟩ => ?_
  have hu₁ := h₁.rsp
  have hu₂ := h₂.rsp
  have hl₁ := call_leak h₁
  have hl₂ := call_leak h₂
  obtain ⟨o₁, s₁, l₁, -, -, a₁, m₁, k₁⟩ := h₁
  obtain ⟨o₂, s₂, l₂, -, -, a₂, m₂, k₂⟩ := h₂
  obtain ⟨b0, b1, b2, b3, b4⟩ := call_args (used := q.used) hu₁ m₁
  obtain ⟨c0, c1, c2, c3, c4⟩ := call_args (used := q.used) hu₂ m₂
  obtain ⟨di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ := a₁
  obtain ⟨di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ := a₂
  refine ⟨callReads q.inputs q.used, callWrites q.inputs, callReads q.inputs q.used, callWrites q.inputs,
    call_cand_pre l₁.callFacts hu₁ ⟨di₁, si₁, dx₁, cx₁, r8₁, r9₁⟩ m₁,
    call_cand_pre l₂.callFacts hu₂ ⟨di₂, si₂, dx₂, cx₂, r8₂, r9₂⟩ m₂, ?_,
    call_covers_reads l₁ k₁.2.1 k₁.2.2, call_covers_writes l₁ k₁.2.2,
    call_covers_reads l₂ k₂.2.1 k₂.2.2, call_covers_writes l₂ k₂.2.2, hu₁.trans hu₂.symm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, hl₁.trans hl₂.symm⟩
  · rw [call_gpr (by decide), call_gpr (by decide), di₁, di₂]
  · rw [call_gpr (by decide), call_gpr (by decide), si₁, si₂]
  · rw [call_gpr (by decide), call_gpr (by decide), dx₁, dx₂]
  · rw [call_gpr (by decide), call_gpr (by decide), cx₁, cx₂]
  · rw [call_gpr (by decide), call_gpr (by decide), r8₁, r8₂]
  · rw [call_gpr (by decide), call_gpr (by decide), r9₁, r9₂]
  · rw [call_rsp hu₁, call_rsp hu₂]
  · match i, hi with
    | 0, _ => exact b0.trans c0.symm
    | 1, _ => exact b1.trans c1.symm
    | 2, _ => exact b2.trans c2.symm
    | 3, _ => exact b3.trans c3.symm
    | 4, _ => exact b4.trans c4.symm

def AllocCT (q : SearchPoint) (u : State) : Prop := ∃ s, ReadyCT q s ∧ u = allocated 40 s

theorem alloc_pins : Pins AllocCT [.r12, .rsp] := by
  rintro q _ _ ⟨a, ⟨h₁, _⟩, rfl⟩ ⟨b, ⟨h₂, _⟩, rfl⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [allocated_reg _ _ _ (by decide), allocated_reg _ _ _ (by decide)]
    exact search_ctl_pins q _ _ h₁ h₂ .r12 (by simp)
  · rw [allocated_rsp, allocated_rsp, search_ctl_pins q _ _ h₁ h₂ .rsp (by simp)]

private theorem arguments_ready (q : SearchPoint) (u : State) (h : AllocCT q u) :
    WP isa (.block arguments) u (CallCT q) := by
  obtain ⟨s, ⟨⟨original, h, ht⟩, hr⟩, rfl⟩ := h
  exact WP.mono (search_arguments_ok h) fun _ ⟨ha, hm, k⟩ => ⟨original, s, h, ht, hr, ha, hm, k⟩

theorem search_candidate_run_ct (v : RoundImpl) :
    RelCT isa (Two ReadyCT) (candidateRun (candidateCall v)) (fun _ _ => True) := by
  unfold candidateRun
  apply frame_alloc_ct
  refine (RelCT.seq (two_piece [.r12, .rsp] alloc_pins (by taint_decide) arguments_ready)
    (search_call_ct v)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩⟩

/-! ## An iteration -/

/-- Whether the search goes on past the point's candidate. -/
def SearchPoint.continues (q : SearchPoint) : Prop :=
  q.remaining ≠ 0 ∧ (q.status = 2 ∨ q.status = 3) ∧ q.cand ≠ 0

/-- The point past the candidate, when the search goes on. -/
def SearchPoint.next (q : SearchPoint) : SearchPoint :=
  ⟨q.inputs, q.used + q.cand, if q.status = 2 then q.remaining else q.remaining - 1,
    q.trace.drop (q.leak.length + 1)⟩

theorem SearchCTL.status {q : SearchPoint} {original : State}
    (ht : (tailOf q.inputs original q.used q.remaining).trace = q.trace) (hr : q.remaining ≠ 0) :
    candStatus q.inputs original q.used = q.status := by
  rw [candStatus, VG.Proof.RsaKeyGen.Search.status_of_leak, SearchCTL.leak ht hr]

theorem continues_iff {q : SearchPoint} {original s : State}
    (hl : SearchLive q.inputs original q.used q.remaining s)
    (ht : (tailOf q.inputs original q.used q.remaining).trace = q.trace) :
    Continues q.inputs original q.used q.remaining ↔ q.continues := by
  by_cases hr : q.remaining = 0
  · simp [Continues, SearchPoint.continues, hr]
  · rw [Continues, SearchPoint.continues, SearchCTL.status ht hr, CandCT.used hl ht hr]

theorem ctl_next {q : SearchPoint} {original s t : State} {final : PrimeSearchResult}
    (hl : SearchLive q.inputs original q.used q.remaining s)
    (ht : (tailOf q.inputs original q.used q.remaining).trace = q.trace)
    (hc : ContinuePost q.inputs original final q.used q.remaining t) : SearchCTL q.next t := by
  obtain ⟨hr, u, k, -, hi, hu, hk, htail⟩ := hc
  have hs := SearchCTL.status ht hr
  have hcu := CandCT.used hl ht hr
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
  (q.continues ∧ eval .e t = some true ∧ SearchCTL q.next t) ∨ (¬q.continues ∧ eval .e t = some false)

theorem search_ct_step (v : RoundImpl) (q : SearchPoint) (s : State) (h : SearchCTL q s) :
    WP isa (iteration (candidateCall v)) s (SearchCTStep q) := by
  obtain ⟨o, hl, ht⟩ := h
  refine WP.mono (search_iteration v (final := (tailOf q.inputs o q.used q.remaining).consume q.used [])
    ⟨hl, [], rfl⟩) fun t hs => ?_
  rcases hs with ⟨he, hc⟩ | ⟨he, hn, -⟩
  · exact .inl ⟨(continues_iff hl ht).mp hc.continues, he, ctl_next hl ht hc⟩
  · exact .inr ⟨fun h => hn ((continues_iff hl ht).mpr h), he⟩

/-- The loop state with the guard's flag. -/
def GuardCT (q : SearchPoint) (s : State) : Prop :=
  SearchCTL q s ∧ eval .e s = some (decide (q.remaining = 0))

private theorem guard_ready (q : SearchPoint) (s : State) (h : SearchCTL q s) :
    WP isa (.block [.mov .rax (.mem (field 0)), .alu .test .rax (.reg .rax)]) s (GuardCT q) := by
  obtain ⟨o, hl, ht⟩ := h
  exact WP.mono (iter_guard hl) fun t ⟨⟨he, hm⟩, k⟩ => ⟨⟨o, hl.keep k hm (by decide), ht⟩, he⟩

/-- The branch leaves r12 at the frame. -/
theorem search_branch (v : RoundImpl) {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    {used remaining : Nat} (h : SearchIter p original final used remaining s)
    (he : eval .e s = some (decide (remaining = 0))) :
    WP isa (.ite .e exhausted (.seq (candidateRun (candidateCall v)) classify)) s
      fun t => t.gpr .r12 = p.F := by
  refine WP.ite _ he (fun hz => ?_) (fun hz => ?_)
  · have hz := of_decide_eq_true hz
    subst hz
    obtain ⟨hl, tr, hfinal⟩ := h
    unfold tailOf at hfinal
    rw [VG.Proof.RsaKeyGen.Search.search_zero] at hfinal
    exact WP.mono (search_exhausted hl (result := final) (by rw [hfinal]; rfl)) fun t hd => hd.r12
  · have hz := of_decide_eq_false hz
    refine WP.seq (WP.mono (search_candidate_run v h.1) fun t ⟨ht, hc⟩ => ?_)
    refine WP.mono (search_classify ⟨ht, h.2⟩ hc hz) fun _ hp => ?_
    rcases hp with ⟨-, -, _, _, -, ⟨hi, -⟩, -⟩ | ⟨-, -, hd⟩
    exacts [hi.r12, hd.r12]

private theorem ready_of_guard {q : SearchPoint} {s : State} (h : GuardCT q s ∧ eval .e s = some false) :
    ReadyCT q s := by
  refine ⟨h.1.1, fun h0 => ?_⟩
  have := h.1.2.symm.trans h.2
  simp [h0] at this

private theorem cand_ready (v : RoundImpl) (q : SearchPoint) (s : State) (h : ReadyCT q s) :
    WP isa (candidateRun (candidateCall v)) s (CandCT q) :=
  let ⟨⟨o, hl, ht⟩, hr⟩ := h
  WP.mono (search_candidate_run v hl) fun _ ⟨hl', hc⟩ => ⟨o, hl', hc, ht, hr⟩

private theorem branch_ct (v : RoundImpl) :
    RelCT isa (Two GuardCT) (.ite .e exhausted (.seq (candidateRun (candidateCall v)) classify))
      (fun _ _ => True) := by
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact two_map (fun q => q.inputs) (fun _ _ h => h.1.1.any) search_exhausted_ct
  · refine RelCT.seq ((two_post (search_candidate_run_ct v) (cand_ready v)).mono
      (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, ready_of_guard h₁, ready_of_guard h₂⟩) fun _ _ h => h) ?_
    exact search_classify_ct

theorem search_iteration_ct (v : RoundImpl) :
    RelCT isa (Two SearchCTL) (iteration (candidateCall v)) (fun _ _ => True) := by
  unfold iteration
  change RelCT isa _ (.seq _ (.seq _ _)) _
  refine RelCT.seq (two_piece [.r12, .rsp] search_ctl_pins (by taint_decide) guard_ready) ?_
  exact RelCT.seq (two_post (branch_ct v) (Ψ := fun q t => t.gpr .r12 = q.inputs.F)
      fun q u h => let ⟨⟨_, hl, _⟩, he⟩ := h; search_branch v ⟨hl, [], rfl⟩ he)
    (two_taint [.r12] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact h₁.trans h₂.symm) (by taint_decide))

/-! ## The loop -/

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q : SearchPoint, n = q.inputs.randLen - q.used + 1 ∧ SearchCTL q s ∧ SearchCTL q t

private theorem iteration_pair (v : RoundImpl) (n : Nat) :
    RelCT isa (LoopPair n) (iteration (candidateCall v)) fun s t =>
      eval .e s = eval .e t ∧ (eval .e s = some false → True) ∧
      (eval .e s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (q : SearchPoint) (s : State) (h : n = q.inputs.randLen - q.used + 1 ∧ SearchCTL q s) :
      WP isa (iteration (candidateCall v)) s fun t => n = q.inputs.randLen - q.used + 1 ∧ SearchCTStep q t :=
    WP.mono (search_ct_step v q s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((search_iteration_ct v).mono
    (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, h₁.2, h₂.2⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂⟩ => ⟨q, ⟨hn, h₁⟩, hn, h₂⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, _, h₂⟩
  rcases h₁ with ⟨hb, e₁, c₁⟩ | ⟨hb, e₁⟩ <;> rcases h₂ with ⟨hb', e₂, c₂⟩ | ⟨hb', e₂⟩
  · refine ⟨e₁.trans e₂.symm, fun _ => trivial, fun _ => ⟨_, ?_, q.next, rfl, c₁, c₂⟩⟩
    obtain ⟨o, hl, _⟩ := c₁
    have hle := hl.used_le
    have hcand := hb.2.2
    simp only [SearchPoint.next] at hle ⊢
    omega
  · exact absurd hb hb'
  · exact absurd hb' hb
  · exact ⟨e₁.trans e₂.symm, fun _ => trivial, fun h => by rw [e₁] at h; cases h⟩

theorem search_loop_ct (v : RoundImpl) :
    RelCT isa (Two SearchCTL) (.loop (iteration (candidateCall v)) .e) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration (candidateCall v)) (c := .e)
    (Q := fun _ _ => True) LoopPair (iteration_pair v) (q.inputs.randLen - q.used + 1)
    _ _ _ _ _ _ ⟨q, rfl, hs, ht⟩ he₁ he₂

/-! ## Entry and return -/

/-- A run's entry, with its public descriptor and its result's trace. -/
def SearchStart (a : SearchPublic × List Nat) (s : State) : Prop :=
  SearchInput a.1 s ∧ (searchResult s).trace = a.2

/-- A run's entry, past the frame's allocation. -/
def AllocStart (a : SearchPublic × List Nat) (u : State) : Prop :=
  ∃ s, SearchStart a s ∧ u = allocated 160 s

private theorem alloc_start_pins : Pins AllocStart [.rsp] := by
  rintro a _ _ ⟨s, ⟨h₁, -⟩, rfl⟩ ⟨t, ⟨h₂, -⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst r
  rw [alloc_rsp h₁, alloc_rsp h₂]

/-- The state's pointer, the frame's base and the stack pointer, past the
frame's first words. -/
def EntryPins (p : SearchPublic) (t : State) : Prop :=
  t.gpr .rax = p.stp ∧ t.gpr .r12 = p.F ∧ t.gpr .rsp = p.F

private theorem entry_pins (a : SearchPublic × List Nat) (u : State) (h : AllocStart a u) :
    WP isa (.block (entryHead ++ entryArgs)) u (EntryPins a.1) := by
  obtain ⟨s, ⟨hi, -⟩, rfl⟩ := h
  rw [WP.block_append_iff]
  refine WP.mono (entry_head_ok hi) fun t ⟨hr, hm, k⟩ => ?_
  refine WP.mono (entry_args_ok hi hm k hr) fun w ⟨hra, _, kw⟩ => ⟨?_, (kw.gpr (by decide)).trans hr, ?_⟩
  · rw [hra, ← hi.2]; rfl
  · rw [kw.gpr (by decide), k.gpr (by decide), alloc_rsp hi]

theorem search_entry_ct : RelCT isa (Two AllocStart) (.block entry) (fun _ _ => True) := by
  unfold entry
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun a => EntryPins a.1) [.rsp] alloc_start_pins
    (by taint_decide) entry_pins) ?_)
  exact two_taint [.rax, .r12, .rsp] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [h₁.1.trans h₂.1.symm, h₁.2.1.trans h₂.2.1.symm, h₁.2.2.trans h₂.2.2.symm]) (by taint_decide)

/-- A loop's end. -/
def DoneCT (p : SearchPublic) (s : State) : Prop := ∃ original r, SearchDone p original r s

private theorem finish_pointers (p : SearchPublic) (s : State) (h : DoneCT p s) :
    WP isa (.block (finish.take 9)) s fun t => t.gpr .rax = p.stp ∧ t.gpr .r8 = p.up := by
  obtain ⟨o, r, h⟩ := h
  have scr := h.input.frame_scr h.wr
  have hl : ∀ d, d + 8 ≤ 160 → InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 d) 8 := fun d hd =>
    let ⟨r, hr, hc⟩ := scr.st hd; ⟨r, List.mem_append_right _ hr, hc⟩
  have hl0 : InRegions (s.rd ++ s.wr) p.F 8 := by simpa only [BitVec.add_zero] using hl 0 (by decide)
  have w7 := h.usedPtr
  have w18 := h.stp
  simp only [Bignum.word, off, Nat.reduceMul] at w7 w18
  unfold finish
  simp only [List.take_succ_cons, List.take_zero]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    h.r12, hl0, hl 8 (by decide), hl 16 (by decide), hl 24 (by decide), hl 32 (by decide), hl 56 (by decide),
    hl 128 (by decide), hl 136 (by decide), hl 144 (by decide), w7, w18]

theorem search_finish_ct : RelCT isa (Two DoneCT) (.block finish) (fun _ _ => True) := by
  change RelCT isa (Two DoneCT) (.block (finish.take 9 ++ finish.drop 9)) _
  refine RelCT.block_append (RelCT.seq (two_piece [.r12] ?_ (by taint_decide) finish_pointers) ?_)
  · intro p s t ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.r12.trans h₂.r12.symm
  · exact two_taint [.rax, .r8] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

/-! ## The whole search -/

/-- The point the loop starts at. -/
def initialPoint (a : SearchPublic × List Nat) : SearchPoint := ⟨a.1, 0, a.1.remaining, a.2⟩

theorem tail_initial {p : SearchPublic} {s : State} (h : SearchInput p s) :
    tailOf p s 0 p.remaining = searchResult s := by
  rw [← h.2]
  simp only [searchResult, tailOf, searchOfState, List.drop_zero]

private theorem entry_started (a : SearchPublic × List Nat) (u : State) (h : AllocStart a u) :
    WP isa (.block entry) u (SearchCTL (initialPoint a)) := by
  obtain ⟨s, ⟨hi, ht⟩, rfl⟩ := h
  exact WP.mono (search_start hi) fun _ hl => ⟨s, hl, by
    show (tailOf a.1 s 0 a.1.remaining).trace = a.2
    rw [tail_initial hi, ht]⟩

private theorem loop_done (v : RoundImpl) (a : SearchPublic × List Nat) (s : State)
    (h : SearchCTL (initialPoint a) s) :
    WP isa (.loop (iteration (candidateCall v)) .e) s (DoneCT a.1) := by
  obtain ⟨o, hl, _⟩ := h
  exact WP.mono (search_loop v (final := (tailOf a.1 o 0 a.1.remaining).consume 0 []) ⟨hl, [], rfl⟩)
    fun _ ht => ⟨o, _, ht⟩

theorem search_code_ct (v : RoundImpl) :
    RelCT isa (Two SearchStart) (searchCode v) (fun _ _ => True) := by
  unfold searchCode code
  apply frame_alloc_ct
  change RelCT isa _ (.seq _ (.seq _ _)) _
  refine (RelCT.seq (two_post search_entry_ct entry_started)
    (RelCT.seq (two_post (two_map initialPoint (fun _ _ h => h) (search_loop_ct v)) (loop_done v))
      (two_map Prod.fst (fun _ _ h => h) search_finish_ct))).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨a, h₁, h₂⟩, rfl, rfl⟩
  exact ⟨a, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩⟩

private theorem search_public_descriptor {s t : State} (h : searchPub s t) : searchOfState s = searchOfState t := by
  obtain ⟨hsp, hdi, hsi, hdx, hcx, h8, h9, ha, he, hw, -⟩ := h
  change [word s.mem (stackArg s 5) 0, word s.mem (stackArg s 5) 8, word s.mem (stackArg s 5) 16,
    word s.mem (stackArg s 5) 24] = [word t.mem (stackArg t 5) 0, word t.mem (stackArg t 5) 8,
      word t.mem (stackArg t 5) 16, word t.mem (stackArg t 5) 24] at hw
  have h0 : s.mem.readW (stackArg s 5) 64 = t.mem.readW (stackArg t 5) 64 := by
    simpa only [Bignum.word, off, BitVec.add_zero] using (List.cons.inj hw).1
  unfold searchOfState
  rw [searchRemaining, searchRemaining, searchLen, searchLen, h0, he, hsp, hdi, hsi, hdx, hcx, h8, h9,
    ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide), ha 5 (by decide)]

theorem search_constantTime (v : RoundImpl) :
    ConstantTime isa searchContract.pre searchContract.pub (searchCode v) := by
  refine RelCT.constantTime ((search_code_ct v).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨(searchOfState s, (searchResult s).trace), ⟨⟨hs, rfl⟩, rfl⟩,
    ⟨⟨ht, (search_public_descriptor hp).symm⟩, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.symm⟩⟩

end VG.Proof.RsaKeyGen.X86_64.Search
