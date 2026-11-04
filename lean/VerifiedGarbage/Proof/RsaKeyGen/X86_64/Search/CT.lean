module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Safety
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Safety
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Omega

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
    WP isa (.block (advance ++ [.alu .cmp .rdx (.imm 2)])) s (Reject3 q) := by
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

end VG.Proof.RsaKeyGen.X86_64.Search
