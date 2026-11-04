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

end VG.Proof.RsaKeyGen.X86_64.Search
