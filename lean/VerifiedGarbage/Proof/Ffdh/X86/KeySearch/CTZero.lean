module

public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Classify
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Entry
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Classify
meta import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Entry

/-! # Two runs of the key search's exits (x86)

Two runs relate by public words (`At`): the public descriptor, and the
state's words at offsets that hold the same in both (never the caller's
`esi`). The taint analysis checks a piece of code from `esi` and `esp`,
which they fix; a piece that addresses memory through words loaded from
the state is checked with those registers fixed too, after a piece that
loads them (`zeroOut_ct`). The exits without an attempt leak nothing but
what those words fix (`exhausted_ct`, `request_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeySearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.KeySearch
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite)

/-- Public words: the descriptor, offsets and their words. -/
abbrev Pw := KPub × List Nat × (Nat → BitVec 32)

/-- A run's state whose words at the offsets `a.2.1` hold `a.2.2`. -/
def At (a : Pw) (s : State) : Prop := ∃ o, ofState o = a.1 ∧ St o a.2.1 a.2.2 s

theorem at_pins : Pins At [.esi, .esp] := by
  intro a s₁ s₂ ⟨o₁, e₁, h₁⟩ ⟨o₂, e₂, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.esi, h₂.esi]; show (ofState o₁).S = (ofState o₂).S; rw [e₁, e₂]
  · rw [h₁.esp, h₂.esp]; show (ofState o₁).sp = (ofState o₂).sp; rw [e₁, e₂]

/-- A loop state's public words: all it keeps but the caller's `esi`. -/
def pubDs : List Nat := [0, 4, 8, 12, 16, 20, 28, 36, 40, 44, 48, 52, 56, 60, 64, 68, 76]

theorem pubDs_aligned : Aligned pubDs := by decide

theorem liveF_pub (p : KPub) (e e' : BitVec 32) (used keys scalars : Nat) :
    ∀ d ∈ pubDs, liveF p e used keys scalars d = liveF p e' used keys scalars d := by
  simp only [pubDs, List.mem_cons, List.not_mem_nil, or_false]
  rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rfl

theorem St.at {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) : At (ofState o, ds, f) s :=
  ⟨o, rfl, h⟩

/-- The public words of a loop state. -/
abbrev liveAt (p : KPub) (used keys scalars : Nat) : Pw := (p, pubDs, liveF p 0 used keys scalars)

theorem Live.at {p : KPub} {o s : State} {used keys scalars : Nat} (h : Live p o used keys scalars s) :
    At (liveAt p used keys scalars) s := by
  have S := h.st
  obtain ⟨A, rfl⟩ := h.input
  exact ⟨o, rfl, (S.sub fun d hd => by
    simp only [pubDs, liveDs, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; omega).congr
    (liveF_pub _ _ _ _ _ _)⟩

/-- Public words from which the outputs are zeroed. -/
def ZAt (a : Pw) (s : State) : Prop :=
  At a s ∧ Aligned a.2.1 ∧ xOff ∈ a.2.1 ∧ yOff ∈ a.2.1 ∧ lenOff ∈ a.2.1 ∧ a.2.2 xOff = a.1.xp ∧
    a.2.2 yOff = a.1.yp ∧ a.2.2 lenOff = BitVec.ofNat 32 a.1.len

theorem zat_pins : Pins ZAt [.esi, .esp] := fun a _ _ h₁ h₂ => at_pins a _ _ h₁.1 h₂.1

theorem zeroHead_ok {d : Nat} (hd4 : d + 4 ≤ 128) (a : Pw) (s : State) (h : At a s) (hd : d ∈ a.2.1)
    (hl : lenOff ∈ a.2.1) :
    WP isa (.block [.mov .edx (.mem (st d)), .mov .ecx (.mem (st lenOff)), .mov .eax (.imm 0)]) s fun t =>
      At a t ∧ t.gpr .edx = a.2.2 d ∧ t.gpr .ecx = a.2.2 lenOff := by
  obtain ⟨o, e, S⟩ := h
  refine S.ld (Or.inr (Or.inr rfl)) hd hd4 fun t₁ S₁ g₁ _ _ _ => ?_
  refine S₁.ld (Or.inr (Or.inl rfl)) hl (by decide) fun t₂ S₂ g₂ o₂ _ _ => ?_
  refine wp_movi fun t₃ U₃ => WP.block_nil ⟨⟨o, e, S₂.reg U₃ (Or.inl rfl)⟩, ?_, ?_⟩
  · rw [U₃.other _ (by decide), o₂ _ (by decide), g₁]
  · rw [U₃.other _ (by decide), g₂]

theorem zeroOut_ct {d : Nat} (hd4 : d + 4 ≤ 128) {hc : VG.Taint.Hint VG.X86.Taint.T}
    (hchk : (taint.check (τr [.esi, .esp])
      (.block [.mov .edx (.mem (st d)), .mov .ecx (.mem (st lenOff)), .mov .eax (.imm 0)]) hc).isSome = true) :
    RelCT isa (Two fun a s => At a s ∧ d ∈ a.2.1 ∧ lenOff ∈ a.2.1) (zeroOut d) fun _ _ => True := by
  unfold zeroOut
  refine RelCT.seq (two_piece (Ψ := fun a t => At a t ∧ t.gpr .edx = a.2.2 d ∧ t.gpr .ecx = a.2.2 lenOff)
    [.esi, .esp] (fun a _ _ h₁ h₂ => at_pins a _ _ h₁.1 h₂.1) hchk
    fun a s h => zeroHead_ok hd4 a s h.1 h.2.1 h.2.2) ?_
  refine two_taint [.edx, .ecx, .esi, .esp] (fun a s₁ s₂ h₁ h₂ r hr => ?_) (by taint_decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | hr
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2, h₂.2.2]
  · exact at_pins a _ _ h₁.1 h₂.1 r (by simpa using hr)

theorem zeroOne_keep {a : Pw} {s : State} (h : ZAt a s) {d : Nat} (hd : d = xOff ∨ d = yOff) :
    WP isa (zeroOut d) s (ZAt a) := by
  obtain ⟨p, ds, f⟩ := a
  obtain ⟨⟨o, e, S⟩, hA, hx, hy, hl, ex, ey, el⟩ := h
  subst e
  have A := S.abi
  have xs : (stR (arg o 12)).Disjoint ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← xR_eq A]; exact A.xs.symm
  have ys : (stR (arg o 12)).Disjoint ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← yR_eq A]; exact A.ys.symm
  have xb : (arg o 0).toNat + (arg o 7).toNat ≤ 2 ^ 32 := by have := A.xBound; rw [A.xLen] at this; exact this
  have yb : (arg o 2).toNat + (arg o 7).toNat ≤ 2 ^ 32 := by have := A.yBound; rw [A.yLen] at this; exact this
  have xin : (⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ : Region) ∈ o.wr := by
    rw [← xR_eq A, A.wr]; exact List.mem_cons_self ..
  have yin : (⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ : Region) ∈ o.wr := by
    rw [← yR_eq A, A.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  rcases hd with rfl | rfl
  · exact WP.mono (S.zeroOne hA ex el hx hl (by decide) xin xs xb) fun u hu =>
      ⟨⟨o, rfl, hu.1⟩, hA, hx, hy, hl, ex, ey, el⟩
  · exact WP.mono (S.zeroOne hA ey el hy hl (by decide) yin ys yb) fun u hu =>
      ⟨⟨o, rfl, hu.1⟩, hA, hx, hy, hl, ex, ey, el⟩

theorem zeroOutputs_ct : RelCT isa (Two ZAt) zeroOutputs fun _ _ => True := by
  unfold zeroOutputs
  refine RelCT.seq (two_post (Ψ := ZAt) (two_map id (fun a s h => ⟨h.1, h.2.2.1, h.2.2.2.2.1⟩)
    (zeroOut_ct (d := xOff) (by decide) (by taint_decide))) fun a s h => zeroOne_keep h (Or.inl rfl)) ?_
  exact two_map id (fun a s h => ⟨h.1, h.2.2.2.1, h.2.2.2.2.1⟩)
    (zeroOut_ct (d := yOff) (by decide) (by taint_decide))

/-- The loop's public data: the descriptor, the octets consumed and the budgets. -/
abbrev Lp := KPub × Nat × Nat × Nat

abbrev Lp.at (q : Lp) : Pw := liveAt q.1 q.2.1 q.2.2.1 q.2.2.2

/-- `terminal 3`'s words. -/
abbrev exhaustedAt (q : Lp) : Pw :=
  (q.1, statusOff :: requestOff :: scalarsOff :: keysOff :: pubDs,
    upd (upd (upd (upd q.at.2.2 keysOff 0) scalarsOff 0) requestOff 0) statusOff (BitVec.ofNat 32 3))

theorem exhausted_ct : RelCT isa (Two fun (q : Lp) s => At q.at s) exhausted fun _ _ => True := by
  unfold exhausted
  refine RelCT.seq (two_piece (Ψ := fun q t => ZAt (exhaustedAt q) t) [.esi, .esp]
    (fun q _ _ h₁ h₂ => at_pins _ _ _ h₁ h₂) (by taint_decide) fun q s h => ?_)
    (two_map exhaustedAt (fun _ _ h => h) zeroOutputs_ct)
  obtain ⟨o, e, S⟩ := h
  refine WP.mono (S.terminal pubDs_aligned 3) fun t ⟨St, _⟩ => ⟨⟨o, e, St⟩,
    show Aligned (statusOff :: requestOff :: scalarsOff :: keysOff :: pubDs) by decide,
    show xOff ∈ statusOff :: requestOff :: scalarsOff :: keysOff :: pubDs by decide,
    show yOff ∈ statusOff :: requestOff :: scalarsOff :: keysOff :: pubDs by decide,
    show lenOff ∈ statusOff :: requestOff :: scalarsOff :: keysOff :: pubDs by decide, ?_, ?_, ?_⟩
  all_goals simp [upd, liveF, xOff, yOff, lenOff, statusOff, requestOff, scalarsOff, keysOff]

/-- `request`'s first block: the request `p_len`, the status 0. -/
theorem St.requestBlock {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds)
    (hl : lenOff ∈ ds) :
    WP isa (.block [.mov .eax (.mem (st lenOff)), .store (st requestOff) .eax, .mov .eax (.imm 0),
      .store (st statusOff) .eax]) s fun t =>
      St o (statusOff :: requestOff :: ds) (upd (upd f requestOff (f lenOff)) statusOff 0) t := by
  refine h.ld (Or.inl rfl) hl (by decide) fun t₁ S₁ g₁ _ _ _ => ?_
  refine S₁.stw hA (d := requestOff) (by decide) (by decide) fun t₂ S₂ G₂ _ _ _ => ?_
  refine wp_movi fun t₃ U₃ => ?_
  have S₃ := S₂.reg U₃ (Or.inl rfl)
  refine S₃.stw (hA.cons (by decide) (by decide)) (d := statusOff) (by decide) (by decide)
    fun t₄ S₄ _ _ _ _ => WP.block_nil ?_
  rw [g₁, U₃.gpr] at S₄
  exact S₄

/-- `request`'s words. -/
abbrev requestAt (q : Lp) : Pw :=
  (q.1, statusOff :: requestOff :: pubDs, upd (upd q.at.2.2 requestOff (q.at.2.2 lenOff)) statusOff 0)

theorem request_ct : RelCT isa (Two fun (q : Lp) s => At q.at s) request fun _ _ => True := by
  unfold request
  refine RelCT.seq (two_piece (Ψ := fun q t => ZAt (requestAt q) t) [.esi, .esp]
    (fun q _ _ h₁ h₂ => at_pins _ _ _ h₁ h₂) (by taint_decide) fun q s h => ?_)
    (two_map requestAt (fun _ _ h => h) zeroOutputs_ct)
  obtain ⟨o, e, S⟩ := h
  refine WP.mono (S.requestBlock pubDs_aligned (show lenOff ∈ pubDs by decide)) fun t St => ⟨⟨o, e, St⟩,
    show Aligned (statusOff :: requestOff :: pubDs) by decide, show xOff ∈ statusOff :: requestOff :: pubDs by decide,
    show yOff ∈ statusOff :: requestOff :: pubDs by decide, show lenOff ∈ statusOff :: requestOff :: pubDs by decide,
    ?_, ?_, ?_⟩
  all_goals simp [upd, liveF, xOff, yOff, lenOff, statusOff, requestOff]

end VG.Proof.Ffdh.X86.KeySearch
