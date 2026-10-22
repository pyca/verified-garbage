module

import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Exits
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Exits
meta import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Steps
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.X86.Target

/-! # Two runs of the parameter search's exits (x86)

Two runs relate by a public descriptor (`Any`), which fixes `esi` and `esp`;
the taint analysis checks a piece of code from them. `zeroOut` addresses the
output through words loaded from the state, which the descriptor fixes
(`zeroOut_ct`). From loop states at the same point, `exhausted` and
`request` leak nothing more (`exhausted_ct`, `request_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.ParamSearch
open VG.Proof.Ffdh.X86.KeySearch (Ctl Aligned upd Scratch)
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite)

/-- A run's state with the public descriptor `p`. -/
def Any (p : PPub) (s : State) : Prop := ∃ o ds f, ofState o = p ∧ St o ds f s

theorem any_pins {α : Type} {Φ : α → State → Prop} (g : α → PPub) (h : ∀ a s, Φ a s → Any (g a) s) :
    Pins Φ [.esi, .esp] := by
  intro a s₁ s₂ h₁ h₂ r hr
  obtain ⟨o₁, _, _, e₁, S₁⟩ := h a s₁ h₁
  obtain ⟨o₂, _, _, e₂, S₂⟩ := h a s₂ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [S₁.esi, S₂.esi]; show (ofState o₁).S = (ofState o₂).S; rw [e₁, e₂]
  · rw [S₁.esp, S₂.esp]; show (ofState o₁).sp = (ofState o₂).sp; rw [e₁, e₂]

/-- A run's state from which the output is zeroed. -/
def ZAt (p : PPub) (s : State) : Prop :=
  ∃ o ds f, ofState o = p ∧ St o ds f s ∧ Aligned ds ∧ outOff ∈ ds ∧ widthOff ∈ ds ∧ f outOff = arg o 0 ∧
    f widthOff = BitVec.ofNat 32 (arg o 1).toNat

theorem ZAt.any {p : PPub} {s : State} (h : ZAt p s) : Any p s :=
  let ⟨o, ds, f, e, S, _⟩ := h; ⟨o, ds, f, e, S⟩

theorem zeroHead_ok (p : PPub) (s : State) (h : ZAt p s) :
    WP isa (.block [.mov .edx (.mem (st outOff)), .mov .ecx (.mem (st widthOff)), .mov .eax (.imm 0)]) s
      fun t => Any p t ∧ t.gpr .edx = p.op ∧ t.gpr .ecx = BitVec.ofNat 32 p.len := by
  obtain ⟨o, ds, f, rfl, S, _, ho, hw, eo, ew⟩ := h
  refine S.ld (Or.inr (Or.inr rfl)) ho (by decide) fun t₁ S₁ g₁ _ _ _ => ?_
  refine S₁.ld (Or.inr (Or.inl rfl)) hw (by decide) fun t₂ S₂ g₂ o₂ _ _ => ?_
  refine wp_movi fun t₃ U₃ => WP.block_nil ⟨⟨o, ds, f, rfl, S₂.reg U₃ (Or.inl rfl)⟩, ?_, ?_⟩
  · rw [U₃.other _ (by decide), o₂ _ (by decide), g₁, eo]; rfl
  · rw [U₃.other _ (by decide), g₂, ew]; rfl

theorem zeroOut_ct : RelCT isa (Two ZAt) zeroOut fun _ _ => True := by
  unfold zeroOut
  refine RelCT.seq (two_piece (Ψ := fun p t => Any p t ∧ t.gpr .edx = p.op ∧ t.gpr .ecx = BitVec.ofNat 32 p.len)
    [.esi, .esp] (any_pins id fun _ _ h => h.any) (by taint_decide) zeroHead_ok) ?_
  refine two_taint [.edx, .ecx, .esi, .esp] (fun a s₁ s₂ h₁ h₂ r hr => ?_) (by taint_decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | hr
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2, h₂.2.2]
  · exact any_pins (Φ := fun p t => Any p t ∧ t.gpr .edx = p.op ∧ t.gpr .ecx = BitVec.ofNat 32 p.len) id
      (fun _ _ h => h.1) a _ _ h₁ h₂ r (by simpa using hr)

/-- The loop's public data: the descriptor, the octets consumed and the attempts left. -/
abbrev Lp := PPub × Nat × Nat

/-- A loop state at the point `q`. -/
def LiveAt (q : Lp) (s : State) : Prop := ∃ o, Live q.1 o q.2.1 q.2.2 s

theorem LiveAt.any {q : Lp} {s : State} (h : LiveAt q s) : Any q.1 s := by
  obtain ⟨o, L⟩ := h
  exact ⟨o, _, _, L.input.2, L.st⟩

theorem liveAt_pins : Pins LiveAt [.esi, .esp] := any_pins (fun q => q.1) fun _ _ h => h.any

theorem exhausted_ct : RelCT isa (Two LiveAt) exhausted fun _ _ => True := by
  unfold exhausted
  refine RelCT.seq (two_piece (Ψ := fun q t => ZAt q.1 t) [.esi, .esp] liveAt_pins (by taint_decide)
    fun q s ⟨o, L⟩ => ?_) (two_map (fun q => q.1) (fun _ _ h => h) zeroOut_ct)
  obtain ⟨p, used, n⟩ := q
  have S := L.st
  obtain ⟨A, e⟩ := L.input
  subst e
  refine WP.mono (S.terminal liveDs_aligned 3) fun t ⟨Sx, _⟩ => ⟨o, _, _, rfl, Sx, by decide, by decide, by decide,
    ?_, ?_⟩
  all_goals simp [upd, liveF, ofState, outOff, widthOff, statusOff, requestOff, attemptsOff]

theorem request_ct : RelCT isa (Two LiveAt) request fun _ _ => True := by
  unfold request
  refine RelCT.seq (two_piece (Ψ := fun q t => ZAt q.1 t) [.esi, .esp] liveAt_pins (by taint_decide)
    fun q s ⟨o, L⟩ => ?_) (two_map (fun q => q.1) (fun _ _ h => h) zeroOut_ct)
  obtain ⟨p, used, n⟩ := q
  have S := L.st
  obtain ⟨A, e⟩ := L.input
  subst e
  have hc := cap_lt A
  have hr := A.randLen
  have hL := len_pos A
  have ec : (ofState o).cap = parameterEntropy (arg o 3).toNat := rfl
  have el : (ofState o).len = (arg o 1).toNat := rfl
  refine WP.mono (S.requestWords liveDs_aligned (by decide) (by decide) (by decide) (a := (ofState o).randLen - used)
    (L := (ofState o).len) (c := (ofState o).cap) (by simp [liveF, leftOff]) (by simp [liveF, widthOff])
    (by simp [liveF, capOff]) (by rw [ec] at hc; have : (ofState o).randLen = (arg o 6).toNat := rfl; omega)
    (by omega) (by omega)) fun t Sx => ⟨o, _, _, rfl, Sx, by decide, by decide, by decide, ?_, ?_⟩
  all_goals simp [upd, liveF, ofState, outOff, widthOff, statusOff, requestOff]

end VG.Proof.Ffdh.X86.PSearch
