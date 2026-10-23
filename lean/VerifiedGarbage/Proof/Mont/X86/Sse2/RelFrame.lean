module

public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Mont.X86.Sse2.Mcdt
import VerifiedGarbage.Proof.Framework.Omega

/-! # Relating two runs through frames and narrowed permissions

`relCT_of_wp`: two runs leak the same, and their final states are related by
what each satisfies by correctness. `relCT_frame`: a frame whose push and pop
leak only addresses of `esp`, around a body whose runs leak the same, leaves
`esp` the same (frames of registers, `push_frame`, and MCDT frames,
`mcdt_frame`). `relCT_nar`: code that writes only the working space `⟨W, L⟩`
leaks the same as it does with only that region writable and every other
readable (`nar`), where a taint analysis can treat the rest as read-only.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86

/-- Two runs leak the same (`h`); their final states are related by what each
satisfies by correctness. -/
theorem relCT_of_wp {P Q : State → State → Prop} {c : Prog isa} (h : RelCT isa P c fun _ _ => True)
    (hw : ∀ s₁ s₂, P s₁ s₂ → ∃ F₁ F₂ : State → Prop, WP isa c s₁ F₁ ∧ WP isa c s₂ F₂ ∧
      ∀ u₁ u₂, F₁ u₁ → F₂ u₂ → Q u₁ u₂) :
    RelCT isa P c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := h _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨F₁, F₂, ⟨_, u₁, f₁, g₁⟩, ⟨_, u₂, f₂, g₂⟩, hq⟩ := hw _ _ hp
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht, hq _ _ g₁ g₂⟩

/-- A frame whose push leaks the same addresses and leaves `esp` and the
frame's size the same in both runs, and whose pop leaks addresses of `esp`. -/
theorem relCT_frame {i j : Instr} {body : Prog isa} {P R : State → State → Prop}
    (hpush : ∀ s₁ s₂ a₁ a₂, P s₁ s₂ → isa.push i s₁ = some a₁ → isa.push i s₂ = some a₂ →
      isa.addrs i s₁ = isa.addrs i s₂ ∧ a₁.gpr .esp = a₂.gpr .esp ∧
        a₁.wr.head?.map Region.len = a₂.wr.head?.map Region.len)
    (hpop : ∀ b₁ b₂ : State, b₁.gpr .esp = b₂.gpr .esp → isa.addrs j b₁ = isa.addrs j b₂)
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ isa.push i s₁ = some a ∧ isa.push i s₂ = some b) body R) :
    RelCT isa P (.frame i body j) fun c₁ c₂ => c₁.gpr .esp = c₂.gpr .esp := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain ⟨ha, hsp, hl⟩ := hpush _ _ _ _ hp p₁ p₂
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨_, _, hp, p₁, p₂⟩ b₁ b₂
      obtain ⟨-, -, -, -, e₁', k₁, l₁, hk₁, hk₁', hh₁, g₁⟩ := pop_eq q₁
      obtain ⟨-, -, -, -, e₂', k₂, l₂, hk₂, hk₂', hh₂, g₂⟩ := pop_eq q₂
      have hb' := e₁'.trans (hsp.trans e₂'.symm)
      rw [hh₁, hh₂] at hl
      simp only [Option.map_some, Option.some.injEq] at hl
      have hk : k₁ = k₂ := by omega
      refine ⟨by rw [ha, hpop _ _ hb'], ?_⟩
      show s₁'.gpr .esp = s₂'.gpr .esp
      rw [g₁, g₂, hb', hk]

/-- A frame of registers' push, for runs with the same `esp`. -/
theorem push_frame {rs : List Reg} {P : State → State → Prop}
    (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.gpr .esp = s₂.gpr .esp) :
    ∀ s₁ s₂ a₁ a₂, P s₁ s₂ → isa.push (.push rs) s₁ = some a₁ → isa.push (.push rs) s₂ = some a₂ →
      isa.addrs (.push rs) s₁ = isa.addrs (.push rs) s₂ ∧ a₁.gpr .esp = a₂.gpr .esp ∧
        a₁.wr.head?.map Region.len = a₂.wr.head?.map Region.len := by
  intro s₁ s₂ a₁ a₂ hp h₁ h₂
  obtain ⟨-, -, -, rfl⟩ := push_some h₁
  obtain ⟨-, -, -, rfl⟩ := push_some h₂
  have e := hsp _ _ hp
  exact ⟨by simp only [addrs, e], by rw [pushed_esp, pushed_esp, e], by rw [pushed_wr, pushed_wr]; rfl⟩

theorem pop_addrs (r : Reg) (k : Nat) : ∀ b₁ b₂ : State, b₁.gpr .esp = b₂.gpr .esp →
    isa.addrs (.pop r k) b₁ = isa.addrs (.pop r k) b₂ := by
  intro b₁ b₂ h; simp only [addrs, h]

theorem mcdt_push_eq {r : Reg} {s a : State} (h : isa.push (.mcdtEnter r) s = some a) :
    r ≠ .esp ∧ a = mcdtPushed r s := by
  simp only [isa, push] at h
  split at h <;> [rename_i hc; cases h]
  cases h
  exact ⟨hc.1, rfl⟩

/-- An MCDT frame's push, for runs with the same `esp`. -/
theorem mcdt_frame {r : Reg} {P : State → State → Prop}
    (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.gpr .esp = s₂.gpr .esp) :
    ∀ s₁ s₂ a₁ a₂, P s₁ s₂ → isa.push (.mcdtEnter r) s₁ = some a₁ → isa.push (.mcdtEnter r) s₂ = some a₂ →
      isa.addrs (.mcdtEnter r) s₁ = isa.addrs (.mcdtEnter r) s₂ ∧ a₁.gpr .esp = a₂.gpr .esp ∧
        a₁.wr.head?.map Region.len = a₂.wr.head?.map Region.len := by
  intro s₁ s₂ a₁ a₂ hp h₁ h₂
  obtain ⟨hr, rfl⟩ := mcdt_push_eq h₁
  obtain ⟨-, rfl⟩ := mcdt_push_eq h₂
  have e := hsp _ _ hp
  exact ⟨by simp only [addrs, e], by rw [mcdtPushed_esp _ _ hr, mcdtPushed_esp _ _ hr, e],
    by rw [mcdtPushed_wr, mcdtPushed_wr]; rfl⟩

theorem mcdtLeave_addrs : ∀ b₁ b₂ : State, b₁.gpr .esp = b₂.gpr .esp →
    isa.addrs .mcdtLeave b₁ = isa.addrs .mcdtLeave b₂ := by
  intro b₁ b₂ h; simp only [addrs, h]

/-- `s` with only the working space `⟨W, L⟩` writable, and every region readable. -/
def nar (s : State) (W : Addr) (L : Nat) : State := s.withRegions (s.rd ++ s.wr) [⟨W, L⟩]

theorem nar_gpr (s : State) (W : Addr) (L : Nat) : (nar s W L).gpr = s.gpr := rfl
theorem nar_mem (s : State) (W : Addr) (L : Nat) : (nar s W L).mem = s.mem := rfl
theorem nar_wr (s : State) (W : Addr) (L : Nat) : (nar s W L).wr = [⟨W, L⟩] := rfl
theorem nar_rdwr (s : State) (W : Addr) (L : Nat) :
    (nar s W L).rd ++ (nar s W L).wr = s.rd ++ s.wr ++ [⟨W, L⟩] := rfl

/-- A run from `s` is one from `nar s W L` when the code runs from there. -/
theorem nar_trace {c : Prog isa} {s t : State} {W : Addr} {L : Nat} (hw : (⟨W, L⟩ : Region) ∈ s.wr)
    {Q : State → Prop} (H : WP isa c (nar s W L) Q) {tr : List Leak} (E : Exec isa c s tr t) :
    ∃ u, Exec isa c (nar s W L) tr u := by
  obtain ⟨tr', u, EU, _⟩ := H
  have read : Covers ((s.rd ++ s.wr) ++ [⟨W, L⟩]) (s.rd ++ s.wr) := fun a n ⟨r, hr, hc⟩ =>
    ⟨r, by
      rcases List.mem_append.mp hr with h | h
      · exact h
      · rw [List.mem_singleton.mp h]; exact List.mem_append_right _ hw, hc⟩
  have write : Covers [⟨W, L⟩] s.wr := fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; exact hw, hc⟩
  have EW := VG.X86.Exec.widen EU read write
  simp only [nar, State.withRegions_withRegions, State.withRegions_self] at EW
  obtain ⟨rfl, _⟩ := Exec.det E EW
  exact ⟨u, EU⟩

/-- Code that runs from the narrowed states leaks the same from the states,
when it is constant-time from the narrowed states. -/
theorem relCT_nar {c : Prog isa} {P Pub : State → State → Prop} {W : Addr} {L : Nat}
    (hct : ConstantTime isa (fun _ => True) Pub c)
    (h : ∀ s₁ s₂, P s₁ s₂ → (⟨W, L⟩ : Region) ∈ s₁.wr ∧ (⟨W, L⟩ : Region) ∈ s₂.wr ∧
      (∃ Q, WP isa c (nar s₁ W L) Q) ∧ (∃ Q, WP isa c (nar s₂ W L) Q) ∧ Pub (nar s₁ W L) (nar s₂ W L)) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨w₁, w₂, ⟨_, H₁⟩, ⟨_, H₂⟩, hpub⟩ := h _ _ hp
  obtain ⟨_, E₁⟩ := nar_trace w₁ H₁ e₁
  obtain ⟨_, E₂⟩ := nar_trace w₂ H₂ e₂
  exact ⟨hct _ _ _ _ _ _ trivial trivial hpub E₁ E₂, trivial⟩

end VG.Proof.Mont.X86.Sse2
