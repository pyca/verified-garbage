module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.Flat

/-!
# Constant time by the states a run reaches

The taint analysis treats memory as secret, so a public value loaded from
memory (a word of a header of addresses and lengths) is secret to it. Cut the
code's list of programs (`Code.flat`) where such values are loaded: `At Φ F n`
holds of the state after the first `n` programs of `F` from a state
satisfying `Φ`. Each run that terminates goes through these states
(`at_step`, by determinism), so the relational proof needs no correctness
facts between the cuts, only the registers each cut fixes (`pins_at`): the
values a correctness proof gives them from the initial state, for the same
public data.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE

variable {α : Type}

/-- After the first `n` programs of `F`, from a state satisfying `Φ a`. -/
def At (Φ : α → State → Prop) (F : List (Prog isa)) (n : Nat) (a : α) (u : State) : Prop :=
  ∃ s₀ t, Φ a s₀ ∧ Exec isa (Code.seqL (F.take n)) s₀ t u

/-- The programs from the `n`th to the `m`th. -/
abbrev seg (F : List (Prog isa)) (n m : Nat) : Prog isa := Code.seqL ((F.drop n).take (m - n))

theorem at_zero {Φ : α → State → Prop} {F : List (Prog isa)} {a : α} {s : State} (h : Φ a s) :
    At Φ F 0 a s :=
  ⟨s, [], h, by rw [List.take_zero]; exact .block rfl⟩

theorem take_split (F : List (Prog isa)) {n m : Nat} (hnm : n ≤ m) :
    F.take m = F.take n ++ (F.drop n).take (m - n) := by
  rw [← List.take_add]; congr 1; omega

theorem drop_split (F : List (Prog isa)) {n m : Nat} (hnm : n ≤ m) :
    F.drop n = (F.drop n).take (m - n) ++ F.drop m := by
  conv => lhs; rw [← List.take_append_drop (m - n) (F.drop n)]
  rw [List.drop_drop]; congr 2; omega

theorem at_step {Φ : α → State → Prop} {F : List (Prog isa)}
    (hrun : ∀ a s, Φ a s → WP isa (Code.seqL F) s fun _ => True) {n m : Nat} (hnm : n ≤ m) {a : α}
    {u : State} (h : At Φ F n a u) : WP isa (seg F n m) u (At Φ F m a) := by
  obtain ⟨s₀, t, h₀, e⟩ := h
  obtain ⟨_, _, eF, -⟩ := hrun a s₀ h₀
  rw [← List.take_append_drop n F, drop_split F hnm] at eF
  obtain ⟨_, _, u', -, e₁, e₂⟩ := exec_seqL_append.mp eF
  obtain ⟨-, rfl⟩ := Exec.det e e₁
  obtain ⟨_, _, v, -, e₃, -⟩ := exec_seqL_append.mp e₂
  exact ⟨_, v, e₃, s₀, _, h₀, by rw [take_split F hnm]; exact exec_seqL_append.mpr ⟨_, _, _, rfl, e, e₃⟩⟩

/-- The registers a cut fixes: each has a value, from the initial state, that
two initial states for the same `a` agree on. -/
theorem pins_at {Φ : α → State → Prop} {F : List (Prog isa)} {n : Nat} {rs : List Reg}
    (V : State → Reg → BitVec 64)
    (hv : ∀ a s₀, Φ a s₀ → WP isa (Code.seqL (F.take n)) s₀ fun u => ∀ r ∈ rs, u.gpr r = V s₀ r)
    (hV : ∀ a s₀ s₀', Φ a s₀ → Φ a s₀' → ∀ r ∈ rs, V s₀ r = V s₀' r) : Pins (At Φ F n) rs := by
  rintro a u₁ u₂ ⟨s₁, t₁, h₁, e₁⟩ ⟨s₂, t₂, h₂, e₂⟩ r hr
  obtain ⟨_, _, x₁, y₁⟩ := hv a s₁ h₁
  obtain ⟨_, _, x₂, y₂⟩ := hv a s₂ h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  rw [y₁ r hr, y₂ r hr, hV a s₁ s₂ h₁ h₂ r hr]

/-- `pins_at`, the values as a list. -/
theorem pins_at_list {Φ : α → State → Prop} {F : List (Prog isa)} {n : Nat} {rs : List Reg}
    (vs : State → List (BitVec 64))
    (hv : ∀ a s₀, Φ a s₀ → WP isa (Code.seqL (F.take n)) s₀ fun u => rs.map u.gpr = vs s₀)
    (hV : ∀ a s₀ s₀', Φ a s₀ → Φ a s₀' → vs s₀ = vs s₀') : Pins (At Φ F n) rs := by
  rintro a u₁ u₂ ⟨s₁, t₁, h₁, e₁⟩ ⟨s₂, t₂, h₂, e₂⟩ r hr
  obtain ⟨_, _, x₁, y₁⟩ := hv a s₁ h₁
  obtain ⟨_, _, x₂, y₂⟩ := hv a s₂ h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact List.map_inj_left.mp (y₁.trans ((hV a s₁ s₂ h₁ h₂).trans y₂.symm)) r hr

theorem at_zero_inv {Φ : α → State → Prop} {F : List (Prog isa)} {a : α} {u : State} (h : At Φ F 0 a u) :
    Φ a u := by
  obtain ⟨s₀, t, h₀, e⟩ := h
  rw [List.take_zero] at e
  obtain ⟨-, rfl⟩ := exec_nil_iff.mp e
  exact h₀

/-- One program, as a list. -/
theorem RelCT.seqL_single {P Q : State → State → Prop} {c : Prog isa} (h : RelCT isa P c Q) :
    RelCT isa P (Code.seqL [c]) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq x₁ y₁ =>
    cases e₂ with
    | seq x₂ y₂ =>
      obtain ⟨rfl, rfl⟩ := exec_nil_iff.mp y₁
      obtain ⟨rfl, rfl⟩ := exec_nil_iff.mp y₂
      obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp x₁ x₂
      exact ⟨by rw [ht], hq⟩

/-- A segment the taint analysis checks, then the rest. -/
theorem chain_cons {Φ : α → State → Prop} {F : List (Prog isa)}
    (hrun : ∀ a s, Φ a s → WP isa (Code.seqL F) s fun _ => True) {n m : Nat} (hnm : n ≤ m)
    (hct : RelCT isa (Two (At Φ F n)) (seg F n m) fun _ _ => True)
    (hrest : RelCT isa (Two (At Φ F m)) (Code.seqL (F.drop m)) fun _ _ => True) :
    RelCT isa (Two (At Φ F n)) (Code.seqL (F.drop n)) fun _ _ => True := by
  rw [drop_split F hnm]
  exact RelCT.seqL_append (two_post hct fun _ _ h => at_step hrun hnm h) hrest

/-- The code, from the cuts. -/
theorem chain_start {Φ : α → State → Prop} {c : Prog isa}
    (h : RelCT isa (Two (At Φ c.flat 0)) (Code.seqL (c.flat.drop 0)) fun _ _ => True) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.of_flat (h.mono (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨a, at_zero h₁, at_zero h₂, hsp⟩) fun _ _ h => h)

end VG.Proof.Bignum.PPC64LE
