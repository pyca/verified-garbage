module

public import VerifiedGarbage.Proof.Rsa.Arm.KeyEq
public import VerifiedGarbage.Impl.Rsa.Arm.Inverse
public import VerifiedGarbage.Proof.Rsa.InverseArithmetic
public import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.RelCT
import Batteries.Tactic.Alias

/-! # Sequences of the RSA key operations on ARMv7, and the side conditions of their indices -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm
open VG.Proof.Rsa (subMod halfMod)

theorem wp_seqs_cons {c : Prog isa} {l : List (Prog isa)} (hl : l ≠ []) {s : State} {Q : State → Prop} :
    WP isa (seqs (c :: l)) s Q ↔ WP isa c s (fun t => WP isa (seqs l) t Q) := by
  match l, hl with
  | _ :: _, _ => exact WP.seq_iff

theorem wp_seqs_append {l₁ l₂ : List (Prog isa)} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) {s : State}
    {Q : State → Prop} :
    WP isa (seqs (l₁ ++ l₂)) s Q ↔ WP isa (seqs l₁) s (fun t => WP isa (seqs l₂) t Q) := by
  induction l₁ generalizing s with
  | nil => exact absurd rfl h₁
  | cons c l ih =>
    rcases l with _ | ⟨d, l⟩
    · exact wp_seqs_cons h₂
    · rw [List.cons_append, wp_seqs_cons (by simp), wp_seqs_cons (by simp)]
      exact ⟨fun h => WP.mono h fun t ht => (ih (by simp)).mp ht,
        fun h => WP.mono h fun t ht => (ih (by simp)).mpr ht⟩

/-! ## Regrouping a list of programs -/

theorem seqs_single (c : Prog isa) : seqs [c] = c := rfl

theorem exec_seq_inv {a b : Prog isa} {s s' : State} {tr : List Leak} (h : Exec isa (.seq a b) s tr s') :
    ∃ u tr₁ tr₂, tr = tr₁ ++ tr₂ ∧ Exec isa a s tr₁ u ∧ Exec isa b u tr₂ s' := by
  cases h with
  | seq e₁ e₂ => exact ⟨_, _, _, rfl, e₁, e₂⟩

theorem exec_seqs_append {l₂ : List (Prog isa)} (h₂ : l₂ ≠ []) :
    ∀ {l₁ : List (Prog isa)}, l₁ ≠ [] → ∀ {s : State} {tr s'},
      Exec isa (seqs (l₁ ++ l₂)) s tr s' → Exec isa (.seq (seqs l₁) (seqs l₂)) s tr s' := by
  intro l₁
  induction l₁ with
  | nil => intro h; exact absurd rfl h
  | cons c l ih =>
    intro _ s tr s' e
    rcases l with _ | ⟨d, l⟩
    · obtain ⟨x, l₂', rfl⟩ := List.exists_cons_of_ne_nil h₂
      exact e
    · obtain ⟨u, tr₁, tr₂, rfl, e₁, e₂⟩ := exec_seq_inv (a := c) (b := seqs ((d :: l) ++ l₂)) e
      obtain ⟨u', tr₃, tr₄, rfl, e₃, e₄⟩ := exec_seq_inv (ih (List.cons_ne_nil _ _) e₂)
      rw [← List.append_assoc]
      exact .seq (.seq e₁ e₃) e₄

theorem exec_seqs_join : ∀ {ls : List (List (Prog isa))}, (∀ l ∈ ls, l ≠ []) → ls ≠ [] → ∀ {s : State} {tr s'},
    Exec isa (seqs ls.flatten) s tr s' → Exec isa (seqs (ls.map seqs)) s tr s' := by
  intro ls
  induction ls with
  | nil => intro _ h; exact absurd rfl h
  | cons l rest ih =>
    intro h _ s tr s' e
    rcases rest with _ | ⟨l', rest⟩
    · rw [List.flatten_cons, List.flatten_nil, List.append_nil] at e
      exact e
    · rw [List.flatten_cons] at e
      have ne : (l' :: rest).flatten ≠ [] := by
        rw [List.flatten_cons]
        exact List.append_ne_nil_of_left_ne_nil (h l' (by simp)) _
      obtain ⟨u, tr₁, tr₂, rfl, e₁, e₂⟩ := exec_seq_inv (exec_seqs_append ne (h l (by simp)) e)
      exact .seq e₁ (ih (fun l hl => h l (List.mem_cons_of_mem _ hl)) (List.cons_ne_nil _ _) e₂)

theorem RelCT.of_join {P Q : State → State → Prop} {ls : List (List (Prog isa))} (h₁ : ∀ l ∈ ls, l ≠ [])
    (h₂ : ls ≠ []) (h : RelCT isa P (seqs (ls.map seqs)) Q) : RelCT isa P (seqs ls.flatten) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (exec_seqs_join h₁ h₂ e₁) (exec_seqs_join h₁ h₂ e₂)

/-- Index side conditions. -/
macro "idx" : tactic => `(tactic| ((try simp only [aM, aNM, aZero, aT1, aT2, aT3, aT4, sOdd, sB, sC, sT,
  List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, hdr, ne_eq]) <;> omega_arith))

end VG.Proof.Rsa.Arm.Keys
