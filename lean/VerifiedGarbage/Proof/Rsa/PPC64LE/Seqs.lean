module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyArrays
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
public import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Flat

/-!
# Sequences of programs on PPC64LE

`wp_seqs_cons`, `wp_seqs_append`: the weakest precondition of `seqs`, piece
by piece; `RelCT.cut`, `WP.cut`: a code cut where its pieces (`Code.flat`)
split, wherever its sequences nest (`flat_seqs`); `idx`: the index side
conditions of the key working space's arrays.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Keys

open VG VG.PPC64LE
open VG.Impl.Rsa.PPC64LE.Keys (seqs aM aNM aZero aT1 aT2 aT3 aT4 sOdd sB sC)

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

/-- The pieces of `seqs l`. -/
theorem flat_seqs : ∀ {l : List (Prog isa)}, l ≠ [] → (seqs l).flat = l.flatMap Code.flat
  | [c], _ => by simp [seqs]
  | c :: d :: l, _ => by
    rw [show seqs (c :: d :: l) = .seq c (seqs (d :: l)) from rfl, Code.flat, flat_seqs (List.cons_ne_nil _ _),
      List.flatMap_cons]
    simp only [List.flatMap_cons]

/-- A code related in two parts whose pieces are its own. -/
theorem RelCT.cut {P R Q : State → State → Prop} {c a b : Prog isa} (hc : c.flat = a.flat ++ b.flat)
    (h₁ : RelCT isa P a R) (h₂ : RelCT isa R b Q) : RelCT isa P c Q :=
  RelCT.of_flat (hc ▸ RelCT.seqL_append
    (fun _ _ _ _ _ _ hp e₁ e₂ => h₁ _ _ _ _ _ _ hp (exec_flat.mpr e₁) (exec_flat.mpr e₂))
    (fun _ _ _ _ _ _ hp e₁ e₂ => h₂ _ _ _ _ _ _ hp (exec_flat.mpr e₁) (exec_flat.mpr e₂)))

/-- A code's run, in two parts whose pieces are its own. -/
theorem WP.cut {c a b : Prog isa} (hc : c.flat = a.flat ++ b.flat) {s : State} {Q : State → Prop}
    (h : WP isa c s Q) : WP isa a s fun u => WP isa b u Q := by
  obtain ⟨t, s', e, hq⟩ := h
  have e' := exec_flat.mp e
  rw [hc] at e'
  obtain ⟨t₁, t₂, u, -, e₁, e₂⟩ := exec_seqL_append.mp e'
  exact ⟨t₁, u, exec_flat.mpr e₁, t₂, s', exec_flat.mpr e₂, hq⟩

/-- Index side conditions. -/
macro "idx" : tactic => `(tactic| ((try simp only [aM, aNM, aZero, aT1, aT2, aT3, aT4, sOdd, sB, sC,
  VG.Proof.Rsa.KeyWorkspace.hdr,
  List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, ne_eq]) <;>
    omega_arith))

end VG.Proof.Rsa.PPC64LE.Keys
