module

public import VerifiedGarbage.Proof.Framework.Bitslice.Lanes

/-!
# The lanes of a layer whose bits are XORs of the same terms

A check of a linear layer compares what the code computes with `mk w g w`,
the lanes holding the atoms `g q` of every bit `q` (`Lanes.lean`). For
MixColumns and its inverse `g q` is a list of a dozen atoms that the kernel
evaluates, from the specification's tables, for every `q` of every output
word, and adds to the lanes one at a time: ten times what running the
code takes. But every bit is the XOR of the same terms `l`, each at the
bit's own position (`g q = l.map (f q)`), so the lanes are the XOR over `l`
of each term's lanes at every position (`mk_map`): a few patterns, which a
table holds, XORed.
-/

@[expose] public section

namespace VG.Bitslice

theorem atomsAt_append (w q : Nat) (l₁ l₂ : List Nat) :
    atomsAt w q (l₁ ++ l₂) = atomsAt w q l₁ ^^^ atomsAt w q l₂ := by
  induction l₁ with
  | nil => simp only [List.nil_append, atomsAt, Nat.zero_xor]
  | cons a l ih => simp only [List.cons_append, atomsAt, ih, Nat.xor_assoc]

theorem mk_nil (w n : Nat) : mk w (fun _ => []) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [mk, ih, atomsAt, Nat.xor_zero]

theorem mk_append (w : Nat) (g₁ g₂ : Nat → List Nat) (n : Nat) :
    mk w (fun p => g₁ p ++ g₂ p) n = mk w g₁ n ^^^ mk w g₂ n := by
  induction n with
  | zero => simp only [mk, Nat.xor_zero]
  | succ n ih =>
    simp only [mk, ih, atomsAt_append]
    rw [Nat.xor_assoc, Nat.xor_assoc, ← Nat.xor_assoc (mk w g₂ n), Nat.xor_comm (mk w g₂ n),
      Nat.xor_assoc]

/-- The lanes of a layer whose bit `p` is the XOR of the atoms `f p x` for `x` in `l`: the XOR over
`l` of the lanes of the one atom `f p x` at every `p`. -/
theorem mk_map {β : Type} (w : Nat) (f : Nat → β → Nat) (l : List β) (n : Nat) :
    mk w (fun p => l.map (f p)) n = l.foldr (fun x acc => mk w (fun p => [f p x]) n ^^^ acc) 0 := by
  induction l with
  | nil => exact mk_nil w n
  | cons x l ih =>
    show mk w (fun p => [f p x] ++ l.map (f p)) n = _
    rw [mk_append, ih]; rfl

end VG.Bitslice
