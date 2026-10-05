import VerifiedGarbage.Proof.Ocb.Spec

/-!
# OCB: the sum of `HASH` a chunk at a time

Untrusted: everything here is checked by Lean. `Sum_{j+c}` is `Sum_j` with
the `c` enciphered blocks after block `j` added (`hsum_add`); a checksum of
blocks is the spec's when the blocks are (`ckOf_eq`, `ckOf_dck`).
-/

namespace VG.Proof.Ocb

open VG.Spec.Ocb (Block Cipher blockAt)

/-- `x` XORed with `g 0`, …, `g (k − 1)`. -/
def sumOf (x : Block) (g : Nat → Block) : Nat → Block
  | 0 => x
  | k + 1 => sumOf x g k ^^^ g k

theorem hsum_add (ciph : Cipher) (l : Block) (a : List Byte) (j : Nat) :
    ∀ c, hsum ciph l a (j + c) =
      sumOf (hsum ciph l a j) (fun k => ciph (blockAt a (j + k) ^^^ offAt 0 l (j + k + 1))) c
  | 0 => rfl
  | c + 1 => by rw [← Nat.add_assoc, hsum, hsum_add ciph l a j c]; rfl

/-- A checksum of blocks `X i`. -/
def ckOf (X : Nat → Block) : Nat → Block
  | 0 => 0
  | i + 1 => ckOf X i ^^^ X i

theorem ckOf_eq {X : Nat → Block} {p : List Byte} {m : Nat} (h : ∀ i < m, X i = blockAt p i) :
    ckOf X m = ckAt p m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, ckAt, ih (fun i hi => h i (by omega)), h m (by omega)]

theorem ckOf_dck {X : Nat → Block} {inv : Cipher} {o0 l : Block} {c : List Byte} {m : Nat}
    (h : ∀ i < m, X i = decBlock inv o0 l c i) : ckOf X m = dckAt inv o0 l c m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, dckAt, ih (fun i hi => h i (by omega)), h m (by omega)]

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} {m : Nat} (h : ∀ i < m, f i = g i) :
    (List.range m).flatMap f = (List.range m).flatMap g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (fun i hi => h i (by omega))]
    simp only [List.flatMap_cons, List.flatMap_nil, h m (by omega)]

end VG.Proof.Ocb
