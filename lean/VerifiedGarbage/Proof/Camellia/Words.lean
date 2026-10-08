import VerifiedGarbage.Spec.Camellia

/-!
# Camellia in terms of the words of a table of subkeys

The implementations bitslice the subkeys into a table in the order their
rounds use them, and run the same rounds for both directions. `cryptWords g E`
is that computation, for `g` groups of six rounds and the table's words
`E 0 … E (8 g + 1)`: the prewhitening with `E 0` and `E 1`, group `i`'s
pairs of rounds with `E (2 + 8 i + 2 p)` and `E (3 + 8 i + 2 p)`, FL and
FLINV with `E (8 + 8 i)` and `E (9 + 8 i)` after every group but the last,
and the postwhitening with `E (8 g)` and `E (8 g + 1)`.

`encryptWith_eq` says encryption under the subkeys of a stored schedule is
`cryptWords` on its words, and `decryptWith_eq` that decryption is
`cryptWords` on them in the order `decPerm` (RFC 3713 §2.3.3's swaps).
-/

namespace VG.Proof.Camellia

open VG.Spec.Camellia

/-- Two rounds: `D2 ^= F(D1, k₁)`, then `D1 ^= F(D2, k₂)`. -/
def pair (k₁ k₂ : BitVec 64) (d : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  let d2 := d.2 ^^^ f d.1 k₁
  (d.1 ^^^ f d2 k₂, d2)

/-- Group `i` of six rounds, then FL and FLINV unless it is the last of `g`. -/
def group (g : Nat) (E : Nat → BitVec 64) (d : BitVec 64 × BitVec 64) (i : Nat) :
    BitVec 64 × BitVec 64 :=
  let d := pair (E (2 + 8 * i)) (E (3 + 8 * i)) d
  let d := pair (E (4 + 8 * i)) (E (5 + 8 * i)) d
  let d := pair (E (6 + 8 * i)) (E (7 + 8 * i)) d
  if i + 1 < g then (fl d.1 (E (8 + 8 * i)), flinv d.2 (E (9 + 8 * i))) else d

/-- The rounds on the halves, after the prewhitening. -/
def groups (g : Nat) (E : Nat → BitVec 64) (d : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  (List.range g).foldl (group g E) d

def cryptWords (g : Nat) (E : Nat → BitVec 64) (m : BitVec 128) : BitVec 128 :=
  let d := groups g E ((m >>> 64).setWidth 64 ^^^ E 0, m.setWidth 64 ^^^ E 1)
  (d.2 ^^^ E (8 * g)) ++ (d.1 ^^^ E (8 * g + 1))

/-- The order of the words for decryption: `kw3, kw4`, the words between
`kw2` and `kw3` from the last back, then `kw1, kw2`. -/
def decPerm (g i : Nat) : Nat :=
  if i < 2 then 8 * g + i else if i < 8 * g then 8 * g + 1 - i else i - 8 * g

theorem encryptWith_eq {R : Nat} (hR : R = 18 ∨ R = 24) (ws : List (BitVec 64)) (m : BitVec 128) :
    encryptWith (subkeysOfWords R ws) m = cryptWords (R / 6) (fun i => ws.getD i 0) m := by
  rcases hR with rfl | rfl <;>
  simp [encryptWith, subkeysOfWords, cryptWords, groups, group, pair, List.range_succ,
    List.flatMap_cons]

theorem decryptWith_eq {R : Nat} (hR : R = 18 ∨ R = 24) (ws : List (BitVec 64)) (m : BitVec 128) :
    decryptWith (subkeysOfWords R ws) m = cryptWords (R / 6) (fun i => ws.getD (decPerm (R / 6) i) 0) m := by
  rcases hR with rfl | rfl <;>
  simp [decryptWith, reverseSubkeys, encryptWith, subkeysOfWords, cryptWords, groups, group, pair,
    List.range_succ, List.flatMap_cons, decPerm]

end VG.Proof.Camellia
