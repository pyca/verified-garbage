module

public import VerifiedGarbage.Proof.Modes.CbcEnc

/-!
# CBC's chaining value to continue from, for any block cipher and target

`Spec.Cbc.next` of CBC encryption's ciphertext is its last block,
`cbcEncC (n - 1)` (`next_encrypt`), and of the ciphertext a decryption
reads, the last block of the data (`next_blocksOf`); both are the IV if
`n = 0`. `bytesAt_of_getD` reads a block out of memory byte by byte.
Nothing here depends on a cipher or a target.
-/

@[expose] public section

namespace VG.Proof.Modes

open VG
open VG.Spec.Aes (bytesAt)

theorem getLastD_map_range {α : Type} (f : Nat → α) (d : α) (n : Nat) :
    ((List.range (n + 1)).map f).getLastD d = f n := by
  rw [List.range_succ, List.map_append, List.map_singleton, List.getLastD_eq_getLast?, List.getLast?_append]
  simp

theorem next_encrypt {L : Nat} (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) {n : Nat}
    (hn : n ≠ 0) :
    Spec.Cbc.next iv (Spec.Cbc.encrypt ciph iv (blocksOf L m₀ D n)) = cbcEncC L ciph m₀ D iv (n - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [encrypt_eq, Spec.Cbc.next, getLastD_map_range, Nat.succ_sub_one]

theorem next_blocksOf (L : Nat) (m₀ : Mem) (D : Addr) (iv : List Byte) {n : Nat} (hn : n ≠ 0) :
    Spec.Cbc.next iv (blocksOf L m₀ D n) = bytesAt m₀ (D + BitVec.ofNat 64 (L * (n - 1))) L := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [blocksOf, Spec.Cbc.next, getLastD_map_range, Nat.succ_sub_one]

theorem next_nil (iv : List Byte) : Spec.Cbc.next iv [] = iv := rfl

/-- The `L` bytes at `P` are `xs`, of length `L`, when each is. -/
theorem bytesAt_of_getD {m : Mem} {P : Addr} {L : Nat} {xs : List Byte} (hl : xs.length = L)
    (h : ∀ u < L, m (P + BitVec.ofNat 64 u) = xs.getD u 0) : bytesAt m P L = xs := by
  apply List.ext_getElem (by simp [bytesAt, hl])
  intro u h1 _
  have hu : u < L := by simpa [bytesAt] using h1
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [h u hu, List.getElem_eq_getD 0]

end VG.Proof.Modes
