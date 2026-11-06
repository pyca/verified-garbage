module

public import VerifiedGarbage.Proof.Modes.Ctr
public import VerifiedGarbage.Spec.Cfb.Final

/-!
# CFB of a message's last piece, for any block cipher and target

A final function calls a whole-block CFB function on the `n = len / L`
whole blocks of its data, which leaves the last ciphertext block `c` in the
IV, then, if `r = len % L` bytes are left, the whole-block encryption on a
zero block, which leaves `CIPH_K(c)` both there and in the IV, and XORs its
first `r` bytes into them. When it has, its data and block are
`Spec.Cfb.encryptFinal`'s and `encryptFinalNext`'s (`cfbEncFinal_of`,
`cfbEncFinalNext_of`), or `decryptFinal`'s and `decryptFinalNext`'s
(`cfbDecFinal_of`, `cfbDecFinalNext_of`). Nothing here depends on a cipher
or a target.
-/

@[expose] public section

namespace VG.Proof.Modes

open VG
open VG.Spec.Aes (bytesAt)

theorem bytesAt_length (m : Mem) (D : Addr) (len : Nat) : (bytesAt m D len).length = len := by
  simp [bytesAt]

theorem bytesAt_add (m : Mem) (D : Addr) (a b : Nat) :
    bytesAt m D (a + b) = bytesAt m D a ++ bytesAt m (D + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map, Function.comp_def, BitVec.ofNat_add,
    BitVec.add_assoc]

theorem bytesAt_drop (m : Mem) (D : Addr) (len a : Nat) :
    (bytesAt m D len).drop a = bytesAt m (D + BitVec.ofNat 64 a) (len - a) := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h1 _
  simp only [bytesAt, List.getElem_drop, List.getElem_map, List.getElem_range, BitVec.ofNat_add, BitVec.add_assoc]

theorem bytesAt_take (m : Mem) (D : Addr) {len k : Nat} (h : k ≤ len) :
    (bytesAt m D len).take k = bytesAt m D k := by
  apply List.ext_getElem (by simp [bytesAt]; omega)
  intro i _ _
  simp only [bytesAt, List.getElem_take, List.getElem_map, List.getElem_range]

theorem blocksOf_succ' (L : Nat) (m : Mem) (D : Addr) (n : Nat) :
    blocksOf L m D (n + 1) = blocksOf L m D n ++ [bytesAt m (D + BitVec.ofNat 64 (L * n)) L] := by
  simp [blocksOf, List.range_succ]

/-- `L n` bytes, as `n` blocks. -/
theorem bytesAt_mul (L : Nat) (m : Mem) (D : Addr) : ∀ n, bytesAt m D (L * n) = (blocksOf L m D n).flatten
  | 0 => by simp [bytesAt, blocksOf]
  | n + 1 => by
    rw [Nat.mul_succ, bytesAt_add, bytesAt_mul L m D n, blocksOf_succ', List.flatten_append, List.flatten_singleton]

/-- The whole segments of the `len` bytes at `D`: its `len / L` blocks. -/
theorem segments_bytesAt {L : Nat} (m : Mem) (D : Addr) (len : Nat) :
    Spec.Cfb.segments L (bytesAt m D len) = blocksOf L m D (len / L) := by
  simp only [Spec.Cfb.segments, bytesAt_length, blocksOf]
  apply List.map_congr_left
  intro i hi
  have hi : i < len / L := List.mem_range.mp hi
  have hle : L * i + L ≤ len := by
    have := Nat.mul_le_mul_left L (Nat.succ_le_of_lt hi)
    rw [Nat.mul_succ] at this
    exact Nat.le_trans this (Nat.mul_div_le len L)
  rw [bytesAt_drop, bytesAt_take _ _ (by omega)]

/-- The partial last segment of the `len` bytes at `D`: its last `len % L`
bytes. -/
theorem tail_bytesAt (L : Nat) (m : Mem) (D : Addr) (len : Nat) :
    Spec.Cfb.tail L (bytesAt m D len) = bytesAt m (D + BitVec.ofNat 64 (L * (len / L))) (len % L) := by
  rw [Spec.Cfb.tail, bytesAt_length, bytesAt_drop, Nat.mod_eq_sub_mul_div]

theorem tail_eq_nil_iff (L : Nat) (m : Mem) (D : Addr) (len : Nat) :
    Spec.Cfb.tail L (bytesAt m D len) = [] ↔ len % L = 0 := by
  rw [tail_bytesAt, ← List.length_eq_zero_iff, bytesAt_length]

/-- The `len` bytes at `D`: its whole blocks, then the rest. -/
theorem bytesAt_blocks_tail (L : Nat) (m : Mem) (D : Addr) (len : Nat) :
    bytesAt m D len = (blocksOf L m D (len / L)).flatten ++
      bytesAt m (D + BitVec.ofNat 64 (L * (len / L))) (len % L) := by
  have h := bytesAt_add m D (L * (len / L)) (len % L)
  rw [Nat.div_add_mod] at h
  rw [h, bytesAt_mul]

/-- CFB encryption of the `len` bytes at `D` by a final function (see
above): its `n = len / L` whole blocks replaced by `Spec.Cfb.encrypt`'s
from `iv`, leaving `c`, the last ciphertext block (`Cbc.next`), and its last
`len % L` bytes XORed with `CIPH_K(c)`. -/
theorem cfbEncFinal_of {L : Nat} (ciph : Spec.Cbc.Cipher) (m₀ m' : Mem) (D : Addr) (iv : List Byte) (len : Nat)
    (hblocks : blocksOf L m' D (len / L) = Spec.Cfb.encrypt ciph iv (blocksOf L m₀ D (len / L)))
    (htail : bytesAt m' (D + BitVec.ofNat 64 (L * (len / L))) (len % L) =
      Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 (L * (len / L))) (len % L))
        (ciph (Spec.Cbc.next iv (Spec.Cfb.encrypt ciph iv (blocksOf L m₀ D (len / L)))))) :
    bytesAt m' D len = Spec.Cfb.encryptFinal ciph L iv (bytesAt m₀ D len) := by
  rw [bytesAt_blocks_tail L m' D len, hblocks, htail, Spec.Cfb.encryptFinal, segments_bytesAt, tail_bytesAt]

/-- The block a final function leaves after CFB encryption: the last
ciphertext block `c` if `len` is a multiple of `L`, and `CIPH_K(c)`
otherwise. -/
theorem cfbEncFinalNext_of {L : Nat} (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (len : Nat) :
    (let c := Spec.Cbc.next iv (Spec.Cfb.encrypt ciph iv (blocksOf L m₀ D (len / L)))
      if len % L = 0 then c else ciph c) = Spec.Cfb.encryptFinalNext ciph L iv (bytesAt m₀ D len) := by
  simp only [Spec.Cfb.encryptFinalNext, segments_bytesAt, tail_eq_nil_iff]

/-- CFB decryption of the `len` bytes at `D` by a final function (see
above): its whole blocks replaced by `Spec.Cfb.decrypt`'s from `iv`, and its
last `len % L` bytes XORed with `CIPH_K(c)`, `c` the last whole ciphertext
block (`Cbc.next`). -/
theorem cfbDecFinal_of {L : Nat} (ciph : Spec.Cbc.Cipher) (m₀ m' : Mem) (D : Addr) (iv : List Byte) (len : Nat)
    (hblocks : blocksOf L m' D (len / L) = Spec.Cfb.decrypt ciph iv (blocksOf L m₀ D (len / L)))
    (htail : bytesAt m' (D + BitVec.ofNat 64 (L * (len / L))) (len % L) =
      Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 (L * (len / L))) (len % L))
        (ciph (Spec.Cbc.next iv (blocksOf L m₀ D (len / L))))) :
    bytesAt m' D len = Spec.Cfb.decryptFinal ciph L iv (bytesAt m₀ D len) := by
  rw [bytesAt_blocks_tail L m' D len, hblocks, htail, Spec.Cfb.decryptFinal, segments_bytesAt, tail_bytesAt]

/-- The block a final function leaves after CFB decryption. -/
theorem cfbDecFinalNext_of {L : Nat} (ciph : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (iv : List Byte) (len : Nat) :
    (let c := Spec.Cbc.next iv (blocksOf L m₀ D (len / L))
      if len % L = 0 then c else ciph c) = Spec.Cfb.decryptFinalNext ciph L iv (bytesAt m₀ D len) := by
  simp only [Spec.Cfb.decryptFinalNext, segments_bytesAt, tail_eq_nil_iff]

end VG.Proof.Modes
