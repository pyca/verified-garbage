import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Gcm.Bits

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.Spec`. -/
section

/-!
# GCM: lemmas about the specification
-/

namespace VG.Proof.Gcm

open VG.Spec.Gcm

/-- Step `i` of Algorithm 1 (`Spec.Gcm.mul`) on `(Z, V)`, for the factor `x`. -/
def mulStep (x : VG.Spec.Gcm.Block) (zv : VG.Spec.Gcm.Block × VG.Spec.Gcm.Block) (i : Nat) : VG.Spec.Gcm.Block × VG.Spec.Gcm.Block :=
  (if x.getMsbD i then zv.1 ^^^ zv.2 else zv.1,
   if zv.2.getLsbD 0 then (zv.2 >>> 1) ^^^ R else zv.2 >>> 1)

/-- The first `k` steps of Algorithm 1 for `x • y`. -/
def mulSteps (x y : VG.Spec.Gcm.Block) (k : Nat) : VG.Spec.Gcm.Block × VG.Spec.Gcm.Block :=
  (List.range k).foldl (VG.Proof.Gcm.mulStep x) (0, y)

theorem mul_eq (x y : VG.Spec.Gcm.Block) : mul x y = (VG.Proof.Gcm.mulSteps x y 128).1 := rfl

theorem mulSteps_zero (x y : VG.Spec.Gcm.Block) : VG.Proof.Gcm.mulSteps x y 0 = (0, y) := rfl

theorem mulSteps_succ (x y : VG.Spec.Gcm.Block) (k : Nat) :
    VG.Proof.Gcm.mulSteps x y (k + 1) = VG.Proof.Gcm.mulStep x (VG.Proof.Gcm.mulSteps x y k) k := by
  simp only [VG.Proof.Gcm.mulSteps, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem ghashFrom_blocksAt_succ (h y : VG.Spec.Gcm.Block) (m : Mem) (p : Addr) (i : Nat) :
    ghashFrom h y (VG.Spec.Gcm.blocksAt m p (i + 1)) =
      mul (ghashFrom h y (VG.Spec.Gcm.blocksAt m p i) ^^^ VG.Spec.Gcm.blockAt m (p + BitVec.ofNat 64 (16 * i))) h := by
  simp only [ghashFrom, VG.Spec.Gcm.blocksAt, List.range_succ, List.map_append, List.foldl_append,
    List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]

theorem ghashFrom_blocksAt_zero (h y : VG.Spec.Gcm.Block) (m : Mem) (p : Addr) :
    ghashFrom h y (VG.Spec.Gcm.blocksAt m p 0) = y := rfl

/-- `blockAt` only depends on the 16 bytes of the block. -/
theorem blockAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ i < 16, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    VG.Spec.Gcm.blockAt m' p = VG.Spec.Gcm.blockAt m p := by
  simp only [VG.Spec.Gcm.blockAt, Spec.Aes.bytesAt]
  congr 1
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem toNat_append {n k : Nat} (x : BitVec n) (y : BitVec k) :
    (x ++ y).toNat = x.toNat * 2 ^ k + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

/-- A block from its 16 bytes, the first the most significant. -/
theorem ofBytes_16 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Byte) :
    ofBytes [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] =
      ((b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 : BitVec 64) ++
        (b8 ++ b9 ++ b10 ++ b11 ++ b12 ++ b13 ++ b14 ++ b15 : BitVec 64) : BitVec 128) := by
  apply BitVec.eq_of_toNat_eq
  simp only [ofBytes, List.foldl_cons, List.foldl_nil, VG.Proof.Gcm.toNat_append, BitVec.toNat_ofNat]
  have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt; have := b4.isLt
  have := b5.isLt; have := b6.isLt; have := b7.isLt; have := b8.isLt; have := b9.isLt
  have := b10.isLt; have := b11.isLt; have := b12.isLt; have := b13.isLt; have := b14.isLt
  have := b15.isLt
  omega

end VG.Proof.Gcm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.Stream`. -/
section

/-!
# GCM: GHASH and counter mode over a message given in pieces

Untrusted: everything here is checked by Lean. Target-independent lemmas
about the steps the implementations of AES-GCM take (on every target):

* GHASH absorbs a string `x` a piece at a time (`Absorbed`): the whole
  blocks into the accumulator `Y`, the rest buffered. A piece is absorbed by
  filling the buffer (`absorb_fill`, `absorb_complete`), then whole blocks
  (`absorb_whole`), then buffering the rest (`absorb_tail`); the buffer is
  padded with zeros and absorbed (`absorb_pad`).
* Counter mode XORs the `i`-th byte of the keystream (`ksByte`) into the
  `i`-th byte of the text (`gctr_eq`), whose counter block and keystream
  block the state keeps (`Ctr`).
-/

namespace VG.Proof.Gcm

open VG VG.Spec.Gcm
open VG.Spec.Aes (bytesAt)

/-! ## Blocks and GHASH -/

theorem ghashFrom_append (h y : Block) (xs ys : List Block) :
    ghashFrom h y (xs ++ ys) = ghashFrom h (ghashFrom h y xs) ys := by
  simp only [ghashFrom, List.foldl_append]

theorem ghashFrom_nil (h y : Block) : ghashFrom h y [] = y := rfl

theorem length_blocks (bs : List Byte) : (blocks bs).length = bs.length / 16 := by
  simp [blocks]

theorem blocks_of_lt {bs : List Byte} (h : bs.length < 16) : blocks bs = [] := by
  simp [blocks, Nat.div_eq_of_lt h]

theorem blocks_cons {bs : List Byte} (h : 16 ≤ bs.length) :
    blocks bs = ofBytes (bs.take 16) :: blocks (bs.drop 16) := by
  obtain ⟨n, hn⟩ : ∃ n, bs.length / 16 = n + 1 := ⟨bs.length / 16 - 1, by omega⟩
  have hn' : (bs.drop 16).length / 16 = n := by simp only [List.length_drop]; omega
  simp only [blocks, hn, hn', List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp, List.drop_drop]
  congr 3
  omega

theorem blocks_append_aux (ys : List Byte) (n : Nat) :
    ∀ xs : List Byte, xs.length = 16 * n → blocks (xs ++ ys) = blocks xs ++ blocks ys := by
  induction n with
  | zero => intro xs hx; rw [List.eq_nil_of_length_eq_zero hx]; rfl
  | succ n ih =>
    intro xs hx
    rw [VG.Proof.Gcm.blocks_cons (bs := xs ++ ys) (by simp; omega), VG.Proof.Gcm.blocks_cons (bs := xs) (by omega),
      List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
      ih _ (by simp; omega), List.cons_append]

theorem blocks_append {xs ys : List Byte} (hx : xs.length % 16 = 0) :
    blocks (xs ++ ys) = blocks xs ++ blocks ys :=
  VG.Proof.Gcm.blocks_append_aux ys (xs.length / 16) xs (by omega)

theorem blocks_single {bs : List Byte} (h : bs.length = 16) : blocks bs = [ofBytes bs] := by
  rw [VG.Proof.Gcm.blocks_cons (by omega), List.take_of_length_le (by omega),
    VG.Proof.Gcm.blocks_of_lt (by simp; omega)]

theorem blocks_nil : blocks [] = [] := rfl

/-- The `n` blocks at `p` are the blocks of their bytes. -/
theorem blocksAt_eq (m : Mem) (p : Addr) (n : Nat) : blocksAt m p n = blocks (bytesAt m p (16 * n)) := by
  simp only [blocksAt, blocks, Cmac.bytesAt_length, Nat.mul_div_cancel_left _ (by decide : 0 < 16)]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [blockAt]
  congr 1
  apply List.ext_getElem (by simp [bytesAt]; omega)
  intro j h₁ h₂
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-! ## Absorbing a string a piece at a time -/

/-- The bytes of `x` in whole blocks. -/
abbrev whole (n : Nat) : Nat := 16 * (n / 16)

/-- GHASH, with the hash subkey `h`, has absorbed `x`: the accumulator at `y`
is `GHASH_H` of the whole blocks of `x`, and the rest of `x` (less than a
block) is the first bytes at `b`. -/
def Absorbed (m : Mem) (y b : Addr) (h : Block) (x : List Byte) : Prop :=
  blockAt m y = ghash h (blocks (x.take (VG.Proof.Gcm.whole x.length))) ∧
    bytesAt m b (x.length % 16) = x.drop (VG.Proof.Gcm.whole x.length)

theorem take_whole_append {x d : List Byte} (hx : x.length % 16 = 0) :
    (x ++ d).take (VG.Proof.Gcm.whole (x ++ d).length) = x ++ d.take (VG.Proof.Gcm.whole d.length) := by
  rw [List.take_append, List.take_of_length_le (by simp only [VG.Proof.Gcm.whole, List.length_append]; omega)]
  congr 2
  simp only [VG.Proof.Gcm.whole, List.length_append]; omega

theorem drop_whole_append {x d : List Byte} (hx : x.length % 16 = 0) :
    (x ++ d).drop (VG.Proof.Gcm.whole (x ++ d).length) = d.drop (VG.Proof.Gcm.whole d.length) := by
  rw [List.drop_append, List.drop_of_length_le (show x.length ≤ _ by
    simp only [VG.Proof.Gcm.whole, List.length_append]; omega), List.nil_append]
  congr 1
  simp only [VG.Proof.Gcm.whole, List.length_append]; omega

theorem whole_of_mod {n : Nat} (h : n % 16 = 0) : VG.Proof.Gcm.whole n = n := by simp only [VG.Proof.Gcm.whole]; omega

/-- Nothing absorbed: a zero accumulator. -/
theorem absorbed_nil {m : Mem} {y b : Addr} (h : Block) (hy : blockAt m y = 0) :
    VG.Proof.Gcm.Absorbed m y b h [] := ⟨hy, rfl⟩

/-- `Absorbed` only depends on the accumulator and the buffered bytes. -/
theorem Absorbed.congr {m m' : Mem} {y b : Addr} {h : Block} {x : List Byte} (hx : VG.Proof.Gcm.Absorbed m y b h x)
    (hy : blockAt m' y = blockAt m y) (hb : bytesAt m' b (x.length % 16) = bytesAt m b (x.length % 16)) :
    VG.Proof.Gcm.Absorbed m' y b h x := ⟨hy.trans hx.1, hb.trans hx.2⟩

/-- Whole blocks absorbed into the accumulator, after a whole number of
blocks. -/
theorem absorb_whole {m m' : Mem} {y b : Addr} {h : Block} {x d : List Byte} (hx : VG.Proof.Gcm.Absorbed m y b h x)
    (hx0 : x.length % 16 = 0) (hd : d.length % 16 = 0)
    (hy : blockAt m' y = ghashFrom h (blockAt m y) (blocks d)) : VG.Proof.Gcm.Absorbed m' y b h (x ++ d) := by
  refine ⟨?_, ?_⟩
  · rw [hy, hx.1, VG.Proof.Gcm.take_whole_append hx0, VG.Proof.Gcm.whole_of_mod hd, List.take_of_length_le (Nat.le_refl _),
      List.take_of_length_le (by rw [VG.Proof.Gcm.whole_of_mod hx0]), VG.Proof.Gcm.blocks_append hx0]
    exact (VG.Proof.Gcm.ghashFrom_append _ _ _ _).symm
  · have hl : (x ++ d).length % 16 = 0 := by simp only [List.length_append]; omega
    rw [hl, List.drop_of_length_le (by rw [VG.Proof.Gcm.whole_of_mod hl])]; rfl

/-- The last bytes (less than a block) buffered, after a whole number of
blocks. -/
theorem absorb_tail {m m' : Mem} {y b : Addr} {h : Block} {x d : List Byte} (hx : VG.Proof.Gcm.Absorbed m y b h x)
    (hx0 : x.length % 16 = 0) (hd : d.length < 16)
    (hy : blockAt m' y = blockAt m y) (hb : bytesAt m' b d.length = d) : VG.Proof.Gcm.Absorbed m' y b h (x ++ d) := by
  have hw : VG.Proof.Gcm.whole d.length = 0 := by simp only [VG.Proof.Gcm.whole]; rw [Nat.div_eq_of_lt hd]
  refine ⟨?_, ?_⟩
  · rw [hy, hx.1, VG.Proof.Gcm.take_whole_append hx0, hw, List.take_zero, List.append_nil,
      List.take_of_length_le (by rw [VG.Proof.Gcm.whole_of_mod hx0])]
  · rw [VG.Proof.Gcm.drop_whole_append hx0, hw, List.drop_zero, List.length_append, Nat.add_mod, hx0, Nat.zero_add,
      Nat.mod_mod, Nat.mod_eq_of_lt hd, hb]

/-- Filling the buffer, but not to a whole block. -/
theorem absorb_fill {m m' : Mem} {y b : Addr} {h : Block} {x d : List Byte} (hx : VG.Proof.Gcm.Absorbed m y b h x)
    (hfit : x.length % 16 + d.length < 16) (hy : blockAt m' y = blockAt m y)
    (hb : bytesAt m' b (x.length % 16 + d.length) = bytesAt m b (x.length % 16) ++ d) :
    VG.Proof.Gcm.Absorbed m' y b h (x ++ d) := by
  have hl : (x ++ d).length / 16 = x.length / 16 := by simp only [List.length_append]; omega
  have hm : (x ++ d).length % 16 = x.length % 16 + d.length := by simp only [List.length_append]; omega
  have hw : VG.Proof.Gcm.whole (x ++ d).length = VG.Proof.Gcm.whole x.length := by simp only [VG.Proof.Gcm.whole, hl]
  have hle : VG.Proof.Gcm.whole x.length ≤ x.length := by simp only [VG.Proof.Gcm.whole]; omega
  refine ⟨?_, ?_⟩
  · rw [hy, hx.1, hw, List.take_append_of_le_length hle]
  · rw [hm, hb, hx.2, hw, List.drop_append_of_le_length hle]

/-- Filling the buffer to a whole block `B` (the buffered bytes, then `d`),
which is absorbed. -/
theorem absorb_complete {m m' : Mem} {y b : Addr} {h : Block} {x d : List Byte} (hx : VG.Proof.Gcm.Absorbed m y b h x)
    (hfit : x.length % 16 + d.length = 16) {B : List Byte} (hB : B = x.drop (VG.Proof.Gcm.whole x.length) ++ d)
    (hy : blockAt m' y = ghashFrom h (blockAt m y) [ofBytes B]) : VG.Proof.Gcm.Absorbed m' y b h (x ++ d) := by
  have hle : VG.Proof.Gcm.whole x.length ≤ x.length := by simp only [VG.Proof.Gcm.whole]; omega
  have hl : (x ++ d).length % 16 = 0 := by simp only [List.length_append]; omega
  have hw : VG.Proof.Gcm.whole (x ++ d).length = VG.Proof.Gcm.whole x.length + 16 := by
    rw [VG.Proof.Gcm.whole_of_mod hl]; simp only [List.length_append, VG.Proof.Gcm.whole]; omega
  have hBl : B.length = 16 := by rw [hB]; simp only [List.length_append, List.length_drop, VG.Proof.Gcm.whole]; omega
  refine ⟨?_, ?_⟩
  · have hsplit : (x ++ d).take (VG.Proof.Gcm.whole (x ++ d).length) =
        x.take (VG.Proof.Gcm.whole x.length) ++ (x.drop (VG.Proof.Gcm.whole x.length) ++ d) := by
      rw [List.take_of_length_le (by rw [hw]; simp only [List.length_append, VG.Proof.Gcm.whole]; omega),
        ← List.append_assoc, List.take_append_drop]
    have hlen : (x.take (VG.Proof.Gcm.whole x.length)).length % 16 = 0 := by
      rw [List.length_take, Nat.min_eq_left hle]; simp only [VG.Proof.Gcm.whole]; omega
    rw [hy, hx.1, hsplit, VG.Proof.Gcm.blocks_append hlen, ← hB, VG.Proof.Gcm.blocks_single hBl]
    exact (VG.Proof.Gcm.ghashFrom_append _ _ _ _).symm
  · rw [hl, List.drop_of_length_le (by rw [hw]; simp only [List.length_append, VG.Proof.Gcm.whole]; omega)]
    rfl

theorem padLen_lt (n : Nat) : padLen n < 16 := by simp only [padLen]; omega

theorem length_zeros (n : Nat) : (zeros n).length = n := by simp [zeros]

/-- The buffer padded with zeros to a block `B`, which is absorbed: `x ‖ 0ᵘ`. -/
theorem absorb_pad {m m' : Mem} {y b : Addr} {h : Block} {x : List Byte} (hx : VG.Proof.Gcm.Absorbed m y b h x)
    (h0 : x.length % 16 ≠ 0) {B : List Byte}
    (hB : B = bytesAt m b (x.length % 16) ++ zeros (16 - x.length % 16))
    (hy : blockAt m' y = ghashFrom h (blockAt m y) [ofBytes B]) :
    VG.Proof.Gcm.Absorbed m' y b h (x ++ zeros (padLen x.length)) := by
  have hp : padLen x.length = 16 - x.length % 16 := by simp only [padLen]; omega
  refine VG.Proof.Gcm.absorb_complete hx (by rw [VG.Proof.Gcm.length_zeros, hp]; omega) ?_ hy
  rw [hB, hx.2, hp]

/-- With nothing buffered, there is no padding. -/
theorem padLen_of_mod {n : Nat} (h : n % 16 = 0) : padLen n = 0 := by simp only [padLen]; omega

end VG.Proof.Gcm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.Ctr`. -/
section

/-!
# GCM: counter mode over a text given in pieces

Untrusted: everything here is checked by Lean. `GCTR_K(ICB, X)` XORs byte
`i` of the keystream `CIPH_K(CB₁) ‖ CIPH_K(CB₂) ‖ …` (`ksByte`) into byte `i`
of `X` (`gctr_eq`), so the text from byte `n` on is XORed with the keystream
from byte `n` on (`xorKs`). The state keeps the next counter block and,
within a block, the keystream block (`Ctr`); a piece of text is XORed with
the rest of that block (`ctr_head`), whole blocks with `vg_aes_ctr32`
(`ctr_whole`) and the last bytes with a new keystream block (`ctr_tail`).
-/

namespace VG.Proof.Gcm

open VG VG.Spec.Gcm
open VG.Spec.Aes (bytesAt)

/-- `Nat.repeat` composes. -/
theorem repeat_add (f : Block → Block) (a b : Nat) (x : Block) :
    Nat.repeat f (a + b) x = Nat.repeat f a (Nat.repeat f b x) := by
  induction a with
  | zero => simp [Nat.repeat]
  | succ a ih => rw [Nat.add_right_comm, Nat.repeat, ih]; rfl

/-- Byte `i` of the keystream from the counter block `icb`. -/
def ksByte (ciph : Block → Block) (icb : Block) (i : Nat) : Byte :=
  (toBytes (ciph (Nat.repeat inc32 (i / 16) icb))).getD (i % 16) 0

/-- `d` XORed with the keystream from byte `n` on. -/
def xorKs (ciph : Block → Block) (icb : Block) (n : Nat) (d : List Byte) : List Byte :=
  (List.range d.length).map fun i => d.getD i 0 ^^^ VG.Proof.Gcm.ksByte ciph icb (n + i)

theorem length_xorKs (ciph : Block → Block) (icb : Block) (n : Nat) (d : List Byte) :
    (VG.Proof.Gcm.xorKs ciph icb n d).length = d.length := by simp [VG.Proof.Gcm.xorKs]

theorem getD_xorKs (ciph : Block → Block) (icb : Block) (n : Nat) (d : List Byte) {i : Nat}
    (hi : i < d.length) : (VG.Proof.Gcm.xorKs ciph icb n d).getD i 0 = d.getD i 0 ^^^ VG.Proof.Gcm.ksByte ciph icb (n + i) := by
  simp [VG.Proof.Gcm.xorKs, List.getD_eq_getElem?_getD, hi]

theorem list_ext {x y : List Byte} (hl : x.length = y.length)
    (h : ∀ k < x.length, x.getD k 0 = y.getD k 0) : x = y := by
  apply List.ext_getElem hl
  intro k h₁ h₂
  have := h k h₁
  simpa [List.getD_eq_getElem?_getD, h₁, h₂] using this

theorem xorKs_append (ciph : Block → Block) (icb : Block) (n : Nat) (d e : List Byte) :
    VG.Proof.Gcm.xorKs ciph icb n (d ++ e) = VG.Proof.Gcm.xorKs ciph icb n d ++ VG.Proof.Gcm.xorKs ciph icb (n + d.length) e := by
  simp only [VG.Proof.Gcm.xorKs, List.length_append, List.range_add, List.map_append, List.map_map]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left this]
  · refine List.map_congr_left fun i hi => ?_
    simp only [Function.comp, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left, Nat.add_assoc]

theorem xorKs_nil (ciph : Block → Block) (icb : Block) (n : Nat) : VG.Proof.Gcm.xorKs ciph icb n [] = [] := rfl

theorem getD_flatMap_toBytes (L : List Block) :
    ∀ i, i < 16 * L.length → (L.flatMap toBytes).getD i 0 = (toBytes (L.getD (i / 16) 0)).getD (i % 16) 0 := by
  induction L with
  | nil => intro i hi; simp at hi
  | cons a L ih =>
    intro i hi
    rw [List.flatMap_cons, List.getD_eq_getElem?_getD]
    by_cases h : i < 16
    · rw [List.getElem?_append_left (by rw [Cmac.toBytes_length]; exact h), ← List.getD_eq_getElem?_getD,
        Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      rfl
    · rw [List.getElem?_append_right (by rw [Cmac.toBytes_length]; omega), Cmac.toBytes_length,
        ← List.getD_eq_getElem?_getD, ih (i - 16) (by simp at hi; omega)]
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 16 := ⟨i - 16, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_div_right _ (by decide), Nat.add_mod_right]
      rfl

theorem length_flatMap_toBytes (L : List Block) : (L.flatMap toBytes).length = 16 * L.length := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.flatMap_cons, List.length_append, ih, Cmac.toBytes_length]; simp; omega

theorem getD_bytesAt' (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) :
    (bytesAt m p n).getD k 0 = m (p + BitVec.ofNat 64 k) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hk]

/-- A XOR with the bytes `L` is one with the keystream from byte `n` on. -/
theorem zipWith_eq_xorKs {ciph : Block → Block} {icb : Block} {n : Nat} {d L : List Byte}
    (hl : L.length = d.length) (h : ∀ k < d.length, L.getD k 0 = VG.Proof.Gcm.ksByte ciph icb (n + k)) :
    List.zipWith (· ^^^ ·) d L = VG.Proof.Gcm.xorKs ciph icb n d := by
  refine VG.Proof.Gcm.list_ext (by simp [VG.Proof.Gcm.length_xorKs, hl]) fun k hk => ?_
  simp only [List.length_zipWith, hl, Nat.min_self] at hk
  rw [VG.Proof.Gcm.getD_xorKs _ _ _ _ hk, ← h k hk]
  simp [List.getD_eq_getElem?_getD, hk, hl]

/-- `GCTR` XORs the keystream into the text. -/
theorem gctr_eq (ciph : Block → Block) (icb : Block) (x : List Byte) :
    gctr ciph icb x = VG.Proof.Gcm.xorKs ciph icb 0 x := by
  have hlen : ((keystream ciph icb ((x.length + 15) / 16)).flatMap toBytes).length =
      16 * ((x.length + 15) / 16) := by
    rw [VG.Proof.Gcm.length_flatMap_toBytes]; simp [keystream]
  refine VG.Proof.Gcm.list_ext (by simp [gctr, VG.Proof.Gcm.length_xorKs, hlen]; omega) fun i hi => ?_
  simp only [gctr, List.length_zipWith] at hi
  have hix : i < x.length := by omega
  rw [VG.Proof.Gcm.getD_xorKs _ _ _ _ hix, Nat.zero_add, gctr, List.getD_eq_getElem?_getD, List.getElem?_zipWith,
    List.getElem?_eq_getElem hix, List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some]
  congr 1
  · simp [List.getD_eq_getElem?_getD, hix]
  · have := VG.Proof.Gcm.getD_flatMap_toBytes (keystream ciph icb ((x.length + 15) / 16)) i
      (by simp [keystream]; omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    rw [this, VG.Proof.Gcm.ksByte]
    congr 2
    simp [keystream, List.getD_eq_getElem?_getD, show i / 16 < (x.length + 15) / 16 by omega]

/-- `GCTR` of a text given in two pieces. -/
theorem gctr_append (ciph : Block → Block) (icb : Block) (p d : List Byte) :
    gctr ciph icb (p ++ d) = gctr ciph icb p ++ VG.Proof.Gcm.xorKs ciph icb p.length d := by
  rw [VG.Proof.Gcm.gctr_eq, VG.Proof.Gcm.gctr_eq, VG.Proof.Gcm.xorKs_append, Nat.zero_add]

theorem length_gctr (ciph : Block → Block) (icb : Block) (p : List Byte) :
    (gctr ciph icb p).length = p.length := by rw [VG.Proof.Gcm.gctr_eq, VG.Proof.Gcm.length_xorKs]

/-- `GCTR` twice is the identity. -/
theorem gctr_gctr (ciph : Block → Block) (icb : Block) (p : List Byte) :
    gctr ciph icb (gctr ciph icb p) = p := by
  rw [VG.Proof.Gcm.gctr_eq, VG.Proof.Gcm.gctr_eq]
  refine VG.Proof.Gcm.list_ext (by simp [VG.Proof.Gcm.length_xorKs]) fun k hk => ?_
  simp only [VG.Proof.Gcm.length_xorKs] at hk
  rw [VG.Proof.Gcm.getD_xorKs _ _ _ _ (by rw [VG.Proof.Gcm.length_xorKs]; exact hk), VG.Proof.Gcm.getD_xorKs _ _ _ _ hk, BitVec.xor_assoc,
    BitVec.xor_self, BitVec.xor_zero]

/-- One block of `GCTR`. -/
theorem gctr_block (ciph : Block → Block) (j s : Block) :
    gctr ciph j (toBytes s) = toBytes (s ^^^ ciph j) := by
  rw [VG.Proof.Gcm.gctr_eq]
  refine VG.Proof.Gcm.list_ext (by simp [VG.Proof.Gcm.length_xorKs, Cmac.toBytes_length]) fun k hk => ?_
  simp only [VG.Proof.Gcm.length_xorKs, Cmac.toBytes_length] at hk
  rw [VG.Proof.Gcm.getD_xorKs _ _ _ _ (by rw [Cmac.toBytes_length]; exact hk), Proof.Aes.toBytes_xor _ _ hk, VG.Proof.Gcm.ksByte,
    Nat.zero_add, Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk]
  rfl

/-! ## The counter state -/

/-- The counter block at `cb` and the keystream block at `ks` after `n` bytes
of text: the next counter block, `inc₃₂^⌈n/16⌉(ICB)`, and, within a block,
that block's keystream. -/
def Ctr (m : Mem) (cb ks : Addr) (ciph : Block → Block) (icb : Block) (n : Nat) : Prop :=
  blockAt m cb = Nat.repeat inc32 ((n + 15) / 16) icb ∧
    (n % 16 ≠ 0 → blockAt m ks = ciph (Nat.repeat inc32 (n / 16) icb))

theorem Ctr.congr {m m' : Mem} {cb ks : Addr} {ciph : Block → Block} {icb : Block} {n : Nat}
    (h : VG.Proof.Gcm.Ctr m cb ks ciph icb n) (hc : blockAt m' cb = blockAt m cb) (hk : blockAt m' ks = blockAt m ks) :
    VG.Proof.Gcm.Ctr m' cb ks ciph icb n := ⟨hc.trans h.1, fun h0 => hk.trans (h.2 h0)⟩

theorem ctr_zero (m : Mem) (cb ks : Addr) (ciph : Block → Block) {icb : Block}
    (h : blockAt m cb = icb) : VG.Proof.Gcm.Ctr m cb ks ciph icb 0 := ⟨h, fun h0 => absurd rfl h0⟩

theorem bytes_toBytes_blockAt (m : Mem) (p : Addr) {k : Nat} (hk : k < 16) :
    m (p + BitVec.ofNat 64 k) = (toBytes (blockAt m p)).getD k 0 := (Proof.Aes.toBytes_blockAt m p hk).symm

/-- Within a keystream block: the `k` bytes of text `d` XORed with the
keystream block's bytes from `n mod 16` on. -/
theorem ctr_head {m : Mem} {cb ks : Addr} {ciph : Block → Block} {icb : Block} {n : Nat}
    (h : VG.Proof.Gcm.Ctr m cb ks ciph icb n) (h0 : n % 16 ≠ 0) {d : List Byte} (hk : n % 16 + d.length ≤ 16) :
    List.zipWith (· ^^^ ·) d (bytesAt m (ks + BitVec.ofNat 64 (n % 16)) d.length) = VG.Proof.Gcm.xorKs ciph icb n d := by
  refine VG.Proof.Gcm.zipWith_eq_xorKs (Cmac.bytesAt_length _ _ _) fun k hk' => ?_
  rw [VG.Proof.Gcm.getD_bytesAt' _ _ hk', BitVec.add_assoc, ← BitVec.ofNat_add,
    VG.Proof.Gcm.bytes_toBytes_blockAt m ks (k := n % 16 + k) (by omega), h.2 h0, VG.Proof.Gcm.ksByte,
    show (n + k) / 16 = n / 16 by omega, show (n + k) % 16 = n % 16 + k by omega]

/-- Within a keystream block, the state is that for `n + k` bytes. -/
theorem Ctr.head {m : Mem} {cb ks : Addr} {ciph : Block → Block} {icb : Block} {n k : Nat}
    (h : VG.Proof.Gcm.Ctr m cb ks ciph icb n) (h0 : n % 16 ≠ 0) (hk : n % 16 + k ≤ 16) : VG.Proof.Gcm.Ctr m cb ks ciph icb (n + k) := by
  refine ⟨?_, fun h1 => ?_⟩
  · rw [h.1]; congr 1; omega
  · rw [h.2 h0]; congr 2; omega

theorem length_blocksAt (m : Mem) (p : Addr) (n : Nat) : (blocksAt m p n).length = n := by
  simp [blocksAt]

theorem blocksAt_getD (m : Mem) (p : Addr) (n : Nat) {q : Nat} (hq : q < n) :
    (blocksAt m p n).getD q 0 = blockAt m (p + BitVec.ofNat 64 (16 * q)) := by
  simp [blocksAt, List.getD_eq_getElem?_getD, hq]

theorem ctr32_getD (ciph : Block → Block) (icb : Block) (xs : List Block) {q : Nat} (hq : q < xs.length) :
    (ctr32 ciph icb xs).getD q 0 = xs.getD q 0 ^^^ ciph (Nat.repeat inc32 q icb) := by
  simp [ctr32, keystream, List.getD_eq_getElem?_getD, hq]

/-- Whole blocks, from a whole number of blocks: `vg_aes_ctr32`. -/
theorem ctr_whole {m m' : Mem} {cb ks dp : Addr} {ciph : Block → Block} {icb : Block} {n nb : Nat}
    (h : VG.Proof.Gcm.Ctr m cb ks ciph icb n) (h0 : n % 16 = 0)
    (hd : blocksAt m' dp nb = ctr32 ciph (blockAt m cb) (blocksAt m dp nb))
    (hc : blockAt m' cb = Nat.repeat inc32 nb (blockAt m cb)) :
    bytesAt m' dp (16 * nb) = VG.Proof.Gcm.xorKs ciph icb n (bytesAt m dp (16 * nb)) ∧ VG.Proof.Gcm.Ctr m' cb ks ciph icb (n + 16 * nb) := by
  have hcb : blockAt m cb = Nat.repeat inc32 (n / 16) icb := by rw [h.1]; congr 1; omega
  refine ⟨?_, ?_, fun h1 => absurd (by omega) h1⟩
  · refine VG.Proof.Gcm.list_ext (by simp [VG.Proof.Gcm.length_xorKs, Cmac.bytesAt_length]) fun k hk => ?_
    simp only [Cmac.bytesAt_length] at hk
    rw [VG.Proof.Gcm.getD_xorKs _ _ _ _ (by rw [Cmac.bytesAt_length]; exact hk), VG.Proof.Gcm.getD_bytesAt' _ _ hk,
      VG.Proof.Gcm.getD_bytesAt' _ _ hk]
    have hq : k / 16 < nb := by omega
    have e₁ := congrArg (fun L => L.getD (k / 16) 0) hd
    rw [VG.Proof.Gcm.ctr32_getD _ _ _ (by rw [VG.Proof.Gcm.length_blocksAt]; exact hq), VG.Proof.Gcm.blocksAt_getD _ _ _ hq,
      VG.Proof.Gcm.blocksAt_getD _ _ _ hq] at e₁
    have ea : dp + BitVec.ofNat 64 k = dp + BitVec.ofNat 64 (16 * (k / 16)) + BitVec.ofNat 64 (k % 16) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
    rw [ea, VG.Proof.Gcm.bytes_toBytes_blockAt m' _ (by omega), VG.Proof.Gcm.bytes_toBytes_blockAt m _ (by omega), e₁,
      Proof.Aes.toBytes_xor _ _ (by omega), VG.Proof.Gcm.ksByte, hcb, ← VG.Proof.Gcm.repeat_add,
      show (n + k) / 16 = k / 16 + n / 16 by omega, show (n + k) % 16 = k % 16 by omega]
  · rw [hc, hcb, ← VG.Proof.Gcm.repeat_add]; congr 1; omega

/-- The last bytes, from a whole number of blocks: a keystream block from
`vg_aes_ctr32` (of the counter block on a zero block), XORed in. -/
theorem ctr_tail {m m₁ : Mem} {cb ks : Addr} {ciph : Block → Block} {icb : Block} {n : Nat}
    (h : VG.Proof.Gcm.Ctr m cb ks ciph icb n) (h0 : n % 16 = 0)
    (hk : blockAt m₁ ks = ciph (blockAt m cb)) (hc : blockAt m₁ cb = inc32 (blockAt m cb))
    {d : List Byte} (hd : d.length < 16) (hd0 : d.length ≠ 0) :
    List.zipWith (· ^^^ ·) d (bytesAt m₁ ks d.length) = VG.Proof.Gcm.xorKs ciph icb n d ∧ VG.Proof.Gcm.Ctr m₁ cb ks ciph icb (n + d.length) := by
  have hcb : blockAt m cb = Nat.repeat inc32 (n / 16) icb := by rw [h.1]; congr 1; omega
  refine ⟨?_, ?_, fun _ => ?_⟩
  · refine VG.Proof.Gcm.zipWith_eq_xorKs (Cmac.bytesAt_length _ _ _) fun k hk' => ?_
    rw [VG.Proof.Gcm.getD_bytesAt' _ _ hk', VG.Proof.Gcm.bytes_toBytes_blockAt m₁ ks (k := k) (by omega), hk, hcb, VG.Proof.Gcm.ksByte,
      show (n + k) / 16 = n / 16 by omega, show (n + k) % 16 = k by omega]
  · rw [hc, hcb, show (n + d.length + 15) / 16 = n / 16 + 1 by omega]; rfl
  · rw [hk, hcb, show (n + d.length) / 16 = n / 16 by omega]

end VG.Proof.Gcm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.Compose`. -/
section

/-!
# GCM: the streaming state, the tag and the pre-counter block

Untrusted: everything here is checked by Lean. Target-independent lemmas
relating the steps of `Stream.lean` and `Ctr.lean` to `StreamRepr`,
`fullTag` and `j0`:

* `streamRepr_iff`: the state is `J₀`, GHASH having absorbed
  `ghashInput a c` (`Absorbed`) and the counter state after `len(C)` bytes
  (`Ctr`).
* `ghashInput_append`: more text, after the additional data padded (if it
  is the first text).
* `fullTag_eq`: the tag from GHASH having absorbed `ghashInput a c` padded
  with zeros, then the lengths block, XORed with `CIPH_K(J₀)`.
* `j0_eq`: `J₀` for an IV other than 12 bytes is GHASH having absorbed the IV
  padded, then the lengths block of no additional data and the IV.
* `inc32_bytes`: `inc₃₂` increments the last four bytes, big-endian.
-/

namespace VG.Proof.Gcm

open VG VG.Spec.Gcm
open VG.Spec.Aes (bytesAt)

theorem streamRepr_iff {m : Mem} {p : Addr} {ciph : Block → Block} {h : Block} {iv a c : List Byte} :
    StreamRepr m p ciph h iv a c ↔
      blockAt m p = j0 h iv ∧ VG.Proof.Gcm.Absorbed m (p + 16) (p + 32) h (ghashInput a c) ∧
        VG.Proof.Gcm.Ctr m (p + 48) (p + 64) ciph (inc32 (j0 h iv)) c.length := by
  simp only [StreamRepr, VG.Proof.Gcm.Absorbed, VG.Proof.Gcm.Ctr, VG.Proof.Gcm.whole, and_assoc]

/-! ## What GHASH absorbs -/

theorem ghashInput_nil (a : List Byte) : ghashInput a [] = a := rfl

theorem ghashInput_of_ne {a c : List Byte} (hc : c ≠ []) :
    ghashInput a c = a ++ zeros (padLen a.length) ++ c := by simp [ghashInput, hc]

/-- More text: the additional data padded first, if there was no text. -/
theorem ghashInput_append (a c e : List Byte) (he : e ≠ []) :
    ghashInput a (c ++ e) = (if c = [] then a ++ zeros (padLen a.length) else ghashInput a c) ++ e := by
  have hce : c ++ e ≠ [] := by simp [he]
  rw [VG.Proof.Gcm.ghashInput_of_ne hce]
  split
  · next h => subst h; rfl
  · next h => rw [VG.Proof.Gcm.ghashInput_of_ne h]; simp only [List.append_assoc]

theorem length_pad_mod (n : Nat) : (n + padLen n) % 16 = 0 := by simp only [padLen]; omega

/-- The lengths block `[len(A)]₆₄ ‖ [len(C)]₆₄`. -/
def lensBlock (aLen cLen : Nat) : List Byte := be64 (8 * aLen) ++ be64 (8 * cLen)

theorem length_be64 (x : Nat) : (be64 x).length = 8 := by simp [be64]

theorem length_lensBlock (aLen cLen : Nat) : (VG.Proof.Gcm.lensBlock aLen cLen).length = 16 := by
  simp [VG.Proof.Gcm.lensBlock, VG.Proof.Gcm.length_be64]

/-- `ghashInput a c` padded with zeros to a whole number of blocks. -/
def padded (a c : List Byte) : List Byte :=
  ghashInput a c ++ zeros (padLen (ghashInput a c).length)

theorem length_padded (a c : List Byte) : (VG.Proof.Gcm.padded a c).length % 16 = 0 := by
  simp only [VG.Proof.Gcm.padded, List.length_append, VG.Proof.Gcm.length_zeros]; exact VG.Proof.Gcm.length_pad_mod _

/-- `S`'s blocks: the padded input, then the lengths block. -/
theorem authBlocks_eq (a c : List Byte) :
    authBlocks a c = blocks (VG.Proof.Gcm.padded a c) ++ [ofBytes (VG.Proof.Gcm.lensBlock a.length c.length)] := by
  rw [← VG.Proof.Gcm.blocks_single (VG.Proof.Gcm.length_lensBlock _ _), ← VG.Proof.Gcm.blocks_append (VG.Proof.Gcm.length_padded a c)]
  unfold authBlocks VG.Proof.Gcm.padded VG.Proof.Gcm.lensBlock
  by_cases hc : c = []
  · subst hc; simp [VG.Proof.Gcm.ghashInput_nil, zeros, padLen]
  · rw [VG.Proof.Gcm.ghashInput_of_ne hc]
    have : padLen (a ++ zeros (padLen a.length) ++ c).length = padLen c.length := by
      simp only [List.length_append, VG.Proof.Gcm.length_zeros, padLen]; omega
    rw [this]; simp only [List.append_assoc]

/-- GHASH having absorbed a whole number of blocks. -/
theorem Absorbed.whole_eq {m : Mem} {y b : Addr} {h : Block} {x : List Byte} (hx : VG.Proof.Gcm.Absorbed m y b h x)
    (h0 : x.length % 16 = 0) : blockAt m y = ghash h (blocks x) := by
  rw [hx.1, List.take_of_length_le (by rw [VG.Proof.Gcm.whole_of_mod h0])]

/-- The tag: GHASH of the padded input continued over the lengths block,
XORed with `CIPH_K(J₀)`. -/
theorem fullTag_eq (ciph : Block → Block) (h : Block) (iv a c : List Byte) :
    fullTag ciph h iv a c =
      toBytes (ghashFrom h (ghash h (blocks (VG.Proof.Gcm.padded a c))) [ofBytes (VG.Proof.Gcm.lensBlock a.length c.length)] ^^^
        ciph (j0 h iv)) := by
  rw [fullTag, VG.Proof.Gcm.gctr_block, VG.Proof.Gcm.authBlocks_eq, ghash, VG.Proof.Gcm.ghashFrom_append]; rfl

/-! ## The pre-counter block -/

theorem be64_zero : be64 0 = zeros 8 := by decide

/-- `J₀` for an IV other than 12 bytes: GHASH of the IV padded, then of the
lengths block for no additional data and an IV of `len(IV)` bytes. -/
theorem j0_eq (h : Block) {iv : List Byte} (hiv : iv.length ≠ 12) :
    j0 h iv = ghashFrom h (ghash h (blocks (iv ++ zeros (padLen iv.length))))
      [ofBytes (VG.Proof.Gcm.lensBlock 0 iv.length)] := by
  have hz : zeros (padLen iv.length + 8) = zeros (padLen iv.length) ++ zeros 8 := by
    rw [zeros, zeros, zeros, List.replicate_append_replicate]
  simp only [j0, hiv, ↓reduceIte]
  rw [hz, ← List.append_assoc, List.append_assoc _ (zeros 8),
    VG.Proof.Gcm.blocks_append (by simp only [List.length_append, VG.Proof.Gcm.length_zeros]; exact VG.Proof.Gcm.length_pad_mod _),
    ghash, VG.Proof.Gcm.ghashFrom_append, VG.Proof.Gcm.lensBlock, Nat.mul_zero, VG.Proof.Gcm.be64_zero, VG.Proof.Gcm.blocks_single (bs := zeros 8 ++ be64 (8 * iv.length)) (by simp [VG.Proof.Gcm.length_be64, zeros])]
  rfl

/-- `J₀` for a 12-byte IV. -/
theorem j0_12 (h : Block) {iv : List Byte} (hiv : iv.length = 12) :
    j0 h iv = ofBytes (iv ++ [0, 0, 0, 1]) := by simp only [j0, hiv, ↓reduceIte]

end VG.Proof.Gcm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.Be64`. -/
section

/-!
# GCM: the lengths block from byte-reversed words

Untrusted: everything here is checked by Lean. A 64-bit word stored
little-endian after a byte reversal (`byteRev64`) is the big-endian
`[x]₆₄` of its value (`le8_byteRev64`), which is `be64` modulo 2⁶⁴
(`be64_mod`).
-/

namespace VG.Proof.Gcm

open VG VG.Spec.Gcm

theorem be64_mod (x : Nat) : be64 (x % 2 ^ 64) = be64 x := by
  simp only [be64]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have h : 2 ^ 64 = 256 ^ (7 - i) * 256 ^ (i + 1) := by
    rw [← Nat.pow_add, show 7 - i + (i + 1) = 8 by omega]
  rw [h, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (show 2 ^ 8 ∣ 256 ^ (i + 1) from
    ⟨256 ^ i, by rw [Nat.pow_succ, Nat.mul_comm]⟩)]

theorem byte_extract (w : BitVec 64) (i : Nat) :
    w.extractLsb' (8 * i) 8 = BitVec.ofNat 8 (w.toNat / 256 ^ i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem byteRev64_extract (w : BitVec 64) {i : Nat} (hi : i < 8) :
    (byteRev64 w).extractLsb' (8 * i) 8 = w.extractLsb' (8 * (7 - i)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and]
  rw [getLsbD_byteRev64 _ _ (by omega)]
  congr 1; omega

/-- A byte-reversed word, as its 8 little-endian bytes: `[x]₆₄`. -/
theorem le8_byteRev64 (w : BitVec 64) : Cmac.le8 (byteRev64 w) = be64 w.toNat := by
  simp only [Cmac.le8, be64]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [VG.Proof.Gcm.byteRev64_extract w hi, VG.Proof.Gcm.byte_extract w]

end VG.Proof.Gcm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.Split`. -/
section

/-!
# GCM: counter mode and GHASH of whole blocks, split

Untrusted: everything here is checked by Lean. Counter mode over two runs of
blocks is counter mode over the first, then over the second from the counter
block after the first (`ctr32_append`); the blocks at an address split the
same way (`blocksAt_add`).
-/

namespace VG.Proof.Gcm

open VG VG.Spec.Gcm

theorem keystream_add (ciph : Block → Block) (icb : Block) (a b : Nat) :
    keystream ciph icb (a + b) = keystream ciph icb a ++ keystream ciph (Nat.repeat inc32 a icb) b := by
  simp only [keystream, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, Nat.add_comm a i, VG.Proof.Gcm.repeat_add]

theorem ctr32_append (ciph : Block → Block) (icb : Block) (xs ys : List Block) :
    ctr32 ciph icb (xs ++ ys) = ctr32 ciph icb xs ++ ctr32 ciph (Nat.repeat inc32 xs.length icb) ys := by
  simp only [ctr32, List.length_append, VG.Proof.Gcm.keystream_add]
  exact List.zipWith_append (by simp [keystream])

theorem blocksAt_add (m : Mem) (p : Addr) (a b : Nat) :
    blocksAt m p (a + b) = blocksAt m p a ++ blocksAt m (p + BitVec.ofNat 64 (16 * a)) b := by
  simp only [blocksAt, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, BitVec.add_assoc, Nat.mul_add, BitVec.ofNat_add]

end VG.Proof.Gcm

end
