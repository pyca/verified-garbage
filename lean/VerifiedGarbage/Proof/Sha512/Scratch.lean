import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.Proof.Framework.Offset

/- Proofs formerly in `VerifiedGarbage.Proof.Sha512.Stream`. -/
section

/-!
# Streaming SHA-512: facts about the specification

How `Repr` evolves as bytes are buffered and blocks compressed, and how the
padded message decomposes, independently of any target.
-/

namespace VG.Proof.Sha512.Stream

open VG.Spec.Sha512

/-- Block `i` of the bytes `p`. -/
def blockOf (p : List Byte) (i : Nat) : VG.Spec.Sha512.Block := VG.Spec.Sha512.parseBlock fun k => p.getD (128 * i + k) 0

theorem compressList_succ (H : VG.Spec.Sha512.HashValue) (p : List Byte) (n : Nat) :
    VG.Spec.Sha512.compressList H p (n + 1) = VG.Spec.Sha512.compress (VG.Spec.Sha512.compressList H p n) (VG.Proof.Sha512.Stream.blockOf p n) := by
  simp only [VG.Spec.Sha512.compressList, List.range_succ, List.foldl_append, VG.Proof.Sha512.Stream.blockOf, List.foldl_cons, List.foldl_nil]

theorem compressList_zero (H : VG.Spec.Sha512.HashValue) (p : List Byte) : VG.Spec.Sha512.compressList H p 0 = H := by
  simp only [VG.Spec.Sha512.compressList, List.range_zero, List.foldl_nil]

theorem compressList_congr {H : VG.Spec.Sha512.HashValue} {p q : List Byte} {n : Nat}
    (h : ∀ j < 128 * n, p.getD j 0 = q.getD j 0) : VG.Spec.Sha512.compressList H p n = VG.Spec.Sha512.compressList H q n := by
  induction n with
  | zero => simp only [VG.Proof.Sha512.Stream.compressList_zero]
  | succ n ih =>
    rw [VG.Proof.Sha512.Stream.compressList_succ, VG.Proof.Sha512.Stream.compressList_succ, ih fun j hj => h j (by omega)]
    have : VG.Proof.Sha512.Stream.blockOf p n = VG.Proof.Sha512.Stream.blockOf q n := by
      funext t
      simp only [VG.Proof.Sha512.Stream.blockOf, VG.Spec.Sha512.parseBlock]
      have ht := t.isLt
      rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega),
        h _ (by omega), h _ (by omega), h _ (by omega)]
    rw [this]

theorem compressList_add (H : VG.Spec.Sha512.HashValue) (p : List Byte) (a b : Nat) :
    VG.Spec.Sha512.compressList H p (a + b) = VG.Spec.Sha512.compressList (VG.Spec.Sha512.compressList H p a) (p.drop (128 * a)) b := by
  induction b with
  | zero => simp only [Nat.add_zero, VG.Proof.Sha512.Stream.compressList_zero]
  | succ b ih =>
    rw [← Nat.add_assoc, VG.Proof.Sha512.Stream.compressList_succ, VG.Proof.Sha512.Stream.compressList_succ, ih]
    have : VG.Proof.Sha512.Stream.blockOf p (a + b) = VG.Proof.Sha512.Stream.blockOf (p.drop (128 * a)) b := by
      funext t
      simp only [VG.Proof.Sha512.Stream.blockOf, VG.Spec.Sha512.parseBlock, List.getD_eq_getElem?_getD, List.getElem?_drop]
      simp only [Nat.mul_add, Nat.add_assoc]
    rw [this]

theorem getD_append_left {p q : List Byte} {j : Nat} (h : j < p.length) :
    (p ++ q).getD j 0 = p.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem compressList_append {H : VG.Spec.Sha512.HashValue} {p q : List Byte} {n : Nat} (h : 128 * n ≤ p.length) :
    VG.Spec.Sha512.compressList H (p ++ q) n = VG.Spec.Sha512.compressList H p n :=
  VG.Proof.Sha512.Stream.compressList_congr fun _ hj => VG.Proof.Sha512.Stream.getD_append_left (by omega)

/-! ## Memory -/

theorem stateAt_congr {mem mem' : Mem} {p : Addr} (h : ∀ i < 64, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i)) :
    VG.Spec.Sha512.stateAt mem' p = VG.Spec.Sha512.stateAt mem p := by
  apply Vector.ext
  intro k hk
  simp only [VG.Spec.Sha512.stateAt, Vector.getElem_ofFn]
  apply Mem.readW_congr
  intro i hi
  rw [show p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (8 * k + i) by
    simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]]
  exact h _ (by omega)

theorem bytesAt_congr {mem mem' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i)) :
    VG.Spec.Sha512.bytesAt mem' p n = VG.Spec.Sha512.bytesAt mem p n := by
  simp only [VG.Spec.Sha512.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

/-- `Repr` only depends on the 192 bytes of the state. -/
theorem repr_congr {iv : VG.Spec.Sha512.HashValue} {mem mem' : Mem} {p : Addr} {m : List Byte}
    (h : ∀ i < 192, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (hr : Spec.Sha512.Repr iv mem p m) : Spec.Sha512.Repr iv mem' p m := by
  refine ⟨by rw [VG.Proof.Sha512.Stream.stateAt_congr fun i hi => h i (by omega)]; exact hr.1, ?_⟩
  rw [← hr.2]
  apply VG.Proof.Sha512.Stream.bytesAt_congr
  intro i hi
  have := h (64 + i) (by omega)
  rwa [show p + 64 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (64 + i) by
    simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl]

export VG.WriteBytes (writeBytes writeBytes_nil writeW8_apply writeBytes_snoc writeBytes_before writeBytes_frame write_eq_writeBytes writeBytes_append)

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    VG.Spec.Sha512.bytesAt (VG.WriteBytes.writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) = VG.Spec.Sha512.bytesAt m p r ++ xs := by
  simp only [VG.Spec.Sha512.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    exact VG.WriteBytes.writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Function.comp, VG.WriteBytes.writeBytes]
    have hj : j < xs.length := by simpa using h₁
    rw [show p + BitVec.ofNat 64 (r + j) - (p + BitVec.ofNat 64 r) = BitVec.ofNat 64 j from
      Offset.add_ofNat_add_sub p r j, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hj, List.getD_eq_getElem?_getD]

/-! ## `Repr` -/

theorem repr_nil {iv : VG.Spec.Sha512.HashValue} {mem : Mem} {p : Addr} (h : VG.Spec.Sha512.stateAt mem p = iv) : Spec.Sha512.Repr iv mem p [] := by
  simp [Spec.Sha512.Repr, h, VG.Proof.Sha512.Stream.compressList_zero, VG.Spec.Sha512.bytesAt]

/-- Appending bytes that stay within the buffer. -/
theorem repr_append_buf {iv : VG.Spec.Sha512.HashValue} {mem mem' : Mem} {p : Addr} {m xs : List Byte} (hr : Spec.Sha512.Repr iv mem p m)
    (hlen : m.length % 128 + xs.length < 128) (hs : VG.Spec.Sha512.stateAt mem' p = VG.Spec.Sha512.stateAt mem p)
    (hb : VG.Spec.Sha512.bytesAt mem' (p + 64) (m.length % 128 + xs.length) = m.drop (128 * (m.length / 128)) ++ xs) :
    Spec.Sha512.Repr iv mem' p (m ++ xs) := by
  have hdiv : (m ++ xs).length / 128 = m.length / 128 := by simp only [List.length_append]; omega
  have hmod : (m ++ xs).length % 128 = m.length % 128 + xs.length := by
    simp only [List.length_append]; omega
  refine ⟨?_, ?_⟩
  · rw [hs, hr.1, hdiv, VG.Proof.Sha512.Stream.compressList_append (by omega)]
  · rw [hmod, hb, hdiv, List.drop_append_of_le_length (by omega)]

/-- Appending bytes that complete a block `B` (whose bytes are the buffered
ones followed by `xs`), which is compressed. -/
theorem repr_append_block {iv : VG.Spec.Sha512.HashValue} {mem mem' : Mem} {p : Addr} {m xs : List Byte} (hr : Spec.Sha512.Repr iv mem p m)
    (hlen : m.length % 128 + xs.length = 128)
    (hs : VG.Spec.Sha512.stateAt mem' p =
      VG.Spec.Sha512.compress (VG.Spec.Sha512.stateAt mem p) (VG.Spec.Sha512.parseBlock fun k => (m.drop (128 * (m.length / 128)) ++ xs).getD k 0)) :
    Spec.Sha512.Repr iv mem' p (m ++ xs) := by
  have hdiv : (m ++ xs).length / 128 = m.length / 128 + 1 := by simp only [List.length_append]; omega
  have hmod : (m ++ xs).length % 128 = 0 := by simp only [List.length_append]; omega
  refine ⟨?_, ?_⟩
  · have hb : VG.Proof.Sha512.Stream.blockOf (m ++ xs) (m.length / 128) =
        VG.Spec.Sha512.parseBlock fun k => (m.drop (128 * (m.length / 128)) ++ xs).getD k 0 := by
      rw [← List.drop_append_of_le_length (by omega)]
      simp only [VG.Proof.Sha512.Stream.blockOf, List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [hs, hr.1, hdiv, VG.Proof.Sha512.Stream.compressList_succ, VG.Proof.Sha512.Stream.compressList_append (by omega), hb]
  · rw [hmod]
    simp only [VG.Spec.Sha512.bytesAt, List.range_zero, List.map_nil]
    symm; rw [List.drop_eq_nil_iff]; simp only [List.length_append]; omega

/-! ## Padding -/

/-- The message length in bits, as 16 big-endian bytes. -/
def lenBytes (m : List Byte) : List Byte :=
  (List.range 16).reverse.map fun i => (BitVec.ofNat 128 (8 * m.length)).extractLsb' (8 * i) 8

theorem lenBytes_length (m : List Byte) : (VG.Proof.Sha512.Stream.lenBytes m).length = 16 := by simp [VG.Proof.Sha512.Stream.lenBytes]

/-- For fewer than 2⁶⁴ bytes, the 128-bit length in bits is the 64-bit words
`n >> 61` and `8 n mod 2⁶⁴`, big-endian. -/
theorem lenN_split (n : Nat) (h : n < 2 ^ 64) :
    (List.range 16).reverse.map (fun i => (BitVec.ofNat 128 (8 * n)).extractLsb' (8 * i) 8) =
      VG.Spec.Sha512.wordBytes (BitVec.ofNat 64 n >>> 61) ++ VG.Spec.Sha512.wordBytes (BitVec.ofNat 64 (8 * n)) := by
  have key : BitVec.ofNat 128 (8 * n) = (BitVec.ofNat 64 n >>> 61) ++ BitVec.ofNat 64 (8 * n) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _), Nat.shiftLeft_eq]
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  rw [key]
  generalize BitVec.ofNat 64 n >>> 61 = x
  generalize BitVec.ofNat 64 (8 * n) = y
  simp only [VG.Spec.Sha512.wordBytes, List.range_succ, List.range_zero, List.nil_append,
    List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  simp (disch := decide) only [BitVec.extractLsb'_append_eq_of_add_le,
    BitVec.extractLsb'_append_eq_of_le]

/-- For a message of fewer than 2⁶⁴ bytes, the 128-bit length in bits is the
64-bit words `|m| >> 61` and `8 |m| mod 2⁶⁴`, big-endian. -/
theorem lenBytes_split (m : List Byte) (h : m.length < 2 ^ 64) :
    VG.Proof.Sha512.Stream.lenBytes m = VG.Spec.Sha512.wordBytes (BitVec.ofNat 64 m.length >>> 61) ++ VG.Spec.Sha512.wordBytes (BitVec.ofNat 64 (8 * m.length)) :=
  VG.Proof.Sha512.Stream.lenN_split m.length h

/-- The bytes after the whole blocks of `m`. -/
abbrev rest (m : List Byte) : List Byte := m.drop (128 * (m.length / 128))

theorem rest_length (m : List Byte) : (VG.Proof.Sha512.Stream.rest m).length = m.length % 128 := by
  simp only [VG.Proof.Sha512.Stream.rest, List.length_drop]; omega

theorem compressList_one (H : VG.Spec.Sha512.HashValue) (p : List Byte) :
    VG.Spec.Sha512.compressList H p 1 = VG.Spec.Sha512.compress H (VG.Spec.Sha512.parseBlock fun t => p.getD t 0) := by
  rw [VG.Proof.Sha512.Stream.compressList_succ, VG.Proof.Sha512.Stream.compressList_zero]; simp [VG.Proof.Sha512.Stream.blockOf]

theorem hash_eq (iv : VG.Spec.Sha512.HashValue) (m : List Byte) (nt : Nat)
    (hn : (m.length % 128 + 1 + (239 - m.length % 128) % 128 + 16) = 128 * nt) :
    Spec.Sha512.finalHash iv m = (VG.Spec.Sha512.compressList (VG.Spec.Sha512.compressList iv m (m.length / 128))
      (VG.Proof.Sha512.Stream.rest m ++ [0x80] ++ List.replicate ((239 - m.length % 128) % 128) 0 ++ VG.Proof.Sha512.Stream.lenBytes m) nt).toList.flatMap
        VG.Spec.Sha512.wordBytes := by
  have hp : VG.Spec.Sha512.pad m = m ++ ([0x80] ++ List.replicate ((239 - m.length % 128) % 128) 0 ++ VG.Proof.Sha512.Stream.lenBytes m) := by
    simp [VG.Spec.Sha512.pad, VG.Proof.Sha512.Stream.lenBytes, List.append_assoc]
  have hlen : (VG.Spec.Sha512.pad m).length / 128 = m.length / 128 + nt := by
    rw [hp]; simp only [List.length_append, List.length_replicate, VG.Proof.Sha512.Stream.lenBytes_length, List.length_singleton]
    omega
  simp only [Spec.Sha512.finalHash]
  rw [hlen, VG.Proof.Sha512.Stream.compressList_add, hp, VG.Proof.Sha512.Stream.compressList_append (by omega),
    List.drop_append_of_le_length (by omega)]
  simp only [List.append_assoc]

theorem parseBlock_congr {f g : Nat → Byte} (h : ∀ k < 128, f k = g k) : VG.Spec.Sha512.parseBlock f = VG.Spec.Sha512.parseBlock g := by
  funext j
  have := j.isLt
  simp only [VG.Spec.Sha512.parseBlock]
  rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega),
    h _ (by omega), h _ (by omega), h _ (by omega)]

/-- A message whose padding takes one more block. -/
theorem hash_one {iv : VG.Spec.Sha512.HashValue} {m : List Byte} (hr : m.length % 128 < 112) :
    Spec.Sha512.finalHash iv m = (VG.Spec.Sha512.compress (VG.Spec.Sha512.compressList iv m (m.length / 128))
      (VG.Spec.Sha512.parseBlock fun t => (VG.Proof.Sha512.Stream.rest m ++ [0x80] ++ List.replicate (111 - m.length % 128) 0 ++
        VG.Proof.Sha512.Stream.lenBytes m).getD t 0)).toList.flatMap VG.Spec.Sha512.wordBytes := by
  rw [VG.Proof.Sha512.Stream.hash_eq iv m 1 (by omega), VG.Proof.Sha512.Stream.compressList_one,
    show (239 - m.length % 128) % 128 = 111 - m.length % 128 by omega]

theorem getD_append_right {p q : List Byte} {j : Nat} :
    (p ++ q).getD (p.length + j) 0 = q.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-- A message whose padding takes two more blocks. -/
theorem hash_two {iv : VG.Spec.Sha512.HashValue} {m : List Byte} (hr : 112 ≤ m.length % 128) :
    Spec.Sha512.finalHash iv m = (VG.Spec.Sha512.compress (VG.Spec.Sha512.compress (VG.Spec.Sha512.compressList iv m (m.length / 128))
      (VG.Spec.Sha512.parseBlock fun t => (VG.Proof.Sha512.Stream.rest m ++ [0x80] ++ List.replicate (127 - m.length % 128) 0).getD t 0))
      (VG.Spec.Sha512.parseBlock fun t => (List.replicate 112 0 ++ VG.Proof.Sha512.Stream.lenBytes m).getD t 0)).toList.flatMap VG.Spec.Sha512.wordBytes := by
  rw [VG.Proof.Sha512.Stream.hash_eq iv m 2 (by omega), VG.Proof.Sha512.Stream.compressList_succ, VG.Proof.Sha512.Stream.compressList_one]
  have e : VG.Proof.Sha512.Stream.rest m ++ [0x80] ++ List.replicate ((239 - m.length % 128) % 128) 0 ++ VG.Proof.Sha512.Stream.lenBytes m =
      (VG.Proof.Sha512.Stream.rest m ++ [0x80] ++ List.replicate (127 - m.length % 128) 0) ++
        (List.replicate 112 0 ++ VG.Proof.Sha512.Stream.lenBytes m) := by
    rw [show (239 - m.length % 128) % 128 = (127 - m.length % 128) + 112 by omega, ← List.replicate_append_replicate]
    simp only [List.append_assoc]
  have hl : (VG.Proof.Sha512.Stream.rest m ++ [0x80] ++ List.replicate (127 - m.length % 128) 0).length = 128 := by
    simp only [List.length_append, VG.Proof.Sha512.Stream.rest_length, List.length_replicate, List.length_singleton]; omega
  rw [e]
  have h1 : (VG.Spec.Sha512.parseBlock fun t => ((VG.Proof.Sha512.Stream.rest m ++ [0x80] ++ List.replicate (127 - m.length % 128) 0) ++
      (List.replicate 112 0 ++ VG.Proof.Sha512.Stream.lenBytes m)).getD t 0) =
      VG.Spec.Sha512.parseBlock fun t => (VG.Proof.Sha512.Stream.rest m ++ [0x80] ++ List.replicate (127 - m.length % 128) 0).getD t 0 :=
    VG.Proof.Sha512.Stream.parseBlock_congr fun k hk => VG.Proof.Sha512.Stream.getD_append_left (by omega)
  have h2 : VG.Proof.Sha512.Stream.blockOf ((VG.Proof.Sha512.Stream.rest m ++ [0x80] ++ List.replicate (127 - m.length % 128) 0) ++
      (List.replicate 112 0 ++ VG.Proof.Sha512.Stream.lenBytes m)) 1 =
      VG.Spec.Sha512.parseBlock fun t => (List.replicate 112 0 ++ VG.Proof.Sha512.Stream.lenBytes m).getD t 0 :=
    VG.Proof.Sha512.Stream.parseBlock_congr fun k _ => by
      have := VG.Proof.Sha512.Stream.getD_append_right (p := VG.Proof.Sha512.Stream.rest m ++ [0x80] ++ List.replicate (127 - m.length % 128) 0)
        (q := List.replicate 112 0 ++ VG.Proof.Sha512.Stream.lenBytes m) (j := k)
      rw [hl] at this
      exact this
  rw [h1, h2]

end VG.Proof.Sha512.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha512.Md`. -/
section

/-!
# The SHA-512 family as a streaming Merkle–Damgård hash function

SHA-512 (for any initial hash value, so SHA-384, SHA-512/224 and SHA-512/256
too) as an instance of `Proof.MdStream.Md`, for the generic streaming proofs:
its `Repr` and `finalHash` are the generic ones, by unfolding.
-/

namespace VG.Proof.Sha512

open Spec.Sha512

/-- The big-endian bytes of a 128-bit word (§5.1.2). -/
def lenField (x : BitVec 128) : List Byte := (List.range 16).reverse.map fun i => x.extractLsb' (8 * i) 8

/-- The SHA-512 family: 128-byte blocks, a 64-byte hash value, the
big-endian 128-bit bit count as its length field (for messages shorter than
2⁶⁴ bytes, which the count modulo 2⁶⁴ determines), and all the words of the
hash value big-endian as its output (which the truncated variants
truncate). -/
def md : MdStream.Md 128 64 16 where
  HV := HashValue
  Blk := Block
  stateAt := stateAt
  parse := parseBlock
  compress := compress
  lenBytes n := VG.Proof.Sha512.lenField (BitVec.ofNat 128 (8 * n))
  lenOf x := VG.Proof.Sha512.lenField (BitVec.ofNat 128 (8 * x.toNat))
  lenOk n := n < 2 ^ 64
  digest h := h.toList.flatMap wordBytes
  stateAt_congr := Stream.stateAt_congr
  parse_congr := Stream.parseBlock_congr
  lenBytes_length _ := by simp [VG.Proof.Sha512.lenField]
  lenOf_eq n h := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  lenOf_length _ := by simp [VG.Proof.Sha512.lenField]
  digest_length h := by simp [List.length_flatMap, wordBytes, List.map_const']

/-- The 128-bit length in bits of a 64-bit count of bytes is the 64-bit
words `count >> 61` and `8 count mod 2⁶⁴`, big-endian. -/
theorem lenOf_split (x : BitVec 64) :
    md.lenOf x = wordBytes (x >>> 61) ++ wordBytes (BitVec.ofNat 64 (8 * x.toNat)) := by
  have e := Stream.lenN_split x.toNat x.isLt
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at e
  exact e

theorem repr_iff {iv : HashValue} {mem : Mem} {p : Addr} {m : List Byte} :
    Repr iv mem p m ↔ md.Repr iv mem p m := Iff.rfl

theorem finalHash_eq (iv : HashValue) (m : List Byte) : finalHash iv m = md.hash iv m := rfl

end VG.Proof.Sha512

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha512.Scratch`. -/
section

/-!
# SHA-512's streaming postconditions read memory only within the buffers

`update` and `finalize` keep their working space in a frame of their own
(`Verified.stackScratch`); on x86 and ARMv7, where the frame also holds a
copy of the arguments passed on the stack, that needs their postconditions to
read the memory on entry only within the function's buffers: the streaming
state (`Stream.repr_congr`) and the data (`Stream.bytesAt_congr`).
-/

namespace VG.Proof.Sha512

open VG.Spec.Sha512

theorem updatePost_local (pb : Nat) : ∀ vs m₁ m₂ m' r, vs.length = (updateSig.words pb).length →
    (∀ b ∈ Sig.bufs updateSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateSig.words pb) (VG.Spec.Sha512.updatePost pb) vs m₁ m' r →
      Curry.apply (updateSig.words pb) (VG.Spec.Sha512.updatePost pb) vs m₂ m' r
  | [st, ct, dt, ln], m₁, m₂, m', r, _, hb, h => by
    simp only [VG.Spec.Sha512.updateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 192, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    have hd : ∀ i < (ln.setWidth pb).toNat, m₂ (dt + BitVec.ofNat 64 i) = m₁ (dt + BitVec.ofNat 64 i) :=
      fun i hi => by
        have := Nat.mod_le ln.toNat (2 ^ pb)
        have := ln.isLt
        rw [BitVec.toNat_setWidth] at hi
        exact (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    intro iv msg hr hc
    rw [show VG.Spec.Sha512.bytesAt m₂ (ArgWord.addr.ofRaw dt) ((ArgWord.int pb).ofRaw ln).toNat =
      VG.Spec.Sha512.bytesAt m₁ dt (ln.setWidth pb).toNat from Stream.bytesAt_congr hd]
    exact h iv msg (Stream.repr_congr (fun i hi => (hs i hi).symm) hr) hc

theorem finalizePost_local (pb : Nat) :
    ∀ vs m₁ m₂ m' r, vs.length = (finalizeSig.words pb).length →
      (∀ b ∈ Sig.bufs finalizeSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (finalizeSig.words pb) (VG.Spec.Sha512.finalizePost pb) vs m₁ m' r →
        Curry.apply (finalizeSig.words pb) (VG.Spec.Sha512.finalizePost pb) vs m₂ m' r
  | [st, ct, ot], m₁, m₂, m', r, _, hb, h => by
    simp only [VG.Spec.Sha512.finalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 192, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    intro iv msg hr hl hc
    exact h iv msg (Stream.repr_congr (fun i hi => (hs i hi).symm) hr) hl hc

end VG.Proof.Sha512

end
