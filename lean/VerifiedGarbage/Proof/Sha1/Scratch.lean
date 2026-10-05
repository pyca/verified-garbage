import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.Proof.Framework.Mem
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Spec.Sha1.Contract
import VerifiedGarbage.Proof.Framework.Offset

/- Proofs formerly in `VerifiedGarbage.Proof.Sha1.Stream`. -/
section

/-!
# Streaming SHA-1: facts about the specification

How `Repr` evolves as bytes are buffered and blocks compressed, and how the
padded message decomposes, independently of any target.
-/

namespace VG.Proof.Sha1.Stream

open VG.Spec.Sha1

/-- Block `i` of the bytes `p`. -/
def blockOf (p : List Byte) (i : Nat) : VG.Spec.Sha1.Block := VG.Spec.Sha1.parseBlock fun k => p.getD (64 * i + k) 0

theorem compressList_succ (H : VG.Spec.Sha1.HashValue) (p : List Byte) (n : Nat) :
    VG.Spec.Sha1.compressList H p (n + 1) = VG.Spec.Sha1.compress (VG.Spec.Sha1.compressList H p n) (VG.Proof.Sha1.Stream.blockOf p n) := by
  simp only [VG.Spec.Sha1.compressList, List.range_succ, List.foldl_append, VG.Proof.Sha1.Stream.blockOf, List.foldl_cons, List.foldl_nil]

theorem compressList_zero (H : VG.Spec.Sha1.HashValue) (p : List Byte) : VG.Spec.Sha1.compressList H p 0 = H := by
  simp only [VG.Spec.Sha1.compressList, List.range_zero, List.foldl_nil]

theorem compressList_congr {H : VG.Spec.Sha1.HashValue} {p q : List Byte} {n : Nat}
    (h : ∀ j < 64 * n, p.getD j 0 = q.getD j 0) : VG.Spec.Sha1.compressList H p n = VG.Spec.Sha1.compressList H q n := by
  induction n with
  | zero => simp only [VG.Proof.Sha1.Stream.compressList_zero]
  | succ n ih =>
    rw [VG.Proof.Sha1.Stream.compressList_succ, VG.Proof.Sha1.Stream.compressList_succ, ih fun j hj => h j (by omega)]
    have : VG.Proof.Sha1.Stream.blockOf p n = VG.Proof.Sha1.Stream.blockOf q n := by
      funext t
      simp only [VG.Proof.Sha1.Stream.blockOf, VG.Spec.Sha1.parseBlock]
      have ht := t.isLt
      rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]
    rw [this]

theorem compressList_add (H : VG.Spec.Sha1.HashValue) (p : List Byte) (a b : Nat) :
    VG.Spec.Sha1.compressList H p (a + b) = VG.Spec.Sha1.compressList (VG.Spec.Sha1.compressList H p a) (p.drop (64 * a)) b := by
  induction b with
  | zero => simp only [Nat.add_zero, VG.Proof.Sha1.Stream.compressList_zero]
  | succ b ih =>
    rw [← Nat.add_assoc, VG.Proof.Sha1.Stream.compressList_succ, VG.Proof.Sha1.Stream.compressList_succ, ih]
    have : VG.Proof.Sha1.Stream.blockOf p (a + b) = VG.Proof.Sha1.Stream.blockOf (p.drop (64 * a)) b := by
      funext t
      simp only [VG.Proof.Sha1.Stream.blockOf, VG.Spec.Sha1.parseBlock, List.getD_eq_getElem?_getD, List.getElem?_drop]
      simp only [Nat.mul_add, Nat.add_assoc]
    rw [this]

theorem getD_append_left {p q : List Byte} {j : Nat} (h : j < p.length) :
    (p ++ q).getD j 0 = p.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem compressList_append {H : VG.Spec.Sha1.HashValue} {p q : List Byte} {n : Nat} (h : 64 * n ≤ p.length) :
    VG.Spec.Sha1.compressList H (p ++ q) n = VG.Spec.Sha1.compressList H p n :=
  VG.Proof.Sha1.Stream.compressList_congr fun _ hj => VG.Proof.Sha1.Stream.getD_append_left (by omega)

/-! ## Memory -/

theorem stateAt_congr {mem mem' : Mem} {p : Addr} (h : ∀ i < 20, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i)) :
    VG.Spec.Sha1.stateAt mem' p = VG.Spec.Sha1.stateAt mem p := by
  apply Vector.ext
  intro k hk
  simp only [VG.Spec.Sha1.stateAt, Vector.getElem_ofFn]
  apply Mem.readW_congr
  intro i hi
  rw [show p + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (4 * k + i) by
    simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]]
  exact h _ (by omega)

theorem bytesAt_congr {mem mem' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i)) :
    VG.Spec.Sha1.bytesAt mem' p n = VG.Spec.Sha1.bytesAt mem p n := by
  simp only [VG.Spec.Sha1.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

/-- `Repr` only depends on the 84 bytes of the state. -/
theorem repr_congr {mem mem' : Mem} {p : Addr} {m : List Byte}
    (h : ∀ i < 84, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (hr : Spec.Sha1.Repr mem p m) : Spec.Sha1.Repr mem' p m := by
  refine ⟨by rw [VG.Proof.Sha1.Stream.stateAt_congr fun i hi => h i (by omega)]; exact hr.1, ?_⟩
  rw [← hr.2]
  apply VG.Proof.Sha1.Stream.bytesAt_congr
  intro i hi
  have := h (20 + i) (by omega)
  rwa [show p + 20 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (20 + i) by
    simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl]

export VG.WriteBytes (writeBytes writeBytes_nil writeW8_apply writeBytes_snoc writeBytes_before writeBytes_frame write_eq_writeBytes writeBytes_append)

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    VG.Spec.Sha1.bytesAt (VG.WriteBytes.writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) = VG.Spec.Sha1.bytesAt m p r ++ xs := by
  simp only [VG.Spec.Sha1.bytesAt, List.range_add, List.map_append, List.map_map]
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

theorem repr_nil {mem : Mem} {p : Addr} (h : VG.Spec.Sha1.stateAt mem p = VG.Spec.Sha1.H0) : Spec.Sha1.Repr mem p [] := by
  simp [Spec.Sha1.Repr, h, VG.Proof.Sha1.Stream.compressList_zero, VG.Spec.Sha1.bytesAt]

/-- Appending bytes that stay within the buffer. -/
theorem repr_append_buf {mem mem' : Mem} {p : Addr} {m xs : List Byte} (hr : Spec.Sha1.Repr mem p m)
    (hlen : m.length % 64 + xs.length < 64) (hs : VG.Spec.Sha1.stateAt mem' p = VG.Spec.Sha1.stateAt mem p)
    (hb : VG.Spec.Sha1.bytesAt mem' (p + 20) (m.length % 64 + xs.length) = m.drop (64 * (m.length / 64)) ++ xs) :
    Spec.Sha1.Repr mem' p (m ++ xs) := by
  have hdiv : (m ++ xs).length / 64 = m.length / 64 := by simp only [List.length_append]; omega
  have hmod : (m ++ xs).length % 64 = m.length % 64 + xs.length := by
    simp only [List.length_append]; omega
  refine ⟨?_, ?_⟩
  · rw [hs, hr.1, hdiv, VG.Proof.Sha1.Stream.compressList_append (by omega)]
  · rw [hmod, hb, hdiv, List.drop_append_of_le_length (by omega)]

/-- Appending bytes that complete a block `B` (whose bytes are the buffered
ones followed by `xs`), which is compressed. -/
theorem repr_append_block {mem mem' : Mem} {p : Addr} {m xs : List Byte} (hr : Spec.Sha1.Repr mem p m)
    (hlen : m.length % 64 + xs.length = 64)
    (hs : VG.Spec.Sha1.stateAt mem' p =
      VG.Spec.Sha1.compress (VG.Spec.Sha1.stateAt mem p) (VG.Spec.Sha1.parseBlock fun k => (m.drop (64 * (m.length / 64)) ++ xs).getD k 0)) :
    Spec.Sha1.Repr mem' p (m ++ xs) := by
  have hdiv : (m ++ xs).length / 64 = m.length / 64 + 1 := by simp only [List.length_append]; omega
  have hmod : (m ++ xs).length % 64 = 0 := by simp only [List.length_append]; omega
  refine ⟨?_, ?_⟩
  · have hb : VG.Proof.Sha1.Stream.blockOf (m ++ xs) (m.length / 64) =
        VG.Spec.Sha1.parseBlock fun k => (m.drop (64 * (m.length / 64)) ++ xs).getD k 0 := by
      rw [← List.drop_append_of_le_length (by omega)]
      simp only [VG.Proof.Sha1.Stream.blockOf, List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [hs, hr.1, hdiv, VG.Proof.Sha1.Stream.compressList_succ, VG.Proof.Sha1.Stream.compressList_append (by omega), hb]
  · rw [hmod]
    simp only [VG.Spec.Sha1.bytesAt, List.range_zero, List.map_nil]
    symm; rw [List.drop_eq_nil_iff]; simp only [List.length_append]; omega

/-! ## Padding -/

/-- The message length in bits, as 8 big-endian bytes. -/
def lenBytes (m : List Byte) : List Byte :=
  (List.range 8).reverse.map fun i => (BitVec.ofNat 64 (8 * m.length)).extractLsb' (8 * i) 8

theorem lenBytes_length (m : List Byte) : (VG.Proof.Sha1.Stream.lenBytes m).length = 8 := by simp [VG.Proof.Sha1.Stream.lenBytes]

theorem shl3 (hi lo : BitVec 32) : (hi <<< 3 ||| lo >>> 29) ++ lo <<< 3 = (hi ++ lo) <<< 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  conv_rhs => rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append]
  rw [BitVec.getLsbD_append]
  by_cases h1 : i < 32
  · simp only [h1, ↓reduceIte]; rw [BitVec.getLsbD_shiftLeft]
    by_cases h3 : i < 3
    · simp [h3]
    · simp only [show i - 3 < 32 by omega, ↓reduceIte]; simp [h1, h3, hi']
  · simp only [h1, ↓reduceIte]; rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    by_cases h35 : i < 35
    · simp only [show i - 3 < 32 by omega, ↓reduceIte]; rw [show 29 + (i - 32) = i - 3 by omega]
      simp [show i - 32 < 3 by omega, show ¬ i < 3 by omega, hi']
    · simp only [show ¬ i - 3 < 32 by omega, ↓reduceIte]; rw [show i - 3 - 32 = i - 32 - 3 by omega]
      have : lo.getLsbD (29 + (i - 32)) = false := BitVec.getLsbD_of_ge _ _ (by omega)
      simp [this, show ¬ i - 32 < 3 by omega, show ¬ i < 3 by omega, show i - 32 < 32 by omega, hi']

theorem bits8 (x : BitVec 64) : BitVec.ofNat 64 (8 * x.toNat) = x <<< 3 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- The message length in bits, big-endian, from the two halves of the byte count. -/
theorem lenBytes_halves (hi lo : BitVec 32) (m : List Byte) (h : hi ++ lo = BitVec.ofNat 64 m.length) :
    VG.Proof.Sha1.Stream.lenBytes m = Spec.Sha1.wordBytes (hi <<< 3 ||| lo >>> 29) ++ Spec.Sha1.wordBytes (lo <<< 3) := by
  have hx : BitVec.ofNat 64 (8 * m.length) = (hi <<< 3 ||| lo >>> 29) ++ lo <<< 3 := by
    rw [VG.Proof.Sha1.Stream.shl3, h, ← VG.Proof.Sha1.Stream.bits8]
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mul_mod]
  simp only [VG.Proof.Sha1.Stream.lenBytes, hx, Spec.Sha1.wordBytes]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.reverse_cons,
    List.reverse_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_,
    List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩⟩⟩⟩⟩⟩ <;>
  · ext i hi
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
    split <;> first | omega | (congr 1; omega) | rfl

/-- The bytes after the whole blocks of `m`. -/
abbrev rest (m : List Byte) : List Byte := m.drop (64 * (m.length / 64))

theorem rest_length (m : List Byte) : (VG.Proof.Sha1.Stream.rest m).length = m.length % 64 := by
  simp only [VG.Proof.Sha1.Stream.rest, List.length_drop]; omega

theorem compressList_one (H : VG.Spec.Sha1.HashValue) (p : List Byte) :
    VG.Spec.Sha1.compressList H p 1 = VG.Spec.Sha1.compress H (VG.Spec.Sha1.parseBlock fun t => p.getD t 0) := by
  rw [VG.Proof.Sha1.Stream.compressList_succ, VG.Proof.Sha1.Stream.compressList_zero]; simp [VG.Proof.Sha1.Stream.blockOf]

theorem hash_eq (m : List Byte) (nt : Nat)
    (hn : (m.length % 64 + 1 + (119 - m.length % 64) % 64 + 8) = 64 * nt) :
    Spec.Sha1.hash m = (VG.Spec.Sha1.compressList (VG.Spec.Sha1.compressList VG.Spec.Sha1.H0 m (m.length / 64))
      (VG.Proof.Sha1.Stream.rest m ++ [0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++ VG.Proof.Sha1.Stream.lenBytes m) nt).toList.flatMap
        VG.Spec.Sha1.wordBytes := by
  have hp : VG.Spec.Sha1.pad m = m ++ ([0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++ VG.Proof.Sha1.Stream.lenBytes m) := by
    simp [VG.Spec.Sha1.pad, VG.Proof.Sha1.Stream.lenBytes, List.append_assoc]
  have hlen : (VG.Spec.Sha1.pad m).length / 64 = m.length / 64 + nt := by
    rw [hp]; simp only [List.length_append, List.length_replicate, VG.Proof.Sha1.Stream.lenBytes_length, List.length_singleton]
    omega
  simp only [Spec.Sha1.hash]
  rw [hlen, VG.Proof.Sha1.Stream.compressList_add, hp, VG.Proof.Sha1.Stream.compressList_append (by omega),
    List.drop_append_of_le_length (by omega)]
  simp only [List.append_assoc]

theorem parseBlock_congr {f g : Nat → Byte} (h : ∀ k < 64, f k = g k) : VG.Spec.Sha1.parseBlock f = VG.Spec.Sha1.parseBlock g := by
  funext j
  have := j.isLt
  simp only [VG.Spec.Sha1.parseBlock]
  rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]

/-- A message whose padding takes one more block. -/
theorem hash_one {m : List Byte} (hr : m.length % 64 < 56) :
    Spec.Sha1.hash m = (VG.Spec.Sha1.compress (VG.Spec.Sha1.compressList VG.Spec.Sha1.H0 m (m.length / 64))
      (VG.Spec.Sha1.parseBlock fun t => (VG.Proof.Sha1.Stream.rest m ++ [0x80] ++ List.replicate (55 - m.length % 64) 0 ++
        VG.Proof.Sha1.Stream.lenBytes m).getD t 0)).toList.flatMap VG.Spec.Sha1.wordBytes := by
  rw [VG.Proof.Sha1.Stream.hash_eq m 1 (by omega), VG.Proof.Sha1.Stream.compressList_one,
    show (119 - m.length % 64) % 64 = 55 - m.length % 64 by omega]

theorem getD_append_right {p q : List Byte} {j : Nat} :
    (p ++ q).getD (p.length + j) 0 = q.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-- A message whose padding takes two more blocks. -/
theorem hash_two {m : List Byte} (hr : 56 ≤ m.length % 64) :
    Spec.Sha1.hash m = (VG.Spec.Sha1.compress (VG.Spec.Sha1.compress (VG.Spec.Sha1.compressList VG.Spec.Sha1.H0 m (m.length / 64))
      (VG.Spec.Sha1.parseBlock fun t => (VG.Proof.Sha1.Stream.rest m ++ [0x80] ++ List.replicate (63 - m.length % 64) 0).getD t 0))
      (VG.Spec.Sha1.parseBlock fun t => (List.replicate 56 0 ++ VG.Proof.Sha1.Stream.lenBytes m).getD t 0)).toList.flatMap VG.Spec.Sha1.wordBytes := by
  rw [VG.Proof.Sha1.Stream.hash_eq m 2 (by omega), VG.Proof.Sha1.Stream.compressList_succ, VG.Proof.Sha1.Stream.compressList_one]
  have e : VG.Proof.Sha1.Stream.rest m ++ [0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++ VG.Proof.Sha1.Stream.lenBytes m =
      (VG.Proof.Sha1.Stream.rest m ++ [0x80] ++ List.replicate (63 - m.length % 64) 0) ++
        (List.replicate 56 0 ++ VG.Proof.Sha1.Stream.lenBytes m) := by
    rw [show (119 - m.length % 64) % 64 = (63 - m.length % 64) + 56 by omega, ← List.replicate_append_replicate]
    simp only [List.append_assoc]
  have hl : (VG.Proof.Sha1.Stream.rest m ++ [0x80] ++ List.replicate (63 - m.length % 64) 0).length = 64 := by
    simp only [List.length_append, VG.Proof.Sha1.Stream.rest_length, List.length_replicate, List.length_singleton]; omega
  rw [e]
  have h1 : (VG.Spec.Sha1.parseBlock fun t => ((VG.Proof.Sha1.Stream.rest m ++ [0x80] ++ List.replicate (63 - m.length % 64) 0) ++
      (List.replicate 56 0 ++ VG.Proof.Sha1.Stream.lenBytes m)).getD t 0) =
      VG.Spec.Sha1.parseBlock fun t => (VG.Proof.Sha1.Stream.rest m ++ [0x80] ++ List.replicate (63 - m.length % 64) 0).getD t 0 :=
    VG.Proof.Sha1.Stream.parseBlock_congr fun k hk => VG.Proof.Sha1.Stream.getD_append_left (by omega)
  have h2 : VG.Proof.Sha1.Stream.blockOf ((VG.Proof.Sha1.Stream.rest m ++ [0x80] ++ List.replicate (63 - m.length % 64) 0) ++
      (List.replicate 56 0 ++ VG.Proof.Sha1.Stream.lenBytes m)) 1 =
      VG.Spec.Sha1.parseBlock fun t => (List.replicate 56 0 ++ VG.Proof.Sha1.Stream.lenBytes m).getD t 0 :=
    VG.Proof.Sha1.Stream.parseBlock_congr fun k _ => by
      have := VG.Proof.Sha1.Stream.getD_append_right (p := VG.Proof.Sha1.Stream.rest m ++ [0x80] ++ List.replicate (63 - m.length % 64) 0)
        (q := List.replicate 56 0 ++ VG.Proof.Sha1.Stream.lenBytes m) (j := k)
      rw [hl] at this
      exact this
  rw [h1, h2]

end VG.Proof.Sha1.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha1.Md`. -/
section

/-!
# SHA-1 as a streaming Merkle–Damgård hash function

SHA-1 as an instance of `Proof.MdStream.Md`, for the generic streaming proofs:
its `Repr` and `hash` are the generic ones for `H0`, by unfolding.
-/

namespace VG.Proof.Sha1

open Spec.Sha1

/-- The big-endian bytes of a 64-bit word (§5.1.1). -/
def lenField (x : BitVec 64) : List Byte := (List.range 8).reverse.map fun i => x.extractLsb' (8 * i) 8

/-- SHA-1: 64-byte blocks, a 20-byte hash value, the big-endian 64-bit
bit count as its length field (for messages shorter than 2⁶⁴ bits, which is
the count modulo 2⁶⁴), and the words of the hash value big-endian as its
digest. -/
def md : MdStream.Md 64 20 8 where
  HV := HashValue
  Blk := Block
  stateAt := stateAt
  parse := parseBlock
  compress := compress
  lenBytes n := VG.Proof.Sha1.lenField (BitVec.ofNat 64 (8 * n))
  lenOf x := VG.Proof.Sha1.lenField (BitVec.ofNat 64 (8 * x.toNat))
  lenOk _ := True
  digest h := h.toList.flatMap wordBytes
  stateAt_congr := Stream.stateAt_congr
  parse_congr := Stream.parseBlock_congr
  lenBytes_length _ := by simp [VG.Proof.Sha1.lenField]
  lenOf_eq n _ := by
    refine congrArg VG.Proof.Sha1.lenField (BitVec.eq_of_toNat_eq ?_)
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  lenOf_length _ := by simp [VG.Proof.Sha1.lenField]
  digest_length h := by simp [List.length_flatMap, wordBytes, List.map_const']

theorem repr_iff {mem : Mem} {p : Addr} {m : List Byte} : Repr mem p m ↔ md.Repr H0 mem p m := Iff.rfl

theorem hash_eq (m : List Byte) : Spec.Sha1.hash m = md.hash H0 m := rfl

/-- The digest, as 32-bit words. -/
theorem digest_eq (mem : Mem) (p : Addr) :
    md.digest (md.stateAt mem p) = (List.range 5).flatMap fun k =>
      MdStream.bytes32 true (mem.readW (p + BitVec.ofNat 64 (4 * k)) 32) := by
  simp [VG.Proof.Sha1.md, stateAt, Vector.toList_ofFn, List.range_succ, List.ofFn_succ, MdStream.bytes32, wordBytes]

end VG.Proof.Sha1

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha1.Scratch`. -/
section

/-!
# SHA-1's streaming postconditions read memory only within the buffers

`update` and `finalize` keep their working space in a frame of their own
(`Verified.stackScratch`); on x86 and ARMv7, where the frame also holds a
copy of the arguments passed on the stack, that needs their postconditions to
read the memory on entry only within the function's buffers: the streaming
state (`Stream.repr_congr`) and the data (`Stream.bytesAt_congr`).
-/

namespace VG.Proof.Sha1

open VG.Spec.Sha1

theorem updatePost_local (pb : Nat) : ∀ vs m₁ m₂ m' r, vs.length = (updateSig.words pb).length →
    (∀ b ∈ Sig.bufs updateSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateSig.words pb) (VG.Spec.Sha1.updatePost pb) vs m₁ m' r →
      Curry.apply (updateSig.words pb) (VG.Spec.Sha1.updatePost pb) vs m₂ m' r
  | [st, ct, dt, ln], m₁, m₂, m', r, _, hb, h => by
    simp only [VG.Spec.Sha1.updateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 84, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    have hd : ∀ i < (ln.setWidth pb).toNat, m₂ (dt + BitVec.ofNat 64 i) = m₁ (dt + BitVec.ofNat 64 i) :=
      fun i hi => by
        have := Nat.mod_le ln.toNat (2 ^ pb)
        have := ln.isLt
        rw [BitVec.toNat_setWidth] at hi
        exact (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    intro msg hr hc
    rw [show VG.Spec.Sha1.bytesAt m₂ (ArgWord.addr.ofRaw dt) ((ArgWord.int pb).ofRaw ln).toNat =
      VG.Spec.Sha1.bytesAt m₁ dt (ln.setWidth pb).toNat from Stream.bytesAt_congr hd]
    exact h msg (Stream.repr_congr (fun i hi => (hs i hi).symm) hr) hc

theorem finalizePost_local (pb : Nat) :
    ∀ vs m₁ m₂ m' r, vs.length = (finalizeSig.words pb).length →
      (∀ b ∈ Sig.bufs finalizeSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (finalizeSig.words pb) (VG.Spec.Sha1.finalizePost pb) vs m₁ m' r →
        Curry.apply (finalizeSig.words pb) (VG.Spec.Sha1.finalizePost pb) vs m₂ m' r
  | [st, ct, ot], m₁, m₂, m', r, _, hb, h => by
    simp only [VG.Spec.Sha1.finalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 84, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    intro msg hr hc
    exact h msg (Stream.repr_congr (fun i hi => (hs i hi).symm) hr) hc

end VG.Proof.Sha1

end
