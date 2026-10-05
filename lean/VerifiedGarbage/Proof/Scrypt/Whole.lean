import VerifiedGarbage.Spec.Scrypt
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Sha256.Scratch
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Framework.PowLit

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.BlockMix`. -/
section

/-!
# scryptBlockMix, one block at a time

`blockMix` in the order an implementation computes it: `Y[i]` from the
previous one (`yAt`), and the output as the blocks `Y[0], Y[2], …` followed by
`Y[1], Y[3], …`.
-/

namespace VG.Proof.Scrypt

open VG.Spec.Scrypt
open VG.Spec.Pbkdf2 (xorBytes)

variable (b : List Byte) (r : Nat)

/-- `Y[i]`. -/
def yAt : Nat → List Byte
  | 0 => salsa (xorBytes (blk b (2 * r - 1)) (blk b 0))
  | i + 1 => salsa (xorBytes (VG.Proof.Scrypt.yAt i) (blk b (i + 1)))

/-- `X` before step `i` of scryptBlockMix's step 2. -/
def xBefore : Nat → List Byte
  | 0 => blk b (2 * r - 1)
  | i + 1 => VG.Proof.Scrypt.yAt b r i

theorem yAt_eq (i : Nat) : VG.Proof.Scrypt.yAt b r i = salsa (xorBytes (VG.Proof.Scrypt.xBefore b r i) (blk b i)) := by
  cases i <;> rfl

theorem xBefore_succ (i : Nat) : VG.Proof.Scrypt.xBefore b r (i + 1) = VG.Proof.Scrypt.yAt b r i := rfl

theorem blockMixYs_range' (n : Nat) : ∀ s,
    blockMixYs b (VG.Proof.Scrypt.xBefore b r s) (List.range' s n) = (List.range' s n).map (VG.Proof.Scrypt.yAt b r) := by
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    simp only [List.range'_succ, List.map_cons, blockMixYs]
    rw [← VG.Proof.Scrypt.yAt_eq, ← VG.Proof.Scrypt.xBefore_succ, ih (s + 1)]

theorem blockMixYs_range (n : Nat) :
    blockMixYs b (blk b (2 * r - 1)) (List.range n) = (List.range n).map (VG.Proof.Scrypt.yAt b r) := by
  rw [List.range_eq_range']
  exact VG.Proof.Scrypt.blockMixYs_range' b r n 0

theorem flatMap_congr {α β : Type} {l : List α} {f g : α → List β} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self), ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- scryptBlockMix as the even-indexed `Y[i]` followed by the odd-indexed ones. -/
theorem blockMix_eq : blockMix r b =
    ((List.range r).flatMap fun i => VG.Proof.Scrypt.yAt b r (2 * i)) ++
      ((List.range r).flatMap fun i => VG.Proof.Scrypt.yAt b r (2 * i + 1)) := by
  simp only [blockMix, VG.Proof.Scrypt.blockMixYs_range]
  congr 1
  · refine VG.Proof.Scrypt.flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]; rfl
  · refine VG.Proof.Scrypt.flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]; rfl

theorem length_flatMap_const {α β : Type} (l : List α) {f : α → List β} {n : Nat}
    (h : ∀ a, (f a).length = n) : (l.flatMap f).length = n * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, h, ih, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm]

theorem serialize_length (x : Vector Word 16) : (serialize x).length = 64 := by
  rw [serialize, VG.Proof.Scrypt.length_flatMap_const _ (n := 4) fun _ => rfl]; simp

theorem salsa_length (t : List Byte) : (salsa t).length = 64 := VG.Proof.Scrypt.serialize_length _

theorem yAt_length (i : Nat) : (VG.Proof.Scrypt.yAt b r i).length = 64 := by
  rw [VG.Proof.Scrypt.yAt_eq]; exact VG.Proof.Scrypt.salsa_length _

end VG.Proof.Scrypt

end

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.Memory`. -/
section

/-!
# scrypt: memory lemmas

Addresses and regions, bytes of memory (`Spec.Scrypt.bytesAt`) read and
written, words copied, and the exclusive-or of words, which the proofs of
every target share, so that none imports another target's proof.
-/

namespace VG.Proof.Scrypt.Memory

open VG.Spec.Scrypt (bytesAt blk)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append write_eq_writeBytes)

/-! ## Addresses -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem add_ofNat (a : Addr) (o j : Nat) :
    a + BitVec.ofNat 64 o + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (o + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem toNat_add_ofNat (a : Addr) {o : Nat} (h : a.toNat + o < 2 ^ 64) :
    (a + BitVec.ofNat 64 o).toNat = a.toNat + o := by
  rw [BitVec.toNat_add, VG.Proof.Scrypt.Memory.toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt h]

/-- `[a + o, a + o + n)` lies in `[a, a + len)`. -/
theorem contains_off {a : Addr} {len o n : Nat} (h : o + n ≤ len) (ho : o < 2 ^ 64) :
    (⟨a, len⟩ : Region).Contains (a + BitVec.ofNat 64 o) n := by
  simp only [Region.Contains]
  rw [show a + BitVec.ofNat 64 o - a = BitVec.ofNat 64 o by rw [BitVec.add_comm, BitVec.add_sub_cancel], VG.Proof.Scrypt.Memory.toNat_ofNat_lt ho]; omega

/-- `[a + o, a + o + n)` is a sub-region of `[a, a + len)`. -/
theorem sub_off {a : Addr} {len o n : Nat} (h : o + n ≤ len) (ho : o < 2 ^ 64) :
    Region.Sub ⟨a + BitVec.ofNat 64 o, n⟩ ⟨a, len⟩ := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  have : (x - a).toNat ≤ (x - (a + BitVec.ofNat 64 o)).toNat + o := by
    rw [show x - a = (x - (a + BitVec.ofNat 64 o)) + BitVec.ofNat 64 o by rw [← BitVec.sub_sub, BitVec.sub_add_cancel],
      BitVec.toNat_add, VG.Proof.Scrypt.Memory.toNat_ofNat_lt (by omega)]
    exact Nat.mod_le _ _
  omega

/-- Two parts `[a + o₁, a + o₁ + n₁)` and `[a + o₂, a + o₂ + n₂)` of one
region that do not overlap. -/
theorem disj_off (a : Addr) {o₁ n₁ o₂ n₂ : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁)
    (h₁ : o₁ < 2 ^ 64) (h₂ : o₂ < 2 ^ 64) (h₁' : o₁ + n₁ ≤ 2 ^ 64) (h₂' : o₂ + n₂ ≤ 2 ^ 64) :
    Region.Disjoint ⟨a + BitVec.ofNat 64 o₁, n₁⟩ ⟨a + BitVec.ofNat 64 o₂, n₂⟩ := by
  intro x hx hy
  simp only [Region.Contains] at hx hy
  have t₁ : (BitVec.ofNat 64 o₁).toNat = o₁ := VG.Proof.Scrypt.Memory.toNat_ofNat_lt h₁
  have t₂ : (BitVec.ofNat 64 o₂).toNat = o₂ := VG.Proof.Scrypt.Memory.toNat_ofNat_lt h₂
  bv_omega

theorem InRegions.of_mem {rs : List Region} {R : Region} (hR : R ∈ rs) {a : Addr} {n : Nat}
    (h : R.Contains a n) : InRegions rs a n := ⟨R, hR, h⟩

theorem InRegions.right {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem InRegions.left {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions rd a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_left _ hr, hc⟩

/-! ## Bytes -/

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => by
    simp only [Function.comp_apply, BitVec.ofNat_add, BitVec.add_assoc]

theorem bytesAt_congr {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = m' (p + BitVec.ofNat 64 i)) :
    bytesAt m p n = bytesAt m' p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem frame_bytesAt {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  VG.Proof.Scrypt.Memory.bytesAt_congr fun _ hi => hf.bytes (R := ⟨p, n⟩) hd hn hi

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) (xs : List Byte) (hl : xs.length < 2 ^ 64) :
    bytesAt (VG.WriteBytes.writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ h₂
  simp only [bytesAt, List.getElem_map, List.getElem_range, VG.WriteBytes.writeBytes,
    Mem.sub_ofNat_toNat q (show i < 2 ^ 64 by omega), h₂, ite_true]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some]

theorem bytesAt_writeBytes_sep (m : Mem) {p q : Addr} {n : Nat} (xs : List Byte)
    (h : Region.Disjoint ⟨p, n⟩ ⟨q, xs.length⟩) (hn : n < 2 ^ 64) :
    bytesAt (VG.WriteBytes.writeBytes m q xs) p n = bytesAt m p n := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [VG.WriteBytes.writeBytes]
  split
  · exact absurd ‹_› (h _ (by simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat p (by omega)]; exact hi))
  · rfl

/-- The `64 n` bytes at `p` as `n` blocks of 64. -/
theorem bytesAt_blocks (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (64 * n) = (List.range n).flatMap fun i => bytesAt m (p + BitVec.ofNat 64 (64 * i)) 64 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, VG.Proof.Scrypt.Memory.bytesAt_add, ih, List.range_succ, List.flatMap_append,
      List.flatMap_singleton]

/-- Block `i` of the bytes at `p`. -/
theorem blk_bytesAt (m : Mem) (p : Addr) {n i : Nat} (h : 64 * i + 64 ≤ n) :
    blk (bytesAt m p n) i = bytesAt m (p + BitVec.ofNat 64 (64 * i)) 64 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 64 * i + 64 + k := ⟨n - (64 * i + 64), by omega⟩
  rw [blk, VG.Proof.Scrypt.Memory.bytesAt_add, VG.Proof.Scrypt.Memory.bytesAt_add, List.append_assoc, List.drop_left' (VG.Proof.Scrypt.Memory.bytesAt_length _ _ _),
    List.take_left' (VG.Proof.Scrypt.Memory.bytesAt_length _ _ _)]

/-! ## Words -/

/-- Writing a word read from memory writes its bytes. -/
theorem writeW_readW (m m' : Mem) (d s : Addr) (n : Nat) :
    m.writeW d (m'.readW s (8 * n)) = VG.WriteBytes.writeBytes m d (bytesAt m' s n) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show 8 * n / 8 = n by omega, BitVec.setWidth_eq, BitVec.setWidth_eq, VG.WriteBytes.write_eq_writeBytes]
  congr 1
  simp only [bytesAt]
  exact List.map_congr_left fun j hj => Mem.extractLsb'_read _ _ (List.mem_range.mp hj)

/-- One more word of `w` bytes copied from `A` to `B`. -/
theorem copy_mem (m : Mem) (A B : Addr) (n w : Nat)
    (hsep : Mem.Sep A (w * n + w) B (w * n + w)) (hlt : w * n + w < 2 ^ 64) :
    (VG.WriteBytes.writeBytes m B (bytesAt m A (w * n))).writeW (B + BitVec.ofNat 64 (w * n))
      ((VG.WriteBytes.writeBytes m B (bytesAt m A (w * n))).readW (A + BitVec.ofNat 64 (w * n)) (8 * w)) =
      VG.WriteBytes.writeBytes m B (bytesAt m A (w * n + w)) := by
  rw [VG.Proof.Scrypt.Memory.writeW_readW, VG.Proof.Scrypt.Memory.bytesAt_writeBytes_sep]
  · rw [VG.Proof.Scrypt.Memory.bytesAt_add]
    have := VG.WriteBytes.writeBytes_append m B (bytesAt m A (w * n)) (bytesAt m (A + BitVec.ofNat 64 (w * n)) w)
      (by simp [bytesAt]; omega)
    simpa [bytesAt] using this
  · intro x hx hy
    simp only [Region.Contains, bytesAt, List.length_map, List.length_range] at hx hy
    apply hsep x _ (by omega)
    rw [show x - A = (x - (A + BitVec.ofNat 64 (w * n))) + BitVec.ofNat 64 (w * n) by bv_omega,
      BitVec.toNat_add, VG.Proof.Scrypt.Memory.toNat_ofNat_lt (by omega)]
    have := Nat.mod_le ((x - (A + BitVec.ofNat 64 (w * n))).toNat + w * n) (2 ^ 64)
    omega
  · omega

theorem xorBytes_length (a b : List Byte) (h : a.length = b.length) : (xorBytes a b).length = a.length := by
  simp [xorBytes, h]

/-! ## The exclusive-or of words -/

theorem writeW_xor (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 64 ^^^ m'.readW b 64) =
      VG.WriteBytes.writeBytes m d (xorBytes (bytesAt m' a 8) (bytesAt m' b 8)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (64 : Nat) / 8 = 8 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    VG.WriteBytes.write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁, Mem.extractLsb'_read _ _ h₁]

/-- One more word of `[d] ← [x] xor [y]`. -/
theorem xor_mem (m : Mem) {d x y : Addr} {n k : Nat} (hk : k < n) (hlt : 8 * n < 2 ^ 64)
    (hdx : Region.Disjoint ⟨d, 8 * n⟩ ⟨x, 8 * n⟩) (hdy : Region.Disjoint ⟨d, 8 * n⟩ ⟨y, 8 * n⟩) :
    (VG.WriteBytes.writeBytes m d (xorBytes (bytesAt m x (8 * k)) (bytesAt m y (8 * k)))).writeW
      (d + BitVec.ofNat 64 (8 * k))
      ((VG.WriteBytes.writeBytes m d (xorBytes (bytesAt m x (8 * k)) (bytesAt m y (8 * k)))).readW
          (x + BitVec.ofNat 64 (8 * k)) 64 ^^^
        (VG.WriteBytes.writeBytes m d (xorBytes (bytesAt m x (8 * k)) (bytesAt m y (8 * k)))).readW
          (y + BitVec.ofNat 64 (8 * k)) 64) =
      VG.WriteBytes.writeBytes m d (xorBytes (bytesAt m x (8 * (k + 1))) (bytesAt m y (8 * (k + 1)))) := by
  have hl : (xorBytes (bytesAt m x (8 * k)) (bytesAt m y (8 * k))).length = 8 * k := by
    rw [VG.Proof.Scrypt.Memory.xorBytes_length _ _ (by simp [bytesAt]), VG.Proof.Scrypt.Memory.bytesAt_length]
  -- The words of `x` and `y` are not in the part of `d` written so far.
  have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (8 * k), 8⟩
      ⟨d, (xorBytes (bytesAt m x (8 * k)) (bytesAt m y (8 * k))).length⟩ := by
    rw [hl]; exact (hdx.symm.sub_left (VG.Proof.Scrypt.Memory.sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (8 * k), 8⟩
      ⟨d, (xorBytes (bytesAt m x (8 * k)) (bytesAt m y (8 * k))).length⟩ := by
    rw [hl]; exact (hdy.symm.sub_left (VG.Proof.Scrypt.Memory.sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  rw [VG.Proof.Scrypt.Memory.writeW_xor, VG.Proof.Scrypt.Memory.bytesAt_writeBytes_sep _ _ sx (by omega), VG.Proof.Scrypt.Memory.bytesAt_writeBytes_sep _ _ sy (by omega)]
  have e := VG.WriteBytes.writeBytes_append m d _ (xorBytes (bytesAt m (x + BitVec.ofNat 64 (8 * k)) 8)
    (bytesAt m (y + BitVec.ofNat 64 (8 * k)) 8))
    (by rw [hl, VG.Proof.Scrypt.Memory.xorBytes_length _ _ (by simp [bytesAt]), VG.Proof.Scrypt.Memory.bytesAt_length]; omega)
  rw [hl] at e
  rw [e, Nat.mul_succ, VG.Proof.Scrypt.Memory.bytesAt_add, VG.Proof.Scrypt.Memory.bytesAt_add, xorBytes, xorBytes, xorBytes,
    List.zipWith_append (by simp [bytesAt])]

/-! ## Arithmetic -/

theorem dbl_pow (x k : Nat) : BitVec.ofNat 64 (x * 2 ^ k) + BitVec.ofNat 64 (x * 2 ^ k) =
    BitVec.ofNat 64 (x * 2 ^ (k + 1)) := by
  rw [← BitVec.ofNat_add, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]

end VG.Proof.Scrypt.Memory

end

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.RoMix`. -/
section

/-!
# scryptROMix: facts about the specification

Target-independent facts about `Spec.Scrypt.roMix`: the blocks `V[i]` step 2
writes (`vList`), step 3 one iteration at a time (`mixLoop_succ_fst`,
`mixLoop_succ_snd`), the lengths of the blocks, and `Integerify (X) mod 2^e`
as a little-endian word read from memory (`integerify_mod`).
-/

namespace VG.Proof.Scrypt

open VG.Spec.Scrypt
open VG.Spec.Pbkdf2 (xorBytes)

/-! ## Step 2: the blocks `V[i]` -/

/-- The blocks `V[0], …, V[N - 1]` that step 2 of scryptROMix writes. -/
abbrev vList (r N : Nat) (b : List Byte) : List (List Byte) :=
  (List.range N).map fun i => Nat.repeat (blockMix r) i b

theorem vList_getD {r N j : Nat} (b : List Byte) (hj : j < N) :
    (VG.Proof.Scrypt.vList r N b).getD j [] = Nat.repeat (blockMix r) j b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]; rfl

theorem roMix_eq (r N : Nat) (b : List Byte) :
    roMix r N b = (mixLoop r N (VG.Proof.Scrypt.vList r N b) N (Nat.repeat (blockMix r) N b)).1 := rfl

theorem roMixIndices_eq (r N : Nat) (b : List Byte) :
    roMixIndices r N b = (mixLoop r N (VG.Proof.Scrypt.vList r N b) N (Nat.repeat (blockMix r) N b)).2 := rfl

/-! ## Step 3, one iteration at a time -/

theorem mixLoop_succ_fst (r N : Nat) (v : List (List Byte)) (n : Nat) (x : List Byte) :
    (mixLoop r N v (n + 1) x).1 =
      (mixLoop r N v n (blockMix r (xorBytes x (v.getD (integerify r x % N) [])))).1 := rfl

theorem mixLoop_succ_snd (r N : Nat) (v : List (List Byte)) (n : Nat) (x : List Byte) :
    (mixLoop r N v (n + 1) x).2 = integerify r x % N ::
      (mixLoop r N v n (blockMix r (xorBytes x (v.getD (integerify r x % N) [])))).2 := rfl

/-! ## Lengths -/

theorem blockMix_length {r : Nat} {b : List Byte} (_h : b.length = 128 * r) :
    (blockMix r b).length = 128 * r := by
  rw [VG.Proof.Scrypt.blockMix_eq, List.length_append, VG.Proof.Scrypt.length_flatMap_const _ fun _ => VG.Proof.Scrypt.yAt_length _ _ _,
    VG.Proof.Scrypt.length_flatMap_const _ fun _ => VG.Proof.Scrypt.yAt_length _ _ _, List.length_range]
  omega

theorem repeat_blockMix_length {r : Nat} {b : List Byte} (h : b.length = 128 * r) (i : Nat) :
    (Nat.repeat (blockMix r) i b).length = 128 * r := by
  induction i with
  | zero => exact h
  | succ i ih => exact VG.Proof.Scrypt.blockMix_length ih

/-! ## `Integerify` -/

theorem bytesAt_length' (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem bytesAt_add' (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => by
    simp only [Function.comp_apply, BitVec.ofNat_add, BitVec.add_assoc]

theorem bytesAt_succ (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (n + 1) = m p :: bytesAt m (p + 1) n := by
  simp only [bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · rw [BitVec.add_zero]
  · exact List.map_congr_left fun i _ => by
      simp only [Function.comp_apply]
      rw [show p + BitVec.ofNat 64 (i + 1) = p + 1 + BitVec.ofNat 64 i by bv_omega]

/-- `B[i]` of the bytes at `p` is the 64 bytes at `p + 64 i`. -/
theorem blk_bytesAt' (m : Mem) (p : Addr) {n i : Nat} (h : 64 * i + 64 ≤ n) :
    blk (bytesAt m p n) i = bytesAt m (p + BitVec.ofNat 64 (64 * i)) 64 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 64 * i + 64 + k := ⟨n - (64 * i + 64), by omega⟩
  rw [blk, VG.Proof.Scrypt.bytesAt_add', VG.Proof.Scrypt.bytesAt_add', List.append_assoc, List.drop_left' (VG.Proof.Scrypt.bytesAt_length' _ _ _),
    List.take_left' (VG.Proof.Scrypt.bytesAt_length' _ _ _)]

theorem leNat_append (xs ys : List Byte) :
    leNat (xs ++ ys) = leNat xs + 256 ^ xs.length * leNat ys := by
  induction xs with
  | nil => simp [leNat]
  | cons x xs ih =>
    simp only [leNat, List.foldr_cons, List.cons_append, List.length_cons] at ih ⊢
    rw [ih, Nat.pow_succ, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc, Nat.mul_left_comm]

theorem toNat_append8 {n : Nat} (x : BitVec n) (y : BitVec 8) :
    (x ++ y).toNat = y.toNat + 256 * x.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]
  omega

/-- The `n` bytes at `a`, read as a little-endian integer, are `m.read a n`. -/
theorem leNat_bytesAt (m : Mem) (a : Addr) (n : Nat) :
    leNat (bytesAt m a n) = (m.read a n).toNat := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [VG.Proof.Scrypt.bytesAt_succ, Mem.read, VG.Proof.Scrypt.toNat_append8, ← ih]
    rfl

theorem leNat_bytesAt64_mod (m : Mem) (a : Addr) {e : Nat} (he : e ≤ 64) :
    leNat (bytesAt m a 64) % 2 ^ e = (m.readW a 64).toNat % 2 ^ e := by
  rw [show (64 : Nat) = 8 + 56 from rfl, VG.Proof.Scrypt.bytesAt_add', VG.Proof.Scrypt.leNat_append, VG.Proof.Scrypt.bytesAt_length',
    show (256 : Nat) ^ 8 = 2 ^ e * 2 ^ (64 - e) by rw [← Nat.pow_add, Nat.add_sub_cancel' he],
    Nat.mul_assoc, Nat.add_mul_mod_self_left, VG.Proof.Scrypt.leNat_bytesAt]
  simp only [Mem.readW, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (BitVec.isLt _)]

/-- `Integerify (X) mod 2^e`, for `e ≤ 64`, is the first 8 bytes of `X`'s last
64-byte block, read little-endian, mod `2^e`. -/
theorem integerify_mod (m : Mem) (p : Addr) {r e : Nat} (hr : 0 < r) (he : e ≤ 64) :
    integerify r (bytesAt m p (128 * r)) % 2 ^ e =
      (m.readW (p + BitVec.ofNat 64 (128 * r - 64)) 64).toNat % 2 ^ e := by
  rw [integerify, VG.Proof.Scrypt.blk_bytesAt' _ _ (by omega), show 64 * (2 * r - 1) = 128 * r - 64 by omega,
    VG.Proof.Scrypt.leNat_bytesAt64_mod _ _ he]

theorem and_mask (w : BitVec 64) {e : Nat} (he : e ≤ 64) :
    (w &&& BitVec.ofNat 64 (2 ^ e - 1)).toNat = w.toNat % 2 ^ e := by
  have := Nat.pow_le_pow_right (by omega : 0 < 2) he
  have := Nat.one_le_two_pow (n := e)
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.and_two_pow_sub_one_eq_mod]

end VG.Proof.Scrypt

end

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.Whole`. -/
section

/-!
# scrypt: facts about the specification of the whole function

Target-independent facts for the proofs of `vg_scrypt`: the parameters `valid`
admits, the blocks of step 1 in memory (`bytesAt_chunks`, `chunk_bytesAt`),
the indices each scryptROMix leaks, recovered from the list the contract
declares (`indices_eq`), and `scrypt` from its three steps (`scrypt_eq`).
-/

namespace VG.Proof.Scrypt.Whole

open VG.Spec.Scrypt
open VG.Proof.Scrypt.Memory (bytesAt_add bytesAt_length)

/-! ## The parameters -/

/-- A positive number with no bit in common with its predecessor is a power of
two. -/
theorem isPowerOfTwo_of_and : ∀ n : Nat, 0 < n → n &&& (n - 1) = 0 → n.isPowerOfTwo
  | n, hn, h => by
    induction n using Nat.strongRecOn with
    | _ n ih =>
      obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
      · -- `n = 2 m`: `2 m &&& (2 m - 1) = 2 (m &&& (m - 1))`.
        have hm : 0 < m := by omega
        have e : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
        have h' : m &&& (m - 1) = 0 := by
          apply Nat.eq_of_testBit_eq
          intro i
          have := congrArg (fun x => x.testBit (i + 1)) h
          rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_succ, Nat.testBit_succ,
            show 2 * m / 2 = m by omega, show (2 * m - 1) / 2 = m - 1 by omega] at this
          rw [Nat.testBit_and, Nat.zero_testBit, this]
        obtain ⟨k, hk⟩ := ih m (by omega) hm h'
        exact ⟨k + 1, by rw [hk, Nat.pow_succ, Nat.mul_comm]⟩
      · -- `n = 2 m + 1`: `n &&& (n - 1) = 2 m`, so `m = 0`.
        have h' : m = 0 := by
          apply Nat.eq_of_testBit_eq
          intro i
          have := congrArg (fun x => x.testBit (i + 1)) h
          simp only [Nat.add_sub_cancel] at this
          rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_succ, Nat.testBit_succ,
            show (2 * m + 1) / 2 = m by omega, show 2 * m / 2 = m by omega, Bool.and_self] at this
          rw [Nat.zero_testBit, this]
        exact ⟨0, by omega⟩

theorem valid_pow {N r p dk : Nat} (h : valid N r p dk) : N.isPowerOfTwo :=
  VG.Proof.Scrypt.Whole.isPowerOfTwo_of_and N (by have := h.1; omega) h.2.1

theorem valid_r {N r p dk : Nat} (h : valid N r p dk) : 0 < r := by
  have h₁ := h.1
  have h₃ := h.2.2.1
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp at h₃; omega
  · exact hr

/-! ## Indices -/

theorem mixLoop_snd_length (r N : Nat) (v : List (List Byte)) :
    ∀ (n : Nat) (x : List Byte), (mixLoop r N v n x).2.length = n
  | 0, _ => rfl
  | n + 1, x => by
    rw [Proof.Scrypt.mixLoop_succ_snd, List.length_cons, VG.Proof.Scrypt.Whole.mixLoop_snd_length r N v n]

theorem roMixIndices_length (r N : Nat) (b : List Byte) : (roMixIndices r N b).length = N := by
  rw [Proof.Scrypt.roMixIndices_eq, VG.Proof.Scrypt.Whole.mixLoop_snd_length]

/-- The `i`th part of `N` elements of `l.flatMap f`, if each `f a` has `N`. -/
theorem flatMap_chunk {α β : Type} (f : α → List β) {N : Nat} (hf : ∀ a, (f a).length = N) :
    ∀ (l : List α) (i : Nat) (hi : i < l.length), ((l.flatMap f).drop (N * i)).take N = f l[i]
  | a :: l, 0, _ => by
    rw [List.flatMap_cons, Nat.mul_zero, List.drop_zero, List.take_left' (hf a)]; rfl
  | a :: l, i + 1, hi => by
    rw [List.flatMap_cons, Nat.mul_succ, Nat.add_comm, ← List.drop_drop, List.drop_left' (hf a)]
    exact VG.Proof.Scrypt.Whole.flatMap_chunk f hf l i (by simp at hi; omega)

/-- The indices each scryptROMix leaks, from the list of all of them. -/
theorem indices_eq {r N : Nat} {l₁ l₂ : List (List Byte)}
    (h : l₁.flatMap (roMixIndices r N) = l₂.flatMap (roMixIndices r N)) {i : Nat}
    (h₁ : i < l₁.length) (h₂ : i < l₂.length) :
    roMixIndices r N l₁[i] = roMixIndices r N l₂[i] := by
  rw [← VG.Proof.Scrypt.Whole.flatMap_chunk _ (VG.Proof.Scrypt.Whole.roMixIndices_length r N) l₁ i h₁, h,
    VG.Proof.Scrypt.Whole.flatMap_chunk _ (VG.Proof.Scrypt.Whole.roMixIndices_length r N) l₂ i h₂]

/-! ## The blocks in memory -/

/-- The `n k` bytes at `p` as `k` parts of `n`. -/
theorem bytesAt_chunks (m : Mem) (p : Addr) (n : Nat) :
    ∀ k, bytesAt m p (n * k) =
      (List.range k).flatMap fun i => bytesAt m (p + BitVec.ofNat 64 (n * i)) n
  | 0 => rfl
  | k + 1 => by
    rw [Nat.mul_succ, VG.Proof.Scrypt.Memory.bytesAt_add, VG.Proof.Scrypt.Whole.bytesAt_chunks m p n k, List.range_succ, List.flatMap_append,
      List.flatMap_singleton]

/-- Part `i` of `n` bytes of the bytes at `p`. -/
theorem chunk_bytesAt (m : Mem) (p : Addr) {n i k : Nat} (h : n * i + n ≤ k) :
    ((bytesAt m p k).drop (n * i)).take n = bytesAt m (p + BitVec.ofNat 64 (n * i)) n := by
  obtain ⟨j, rfl⟩ : ∃ j, k = n * i + n + j := ⟨k - (n * i + n), by omega⟩
  rw [VG.Proof.Scrypt.Memory.bytesAt_add, VG.Proof.Scrypt.Memory.bytesAt_add, List.append_assoc, List.drop_left' (VG.Proof.Scrypt.Memory.bytesAt_length _ _ _),
    List.take_left' (VG.Proof.Scrypt.Memory.bytesAt_length _ _ _)]

/-- The blocks of step 1, if PBKDF2 wrote `B` to `p`. -/
theorem blocks_getElem {pw s : List Byte} {r p : Nat} {m : Mem} {b : Addr}
    (h : Spec.Pbkdf2.pbkdf2HmacSha256 pw s 1 (p * 128 * r) = some (bytesAt m b (p * 128 * r)))
    {i : Nat} (hi : i < (blocks pw s r p).length) :
    (blocks pw s r p)[i] = bytesAt m (b + BitVec.ofNat 64 (128 * r * i)) (128 * r) := by
  simp only [blocks, h, Option.getD_some, List.getElem_map, List.getElem_range]
  exact VG.Proof.Scrypt.Whole.chunk_bytesAt m b (by
    simp only [blocks, List.length_map, List.length_range] at hi
    have : 128 * r * i + 128 * r ≤ 128 * r * p := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
    rw [show p * 128 * r = 128 * r * p by rw [Nat.mul_comm, Nat.mul_comm p, Nat.mul_assoc, Nat.mul_left_comm]]
    exact this)

theorem blocks_length (pw s : List Byte) (r p : Nat) : (blocks pw s r p).length = p := by
  simp [blocks]

/-! ## The whole function -/

/-- `scrypt` from its three steps. -/
theorem scrypt_eq {pw s : List Byte} {N r p dk : Nat} {B out : List Byte} (hv : valid N r p dk)
    (h₁ : Spec.Pbkdf2.pbkdf2HmacSha256 pw s 1 (p * 128 * r) = some B)
    (h₂ : Spec.Pbkdf2.pbkdf2HmacSha256 pw
      ((List.range p).flatMap fun i => roMix r N ((B.drop (128 * r * i)).take (128 * r))) 1 dk = some out) :
    scrypt pw s N r p dk = some out := by
  simp only [scrypt, hv, ite_true, h₁]
  exact h₂

end VG.Proof.Scrypt.Whole

end
