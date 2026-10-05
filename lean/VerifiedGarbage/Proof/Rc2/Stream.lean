import VerifiedGarbage.Spec.Rc2
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Spec.Rc2.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Select`. -/
section

/-! # Arithmetic selection lemmas for RC2's constant-time lookups -/

namespace VG.Proof.Rc2

theorem maskByte (x : BitVec 64) : x &&& 255 = (x.setWidth 8).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
  change x.toNat &&& (2 ^ 8 - 1) = x.toNat % 256 % 18446744073709551616
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem joinBytes (lo hi : Byte) :
    lo.setWidth 64 ||| (hi.setWidth 64).rotateRight 56 =
      (lo.setWidth 16 ||| hi.setWidth 16 <<< 8).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_shiftLeft]
  by_cases h8 : j < 8
  · simp (disch := omega) [h8, show j < 16 by omega,
      BitVec.getLsbD_of_ge]
  · by_cases h16 : j < 16
    · simp (disch := omega) [h8, h16, hj, show j - 8 < 64 by omega,
        show j - 8 < 16 by omega, BitVec.getLsbD_of_ge]
    · simp (disch := omega) [h8, h16,
        BitVec.getLsbD_of_ge]

/-- Subtraction exposes zero in the top bit for inputs smaller than 2⁶³. -/
theorem zeroBit (x : BitVec 64) (hx : x.toNat < 2 ^ 63) :
    (x - 1) >>> 63 = if x = 0 then 1 else 0 := by
  by_cases h : x = 0
  · subst x; decide
  · simp only [h, ite_false]
    bv_omega

theorem selectMask_eq (x y : BitVec 8) :
    (0 - (((x.setWidth 64 ^^^ y.setWidth 64) - 1) >>> 63) : BitVec 64) =
      if x = y then BitVec.allOnes 64 else 0 := by
  have hbound : (x.setWidth 64 ^^^ y.setWidth 64).toNat < 2 ^ 63 := by
    rw [← BitVec.setWidth_xor]
    simp only [BitVec.toNat_setWidth]
    have := (x ^^^ y).isLt
    omega
  rw [VG.Proof.Rc2.zeroBit _ hbound]
  have he : (x.setWidth 64 ^^^ y.setWidth 64 = 0#64) ↔ x = y := by
    rw [BitVec.xor_eq_zero_iff]
    constructor
    · intro h
      have := congrArg (BitVec.setWidth 8) h
      simpa using this
    · exact congrArg (BitVec.setWidth 64)
  by_cases h : x = y
  · subst y; simp
  · have hn := mt he.mp h
    simp [hn, h]

/-- OR accumulation of a uniquely selected candidate, even in an arbitrary
order. Repeated candidates are harmless because OR is idempotent. -/
theorem select_fold (f : Nat → BitVec 64) (x : Nat) (is : List Nat) (acc : BitVec 64) :
    is.foldl (fun a i => a ||| if x = i then f i else 0) acc =
      acc ||| if x ∈ is then f x else 0 := by
  induction is generalizing acc with
  | nil => simp
  | cons i is ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    by_cases h : x = i
    · subst i
      by_cases hm : x ∈ is <;> simp [hm, BitVec.or_assoc]
    · by_cases hm : x ∈ is <;> simp [h, hm]

end VG.Proof.Rc2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Word`. -/
section

/-! # RC2 word arithmetic in 64-bit registers -/

namespace VG.Proof.Rc2

theorem maskWord (x : BitVec 64) : x &&& 65535 = (x.setWidth 16).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
  change x.toNat &&& (2 ^ 16 - 1) = x.toNat % 65536 % 18446744073709551616
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem maskWord_lit (x : BitVec 64) : x &&& 65535#64 = (x.setWidth 16).setWidth 64 :=
  VG.Proof.Rc2.maskWord x

theorem rotateWord (x : BitVec 16) (n : Nat) (hn : 1 ≤ n) (hn' : n < 16) :
    ((x.setWidth 64).rotateRight (64 - n) ||| (x.setWidth 64) >>> (16 - n)) &&& 65535 =
      (x.rotateLeft n).setWidth 64 := by
  rw [VG.Proof.Rc2.maskWord]
  apply congrArg (BitVec.setWidth 64)
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateLeft]
  have n64 : (64 - n) % 64 = 64 - n := Nat.mod_eq_of_lt (by omega)
  have n16 : n % 16 = n := Nat.mod_eq_of_lt hn'
  rw [n64, n16]
  rw [show 64 - (64 - n) = n by omega]
  by_cases h : j < n
  · simp (disch := omega) [h, hj,
      show j + (16 - n) < 64 by omega, BitVec.getLsbD_of_ge, Nat.add_comm]
  · simp (disch := omega) [h, hj, show j < 64 by omega,
      show j - n < 64 by omega, BitVec.getLsbD_of_ge]

theorem mixWord (x k a b c : BitVec 16) :
    (x.setWidth 64 + k.setWidth 64 +
      ((a.setWidth 64 &&& b.setWidth 64) + (~~~(a.setWidth 64) &&& c.setWidth 64))) &&& 65535 =
      (x + k + (a &&& b) + (~~~a &&& c)).setWidth 64 := by
  rw [VG.Proof.Rc2.maskWord]
  apply congrArg (BitVec.setWidth 64)
  simp [BitVec.setWidth_add, BitVec.setWidth_not, BitVec.add_assoc]

theorem reverseMixWord (x k a b c : BitVec 16) :
    (x.setWidth 64 - k.setWidth 64 -
      ((a.setWidth 64 &&& b.setWidth 64) + (~~~(a.setWidth 64) &&& c.setWidth 64))) &&& 65535 =
      (x - k - (a &&& b) - (~~~a &&& c)).setWidth 64 := by
  rw [VG.Proof.Rc2.maskWord]
  apply congrArg (BitVec.setWidth 64)
  simp [BitVec.sub_eq_add_neg, BitVec.setWidth_add, BitVec.setWidth_neg_of_le,
    BitVec.setWidth_not, BitVec.add_assoc, BitVec.neg_add]

theorem rotateLeft_reverse (x : BitVec 16) (n : Nat) (hn : 1 ≤ n) (hn' : n < 16) :
    x.rotateLeft (16 - n) = x.rotateRight n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight,
    Nat.mod_eq_of_lt hn', Nat.mod_eq_of_lt (show 16 - n < 16 by omega),
    show 16 - (16 - n) = n by omega]

theorem subInputsWord (x k c : BitVec 64) :
    (x - k - c) &&& 65535 =
      (x.setWidth 16 - k.setWidth 16 - c.setWidth 16).setWidth 64 := by
  rw [VG.Proof.Rc2.maskWord]
  simp [BitVec.sub_eq_add_neg, BitVec.setWidth_add, BitVec.setWidth_neg_of_le]

end VG.Proof.Rc2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Memory`. -/
section

/-! # RC2's little-endian block representation -/

namespace VG.Proof.Rc2

open VG

theorem read64_byte (m : Mem) (p : Addr) (i : Nat) (hi : i < 8) :
    (m.readW p 64).extractLsb' (8 * i) 8 = m (p + BitVec.ofNat 64 i) := by
  change (m.read p 8).extractLsb' (8 * i) 8 = _
  exact Mem.extractLsb'_read m p hi

theorem extractWord (x : BitVec 64) (i : Nat) :
    ((x.extractLsb' (8 * (2 * i)) 8).setWidth 16 |||
      (x.extractLsb' (8 * (2 * i + 1)) 8).setWidth 16 <<< 8) =
        (x >>> (16 * i)).setWidth 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight]
  by_cases h : j < 8
  · simp only [hj, h, decide_true, Bool.true_and, Bool.not_true,
      Bool.false_and, Bool.or_false]
    apply congrArg x.getLsbD
    omega
  · simp only [hj, h, decide_true, Bool.true_and, decide_false, Bool.false_and,
      Bool.not_false, Bool.false_or, show j - 8 < 16 by omega, show j - 8 < 8 by omega]
    apply congrArg x.getLsbD
    omega

theorem getD_ofFn {α : Type} {n : Nat} (f : Fin n → α) (i : Nat) (hi : i < n) (d : α) :
    (Vector.ofFn f).getD i d = f ⟨i, hi⟩ := by
  simp [Vector.getD, hi]

theorem getD_eq_getElem {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (hi : i < n) (d : α) :
    v.getD i d = v[i] := by
  simp [Vector.getD, hi]

theorem decode_read64 (m : Mem) (p : Addr) (i : Nat) (hi : i < 4) :
    (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt m p)).getD i 0 =
      ((m.readW p 64) >>> (16 * i)).setWidth 16 := by
  rw [Spec.Rc2.decodeBlock, VG.Proof.Rc2.getD_ofFn _ i hi]
  change ((Spec.Rc2.blockAt m p).getD (2 * i) 0).setWidth 16 |||
    ((Spec.Rc2.blockAt m p).getD (2 * i + 1) 0).setWidth 16 <<< 8 = _
  have lo : 2 * i < 8 := by omega
  have hi' : 2 * i + 1 < 8 := by omega
  rw [Spec.Rc2.blockAt, VG.Proof.Rc2.getD_ofFn _ _ lo, VG.Proof.Rc2.getD_ofFn _ _ hi']
  rw [← VG.Proof.Rc2.read64_byte m p (2 * i) lo, ← VG.Proof.Rc2.read64_byte m p (2 * i + 1) hi']
  exact VG.Proof.Rc2.extractWord _ i

/-- Concatenation of RC2's four little-endian words. -/
def pack (v : Spec.Rc2.State) : BitVec 64 :=
  ((v.getD 3 0 ++ v.getD 2 0) ++ v.getD 1 0) ++ v.getD 0 0

theorem pack_word (v : Spec.Rc2.State) (i : Nat) (hi : i < 4) :
    ((VG.Proof.Rc2.pack v) >>> (16 * i)).setWidth 16 = v.getD i 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [VG.Proof.Rc2.pack, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with h | h | h | h <;> subst i <;>
    simp (disch := omega) only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul, Nat.zero_add,
      ite_eq_left, ite_eq_right, Nat.add_sub_cancel_left]
  all_goals apply congrArg (BitVec.getLsbD _); omega

/-- Extracting a byte within a 16-bit word agrees with extracting the
same byte directly from the packed block. -/
theorem word_byte (x : BitVec 64) (i : Nat) :
    (((x >>> (16 * (i / 2))).setWidth 16) >>> (8 * (i % 2))).setWidth 8 =
      x.extractLsb' (8 * i) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  have bound : 8 * (i % 2) + j < 16 := by omega
  rw [show decide (8 * (i % 2) + j < 16) = true by simp [bound], Bool.true_and]
  congr 1; omega

theorem encode_pack (v : Spec.Rc2.State) (i : Nat) (hi : i < 8) :
    (Spec.Rc2.encodeBlock v).getD i 0 = (VG.Proof.Rc2.pack v).extractLsb' (8 * i) 8 := by
  rw [Spec.Rc2.encodeBlock, VG.Proof.Rc2.getD_ofFn _ i hi]
  rw [← VG.Proof.Rc2.pack_word v (i / 2) (by omega)]
  exact VG.Proof.Rc2.word_byte _ i

theorem blockAt_write64 (m : Mem) (p : Addr) (v : Spec.Rc2.State) :
    Spec.Rc2.blockAt (m.writeW p (VG.Proof.Rc2.pack v)) p = Spec.Rc2.encodeBlock v := by
  apply Vector.ext
  intro i hi
  have he := VG.Proof.Rc2.encode_pack v i hi
  rw [VG.Proof.Rc2.getD_eq_getElem _ i hi] at he
  rw [he]
  rw [Spec.Rc2.blockAt, Vector.getElem_ofFn]
  simp only [Mem.writeW, BitVec.setWidth_eq, Mem.write,
    Mem.sub_ofNat_toNat p (show i < 2 ^ 64 by omega), hi, ite_true]

theorem pack_eq (v : Spec.Rc2.State) : VG.Proof.Rc2.pack v =
    (((v.getD 0 0).setWidth 64 ||| ((v.getD 1 0).setWidth 64).rotateRight 48) |||
      ((v.getD 2 0).setWidth 64).rotateRight 32) |||
      ((v.getD 3 0).setWidth 64).rotateRight 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [VG.Proof.Rc2.pack, BitVec.getLsbD_append, BitVec.getLsbD_or, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_rotateRight]
  have subBound (n : Nat) : j - n < 64 := by omega
  by_cases h₁ : j < 16
  · simp (disch := omega) [h₁, hj, show j < 32 by omega, show j < 48 by omega, BitVec.getLsbD_of_ge]
  · by_cases h₂ : j < 32
    · simp (disch := omega) [h₁, h₂, hj, show j < 48 by omega, subBound, BitVec.getLsbD_of_ge,
        show j - 16 < 16 by omega]
    · by_cases h₃ : j < 48
      · simp (disch := omega) [h₁, h₂, h₃, hj, subBound, BitVec.getLsbD_of_ge]
        simp (disch := omega) only [ite_eq_left, ite_eq_right]
        simp only [Nat.sub_sub, Nat.reduceAdd]
      · simp (disch := omega) [h₁, h₂, h₃, hj, subBound, BitVec.getLsbD_of_ge]
        simp (disch := omega) only [ite_eq_right]
        simp only [Nat.sub_sub, Nat.reduceAdd]

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (p : Addr)
    (hd : ∀ r ∈ rs, (Region.mk p 8).Disjoint r) :
    Spec.Rc2.blockAt m' p = Spec.Rc2.blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Rc2.blockAt, Vector.getElem_ofFn]
  exact hf.bytes hd (show 8 ≤ 2 ^ 64 by decide) hi

theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (p : Addr)
    (hd : ∀ r ∈ rs, (Region.mk p 128).Disjoint r) :
    Spec.Rc2.scheduleAt m' p = Spec.Rc2.scheduleAt m p := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Rc2.scheduleAt, Vector.getElem_ofFn]
  rw [hf.bytes hd (show 128 ≤ 2 ^ 64 by decide) (show 2 * i < 128 by omega),
    hf.bytes hd (show 128 ≤ 2 ^ 64 by decide) (show 2 * i + 1 < 128 by omega)]

end VG.Proof.Rc2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.CbcMemory`. -/
section

/-! # CBC block copying, XOR, and consecutive-block memory layouts -/

namespace VG.Proof.Rc2

open VG

def wordBlock (x : BitVec 64) : Spec.Rc2.Block := Vector.ofFn fun i => x.extractLsb' (8 * i.val) 8

theorem blockAt_read64 (m : Mem) (p : Addr) : Spec.Rc2.blockAt m p = VG.Proof.Rc2.wordBlock (m.readW p 64) := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Rc2.blockAt, VG.Proof.Rc2.wordBlock, Vector.getElem_ofFn]
  exact (VG.Proof.Rc2.read64_byte m p i hi).symm

theorem wordBlock_xor (x y : BitVec 64) :
    VG.Proof.Rc2.wordBlock (x ^^^ y) = Spec.Rc2.xorBlock (VG.Proof.Rc2.wordBlock x) (VG.Proof.Rc2.wordBlock y) := by
  apply Vector.ext
  intro i hi
  simp only [VG.Proof.Rc2.wordBlock, Spec.Rc2.xorBlock, Vector.getElem_ofFn, Fin.getElem_fin, BitVec.extractLsb'_xor]

theorem blockAt_store64 (m : Mem) (p : Addr) (x : BitVec 64) :
    Spec.Rc2.blockAt (m.writeW p x) p = VG.Proof.Rc2.wordBlock x := by
  rw [VG.Proof.Rc2.blockAt_read64, Mem.readW_writeW_self64]

theorem frame_store64 (m : Mem) (p : Addr) (x : BitVec 64) :
    Frame [⟨p, 8⟩] m (m.writeW p x) :=
  (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)

theorem blockAt_copy (m : Mem) (dst src : Addr) :
    Spec.Rc2.blockAt (m.writeW dst (m.readW src 64)) dst = Spec.Rc2.blockAt m src := by
  rw [VG.Proof.Rc2.blockAt_store64, VG.Proof.Rc2.blockAt_read64 m src]

theorem blockAt_xor (m : Mem) (dst iv : Addr) :
    Spec.Rc2.blockAt (m.writeW dst (m.readW dst 64 ^^^ m.readW iv 64)) dst =
      Spec.Rc2.xorBlock (Spec.Rc2.blockAt m dst) (Spec.Rc2.blockAt m iv) := by
  rw [VG.Proof.Rc2.blockAt_store64, VG.Proof.Rc2.wordBlock_xor, VG.Proof.Rc2.blockAt_read64 m dst, VG.Proof.Rc2.blockAt_read64 m iv]

theorem blocksAt_cons (m : Mem) (p : Addr) (n : Nat) :
    Spec.Rc2.blocksAt m p (n + 1) = Spec.Rc2.blockAt m p :: Spec.Rc2.blocksAt m (p + 8) n := by
  rw [Spec.Rc2.blocksAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.cons.injEq, true_and]
  apply List.map_congr_left
  intro i _
  apply congrArg (Spec.Rc2.blockAt m)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (fun j => p + BitVec.ofNat 64 j) (by omega)

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (p : Addr) (n : Nat)
    (hd : ∀ r ∈ rs, (Region.mk p (8 * n)).Disjoint r) :
    Spec.Rc2.blocksAt m' p n = Spec.Rc2.blocksAt m p n := by
  unfold Spec.Rc2.blocksAt
  apply List.map_congr_left
  intro i hi
  apply VG.Proof.Rc2.blockAt_frame hf
  intro r hr
  exact (hd r hr).sub_left (Offset.sub_base p (by
    have h := List.mem_range.mp hi
    omega))

end VG.Proof.Rc2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.CbcList`. -/
section

/-! # CBC over lists of blocks: concatenation, and decryption block by block -/

namespace VG.Proof.Rc2

open VG

theorem cbc_append (k : Spec.Rc2.Schedule) (d : Spec.Rc2.Direction) (iv : Spec.Rc2.Block)
    (A B : List Spec.Rc2.Block) :
    Spec.Rc2.cbc k d iv (A ++ B) =
      ((Spec.Rc2.cbc k d iv A).1 ++ (Spec.Rc2.cbc k d (Spec.Rc2.cbc k d iv A).2 B).1,
        (Spec.Rc2.cbc k d (Spec.Rc2.cbc k d iv A).2 B).2) := by
  induction A generalizing iv with
  | nil => rfl
  | cons a A ih => simp only [List.cons_append, Spec.Rc2.cbc, ih]

/-- Decryption: each block decrypted and XORed with the ciphertext block before it. -/
theorem cbc_decrypt (k : Spec.Rc2.Schedule) (iv : Spec.Rc2.Block) (cs : List Spec.Rc2.Block) :
    Spec.Rc2.cbc k .decrypt iv cs =
      (List.zipWith (fun c p => Spec.Rc2.xorBlock (Spec.Rc2.decryptBlock k c) p) cs (iv :: cs),
        (iv :: cs).getLast (List.cons_ne_nil _ _)) := by
  induction cs generalizing iv with
  | nil => rfl
  | cons c cs ih =>
    simp only [Spec.Rc2.cbc, Spec.Rc2.cbcStep, ih, List.zipWith_cons_cons, List.getLast_cons_cons]

theorem blocksAt_add (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rc2.blocksAt m p (a + b) =
      Spec.Rc2.blocksAt m p a ++ Spec.Rc2.blocksAt m (p + BitVec.ofNat 64 (8 * a)) b := by
  simp only [Spec.Rc2.blocksAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Offset.add_add, Nat.mul_add]

theorem blocksAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rc2.blocksAt m p n).length = n := by
  simp [Spec.Rc2.blocksAt]

theorem blocksAt_getElem (m : Mem) (p : Addr) {n i : Nat} (hi : i < (Spec.Rc2.blocksAt m p n).length) :
    (Spec.Rc2.blocksAt m p n)[i] = Spec.Rc2.blockAt m (p + BitVec.ofNat 64 (8 * i)) := by
  simp [Spec.Rc2.blocksAt]

end VG.Proof.Rc2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Expansion`. -/
section

/-! # Key-expansion loops and their byte-array representation -/

namespace VG.Proof.Rc2

open VG

abbrev KeyBytes := Vector Byte 128

def fillStep (t j : Nat) (l : VG.Proof.Rc2.KeyBytes) : VG.Proof.Rc2.KeyBytes :=
  let i := t + j
  l.set! i (Spec.Rc2.pi (l.getD (i - 1) 0 + l.getD (i - t) 0))

def fill (key : List Byte) (n : Nat) : VG.Proof.Rc2.KeyBytes :=
  (List.range n).foldl (fun l j => VG.Proof.Rc2.fillStep key.length j l)
    (Vector.ofFn fun i => key.getD i 0)

def descendStep (t8 j : Nat) (l : VG.Proof.Rc2.KeyBytes) : VG.Proof.Rc2.KeyBytes :=
  let i := 127 - t8 - j
  l.set! i (Spec.Rc2.pi (l.getD (i + 1) 0 ^^^ l.getD (i + t8) 0))

def reduce (l : VG.Proof.Rc2.KeyBytes) (bits : Nat) : VG.Proof.Rc2.KeyBytes :=
  let t8 := (bits + 7) / 8
  let tm := BitVec.ofNat 8 (255 % 2 ^ (8 + bits - 8 * t8))
  l.set! (128 - t8) (Spec.Rc2.pi (l.getD (128 - t8) 0 &&& tm))

def descend (l : VG.Proof.Rc2.KeyBytes) (t8 n : Nat) : VG.Proof.Rc2.KeyBytes :=
  (List.range n).foldl (fun l j => VG.Proof.Rc2.descendStep t8 j l) l

theorem fill_succ (key : List Byte) (n : Nat) :
    VG.Proof.Rc2.fill key (n + 1) = VG.Proof.Rc2.fillStep key.length n (VG.Proof.Rc2.fill key n) := by
  simp only [VG.Proof.Rc2.fill, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem descend_succ (l : VG.Proof.Rc2.KeyBytes) (t8 n : Nat) :
    VG.Proof.Rc2.descend l t8 (n + 1) = VG.Proof.Rc2.descendStep t8 n (VG.Proof.Rc2.descend l t8 n) := by
  simp only [VG.Proof.Rc2.descend, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem expandBytes_eq (key : List Byte) (bits : Nat) :
    Spec.Rc2.expandBytes key bits =
      VG.Proof.Rc2.descend (VG.Proof.Rc2.reduce (VG.Proof.Rc2.fill key (128 - key.length)) bits) ((bits + 7) / 8)
        (128 - (bits + 7) / 8) := by
  simp [Spec.Rc2.expandBytes, VG.Proof.Rc2.fill, VG.Proof.Rc2.fillStep, VG.Proof.Rc2.reduce, VG.Proof.Rc2.descend, VG.Proof.Rc2.descendStep,
    List.forIn_pure_yield_eq_foldl]

/-- Only the prefix below `n` has been initialized during copying and
forward expansion; the remaining bytes are unconstrained. -/
def BytesPrefix (m : Mem) (p : Addr) (l : VG.Proof.Rc2.KeyBytes) (n : Nat) : Prop :=
  ∀ i < n, m (p + BitVec.ofNat 64 i) = l.getD i 0

theorem getD_set (l : VG.Proof.Rc2.KeyBytes) (i j : Nat) (hj : j < 128) (b : Byte) :
    (l.set! i b).getD j 0 = if i = j then b else l.getD j 0 := by
  rw [VG.Proof.Rc2.getD_eq_getElem _ j hj, VG.Proof.Rc2.getD_eq_getElem _ j hj, Vector.getElem_set! hj]

theorem BytesPrefix.write {m : Mem} {p : Addr} {l : VG.Proof.Rc2.KeyBytes} {n i : Nat}
    (h : VG.Proof.Rc2.BytesPrefix m p l n) (hn : n ≤ 128) (hi : i < n) (b : Byte) :
    VG.Proof.Rc2.BytesPrefix (m.writeW (p + BitVec.ofNat 64 i) b) p (l.set! i b) n := by
  intro j hj
  rw [WriteBytes.writeW8_apply, VG.Proof.Rc2.getD_set l i j (by omega)]
  by_cases he : i = j
  · subst j; simp
  · have hne := Offset.add_ofNat_ne p (show j < 2 ^ 64 by omega) (show i < 2 ^ 64 by omega) (Ne.symm he)
    rw [ite_eq_right he, ite_eq_right hne, h j hj]

theorem BytesPrefix.extend {m : Mem} {p : Addr} {l : VG.Proof.Rc2.KeyBytes} {n : Nat}
    (h : VG.Proof.Rc2.BytesPrefix m p l n) (hn : n < 128) (b : Byte) :
    VG.Proof.Rc2.BytesPrefix (m.writeW (p + BitVec.ofNat 64 n) b) p (l.set! n b) (n + 1) := by
  intro j hj
  rw [WriteBytes.writeW8_apply, VG.Proof.Rc2.getD_set l n j (by omega)]
  by_cases he : n = j
  · subst j; simp
  · have hne := Offset.add_ofNat_ne p (show j < 2 ^ 64 by omega) (show n < 2 ^ 64 by omega) (Ne.symm he)
    rw [ite_eq_right he, ite_eq_right hne, h j (by omega)]

theorem scheduleAt_expanded {m : Mem} {p : Addr} {key : List Byte} {bits : Nat}
    (h : VG.Proof.Rc2.BytesPrefix m p (Spec.Rc2.expandBytes key bits) 128) :
    Spec.Rc2.scheduleAt m p = Spec.Rc2.expandKey key bits := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Rc2.scheduleAt, Spec.Rc2.expandKey, Vector.getElem_ofFn]
  rw [h (2 * i) (by omega), h (2 * i + 1) (by omega)]

theorem bytesAt_getD (m : Mem) (p : Addr) (n i : Nat) (hi : i < n) :
    (Spec.Rc2.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rc2.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_range hi]

theorem initial_set (key : List Byte) (i : Nat) :
    (VG.Proof.Rc2.fill key 0).set! i (key.getD i 0) = VG.Proof.Rc2.fill key 0 := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_set! hj]
  by_cases he : i = j
  · subst j; simp [VG.Proof.Rc2.fill]
  · rw [ite_eq_right he]

end VG.Proof.Rc2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Memory32`. -/
section

/-! # Byte-wise block output on 32-bit targets -/

namespace VG.Proof.Rc2.Word32

open VG VG.WriteBytes

def outputBytes (v : Spec.Rc2.State) (n : Nat) : List Byte :=
  (List.range (2 * n)).map fun i => (Spec.Rc2.encodeBlock v).getD i 0

theorem outputBytes_length (v : Spec.Rc2.State) (n : Nat) : (VG.Proof.Rc2.Word32.outputBytes v n).length = 2 * n := by
  simp [VG.Proof.Rc2.Word32.outputBytes]

theorem encode_lo (v : Spec.Rc2.State) (i : Nat) (hi : i < 4) :
    (Spec.Rc2.encodeBlock v).getD (2 * i) 0 = (v.getD i 0).setWidth 8 := by
  rw [Spec.Rc2.encodeBlock, VG.Proof.Rc2.getD_ofFn _ _ (by omega)]
  simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 2), Nat.mul_mod_right,
    Nat.mul_zero, BitVec.ushiftRight_zero]

theorem encode_hi (v : Spec.Rc2.State) (i : Nat) (hi : i < 4) :
    (Spec.Rc2.encodeBlock v).getD (2 * i + 1) 0 = ((v.getD i 0) >>> 8).setWidth 8 := by
  rw [Spec.Rc2.encodeBlock, VG.Proof.Rc2.getD_ofFn _ _ (by omega)]
  have hd : (2 * i + 1) / 2 = i := by omega
  have hm : (2 * i + 1) % 2 = 1 := by omega
  simp only [hd, hm, Nat.mul_one]

theorem outputBytes_succ (v : Spec.Rc2.State) (n : Nat) (hn : n < 4) :
    VG.Proof.Rc2.Word32.outputBytes v (n + 1) = VG.Proof.Rc2.Word32.outputBytes v n ++
      [(v.getD n 0).setWidth 8, ((v.getD n 0) >>> 8).setWidth 8] := by
  rw [VG.Proof.Rc2.Word32.outputBytes, show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
    List.range_succ, List.range_succ]
  simp only [List.map_append, List.map_cons, List.map_nil, VG.Proof.Rc2.Word32.encode_lo v n hn,
    VG.Proof.Rc2.Word32.encode_hi v n hn, List.append_assoc, List.cons_append, List.nil_append]
  rfl

theorem outputBytes_write (m : Mem) (p : Addr) (v : Spec.Rc2.State) (n : Nat) (hn : n < 4) :
    writeBytes m p (VG.Proof.Rc2.Word32.outputBytes v (n + 1)) =
      ((writeBytes m p (VG.Proof.Rc2.Word32.outputBytes v n)).writeW (p + BitVec.ofNat 64 (2 * n))
        ((v.getD n 0).setWidth 8)).writeW (p + BitVec.ofNat 64 (2 * n + 1))
          (((v.getD n 0) >>> 8).setWidth 8) := by
  rw [VG.Proof.Rc2.Word32.outputBytes_succ v n hn]
  rw [show VG.Proof.Rc2.Word32.outputBytes v n ++ [(v.getD n 0).setWidth 8, ((v.getD n 0) >>> 8).setWidth 8] =
    (VG.Proof.Rc2.Word32.outputBytes v n ++ [(v.getD n 0).setWidth 8]) ++ [((v.getD n 0) >>> 8).setWidth 8] by simp]
  rw [writeBytes_snoc _ _ _ _ (by simp only [List.length_append, List.length_singleton, VG.Proof.Rc2.Word32.outputBytes_length]; omega),
    writeBytes_snoc _ _ _ _ (by rw [VG.Proof.Rc2.Word32.outputBytes_length]; omega)]
  simp only [List.length_append, List.length_singleton, VG.Proof.Rc2.Word32.outputBytes_length]

theorem outputBytes_pack (m : Mem) (p : Addr) (v : Spec.Rc2.State) :
    writeBytes m p (VG.Proof.Rc2.Word32.outputBytes v 4) = m.writeW p (VG.Proof.Rc2.pack v) := by
  change _ = m.write p 8 (VG.Proof.Rc2.pack v)
  rw [write_eq_writeBytes]
  apply congrArg (writeBytes m p)
  apply List.map_congr_left
  intro i hi
  exact VG.Proof.Rc2.encode_pack v i (List.mem_range.mp hi)

end VG.Proof.Rc2.Word32

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.PairMem`. -/
section

/-! # RC2 block memory as pairs of 32-bit words -/

namespace VG.Proof.Rc2.Word32

open VG

theorem getLsbD_read (m : Mem) : ∀ (n : Nat) (a : Addr) (i : Nat), i < 8 * n →
    (m.read a n).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8)
  | 0, _, _, h => absurd h (by omega)
  | n + 1, a, i, h => by
    simp only [Mem.read, BitVec.getLsbD_append]
    by_cases hi : i < 8
    · simp [hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · simp only [hi, ite_false]
      rw [VG.Proof.Rc2.Word32.getLsbD_read m n (a + 1) (i - 8) (by omega)]
      have e1 : (i - 8) / 8 = i / 8 - 1 := by omega
      have e2 : (i - 8) % 8 = i % 8 := by omega
      rw [e1, e2]
      congr 2
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
      omega

theorem toNat_sub_c (d : BitVec 64) (c : Nat) (hc : c < 16) :
    (d - BitVec.ofNat 64 c).toNat = if c ≤ d.toNat then d.toNat - c else 2 ^ 64 + d.toNat - c := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := d.isLt
  split <;> omega

/-- The low word of a 64-bit load. -/
theorem readW64_lo (m : Mem) (a : Addr) : (m.readW a 64).extractLsb' 0 32 = m.readW a 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.zero_add, Mem.readW,
    BitVec.getLsbD_setWidth, show i < 64 by omega]
  rw [VG.Proof.Rc2.Word32.getLsbD_read m _ a i (by omega), VG.Proof.Rc2.Word32.getLsbD_read m _ a i (by omega)]

/-- The high word of a 64-bit load. -/
theorem readW64_hi (m : Mem) (a : Addr) :
    (m.readW a 64).extractLsb' 32 32 = m.readW (a + BitVec.ofNat 64 4) 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Mem.readW,
    BitVec.getLsbD_setWidth, show 32 + i < 64 by omega]
  rw [VG.Proof.Rc2.Word32.getLsbD_read m _ a (32 + i) (by omega), VG.Proof.Rc2.Word32.getLsbD_read m _ _ i (by omega), BitVec.add_assoc,
    ← BitVec.ofNat_add, show 4 + i / 8 = (32 + i) / 8 by omega, show i % 8 = (32 + i) % 8 by omega]

theorem read64_pair (m : Mem) (p : Addr) :
    m.readW p 64 = (m.readW (p + BitVec.ofNat 64 4) 32) ++ (m.readW p 32) := by
  rw [← VG.Proof.Rc2.Word32.readW64_hi, ← VG.Proof.Rc2.Word32.readW64_lo]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split
  · rename_i h
    simp only [h, decide_true, Bool.true_and, Nat.zero_add]
  · have h : i - 32 < 32 := by omega
    simp only [h, decide_true, Bool.true_and]
    exact congrArg _ (by omega)

theorem write64_pair (m : Mem) (p : Addr) (a b : BitVec 32) :
    m.writeW p (b ++ a) = (m.writeW p a).writeW (p + BitVec.ofNat 64 4) b := by
  funext x
  have e : x - (p + BitVec.ofNat 64 4) = (x - p) - BitVec.ofNat 64 4 := (BitVec.sub_sub _ _ _).symm
  simp only [Mem.writeW, Mem.write, e, show 32 / 8 = 4 from rfl, show (32 + 32) / 8 = 8 from rfl]
  generalize x - p = d
  rw [VG.Proof.Rc2.Word32.toNat_sub_c d 4 (by decide)]
  have := d.isLt
  by_cases h : d.toNat < 4
  · simp only [show ¬ 4 ≤ d.toNat by omega, ite_false, show ¬ 2 ^ 64 + d.toNat - 4 < 4 by omega,
      h, show d.toNat < 8 by omega, ite_true]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
      BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, show 8 * d.toNat + i < 32 by omega, ite_true,
      show 8 * d.toNat + i < 8 * ((32 + 32) / 8) by omega]
  · by_cases h16 : d.toNat < 8
    · simp only [show 4 ≤ d.toNat by omega, ite_true, h16, show d.toNat - 4 < 4 by omega]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
        BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
        show ¬ 8 * d.toNat + i < 32 by omega, ite_false,
        show 8 * (d.toNat - 4) + i < 32 by omega,
        show 8 * d.toNat + i < 8 * ((32 + 32) / 8) by omega,
        show 8 * d.toNat + i - 32 = 8 * (d.toNat - 4) + i by omega]
    · simp only [show 4 ≤ d.toNat by omega, ite_true, h16, show ¬ d.toNat - 4 < 4 by omega,
        h, ite_false]

theorem pair_xor (a b c d : BitVec 32) :
    ((b ^^^ d) ++ (a ^^^ c)) = (b ++ a) ^^^ (d ++ c) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_xor]
  split <;> rfl

end VG.Proof.Rc2.Word32

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Stream`. -/
section

/-!
# Streaming RC2-CBC: the contracts from memory facts

Target-independent lemmas that reduce the postconditions of `vg_rc2_cbc_init`
and the update functions (`Spec.Rc2.cbcInitContract`,
`Spec.Rc2.cbcUpdateContract`) to facts about the memory an implementation
leaves, for implementations that

* `init`: check the lengths in order, and on success copy the IV to
  `ctx + 128` and expand the key into `ctx` (`init_post`, `init_post_error`);
* `update`: if there is no complete block (`out_len = 0`), append the data to
  the pending bytes (`update_post_short`); otherwise copy the pending bytes
  and the first `out_len - pending_len` bytes of data to `out`, the rest of
  the data to `ctx + 136`, and run CBC on `out` in place, with the schedule
  at `ctx` and the chaining value at `ctx + 128` (`update_post_long`).
-/

namespace VG.Proof.Rc2

open VG

theorem getD_of_lt {α : Type} (l : List α) {i : Nat} (d : α) (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rc2.bytesAt m p n).length = n := by
  simp [Spec.Rc2.bytesAt]

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rc2.bytesAt m p (a + b) = Spec.Rc2.bytesAt m p a ++ Spec.Rc2.bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [Spec.Rc2.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Offset.add_add]

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    Spec.Rc2.bytesAt m p (i + 1) = Spec.Rc2.bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [Spec.Rc2.bytesAt, List.range_succ]

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (p : Addr) (n : Nat)
    (hn : n ≤ 2 ^ 64) (hd : ∀ r ∈ rs, (Region.mk p n).Disjoint r) :
    Spec.Rc2.bytesAt m' p n = Spec.Rc2.bytesAt m p n := by
  simp only [Spec.Rc2.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes hd hn (List.mem_range.mp hi)

/-- Bytes written with `writeBytes` read back. -/
theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    Spec.Rc2.bytesAt (WriteBytes.writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem
  · simp [Spec.Rc2.bytesAt]
  · intro i h₁ h₂
    simp only [Spec.Rc2.bytesAt, List.getElem_map, List.getElem_range, WriteBytes.writeBytes,
      Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), h₂, ite_true]
    rw [VG.Proof.Rc2.getD_of_lt _ _ h₂]

theorem bytesAt_eight (m : Mem) (p : Addr) :
    Spec.Rc2.bytesAt m p 8 = (Spec.Rc2.blockAt m p).toList := by
  apply List.ext_getElem
  · simp [Spec.Rc2.bytesAt]
  · intro i h₁ h₂
    simp only [Spec.Rc2.bytesAt, Spec.Rc2.blockAt, List.getElem_map, List.getElem_range,
      Vector.getElem_toList, Vector.getElem_ofFn]

theorem flatMap_blocksAt (m : Mem) (p : Addr) (n : Nat) :
    (Spec.Rc2.blocksAt m p n).flatMap Vector.toList = Spec.Rc2.bytesAt m p (8 * n) := by
  induction n generalizing p with
  | zero => simp [Spec.Rc2.blocksAt, Spec.Rc2.bytesAt]
  | succ n ih =>
    rw [VG.Proof.Rc2.blocksAt_cons, List.flatMap_cons, ih, show 8 * (n + 1) = 8 + 8 * n by omega, VG.Proof.Rc2.bytesAt_add,
      VG.Proof.Rc2.bytesAt_eight]
    rfl

theorem blocks_bytesAt (m : Mem) (p : Addr) (n : Nat) :
    Spec.Rc2.blocks (Spec.Rc2.bytesAt m p (8 * n)) = Spec.Rc2.blocksAt m p n := by
  simp only [Spec.Rc2.blocks, Spec.Rc2.blocksAt, VG.Proof.Rc2.bytesAt_length, Nat.mul_div_cancel_left _ (by decide : 0 < 8)]
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.mp hj
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, Spec.Rc2.blockAt, Spec.Rc2.bytesAt]
  rw [VG.Proof.Rc2.getD_of_lt _ _ (by simp; omega), List.getElem_map, List.getElem_range, Offset.add_add]

/-- Only whole blocks: the blocks of `xs` are those of its first `8 ⌊|xs| / 8⌋` bytes. -/
theorem blocks_take (xs : List Byte) :
    Spec.Rc2.blocks xs = Spec.Rc2.blocks (xs.take (8 * (xs.length / 8))) := by
  have hl : (xs.take (8 * (xs.length / 8))).length = 8 * (xs.length / 8) := by
    simp only [List.length_take]; omega
  simp only [Spec.Rc2.blocks, hl, Nat.mul_div_cancel_left _ (by decide : 0 < 8)]
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.mp hj
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn]
  rw [VG.Proof.Rc2.getD_of_lt _ _ (by omega), VG.Proof.Rc2.getD_of_lt _ _ (by omega), List.getElem_take]

/-! ## `update` -/

/-- With no complete block, the data is appended to the pending bytes, and
the schedule and chaining value are unchanged. -/
theorem update_post_short {m m' : Mem} {ctx data out : Addr} {d : Spec.Rc2.Direction} {p len : Nat}
    (hshort : p + len < 8)
    (hs : Spec.Rc2.scheduleAt m' ctx = Spec.Rc2.scheduleAt m ctx)
    (hiv : Spec.Rc2.blockAt m' (ctx + 128) = Spec.Rc2.blockAt m (ctx + 128))
    (hpend : Spec.Rc2.bytesAt m' (ctx + 136) (p + len) =
      Spec.Rc2.bytesAt m (ctx + 136) p ++ Spec.Rc2.bytesAt m data len) :
    let result := Spec.Rc2.update (Spec.Rc2.contextAt m ctx d p) (Spec.Rc2.bytesAt m data len)
    Spec.Rc2.contextAt m' ctx d ((p + len) % 8) = result.1 ∧
      Spec.Rc2.bytesAt m' out ((p + len) / 8 * 8) = result.2 := by
  have hlen : (Spec.Rc2.bytesAt m (ctx + 136) p ++ Spec.Rc2.bytesAt m data len).length / 8 = 0 := by
    simp only [List.length_append, VG.Proof.Rc2.bytesAt_length]; omega
  have hb : Spec.Rc2.blocks (Spec.Rc2.bytesAt m (ctx + 136) p ++ Spec.Rc2.bytesAt m data len) = [] := by
    simp only [Spec.Rc2.blocks, hlen, List.range_zero, List.map_nil]
  simp only [Spec.Rc2.update, Spec.Rc2.contextAt, hb, Spec.Rc2.cbc, hlen, Nat.mul_zero, List.drop_zero,
    List.flatMap_nil, Nat.mod_eq_of_lt hshort, Nat.div_eq_of_lt hshort, Nat.zero_mul, hs, hiv, hpend]
  simp [Spec.Rc2.bytesAt]

/-- With complete blocks, from the memory `m₁` after the copies (the pending
bytes and the first `out_len - p` bytes of data at `out`, the rest of the
data at `ctx + 136`) and the memory `m'` after CBC on `out`. -/
theorem update_post_long {m m₁ m' : Mem} {ctx data out : Addr} {d : Spec.Rc2.Direction} {p len : Nat}
    (hp : p < 8) (hlong : 8 ≤ p + len)
    (hout : Spec.Rc2.bytesAt m₁ out ((p + len) / 8 * 8) =
      Spec.Rc2.bytesAt m (ctx + 136) p ++ Spec.Rc2.bytesAt m data ((p + len) / 8 * 8 - p))
    (hs₁ : Spec.Rc2.scheduleAt m₁ ctx = Spec.Rc2.scheduleAt m ctx)
    (hiv₁ : Spec.Rc2.blockAt m₁ (ctx + 128) = Spec.Rc2.blockAt m (ctx + 128))
    (hpend : Spec.Rc2.bytesAt m' (ctx + 136) ((p + len) % 8) =
      Spec.Rc2.bytesAt m (data + BitVec.ofNat 64 ((p + len) / 8 * 8 - p)) ((p + len) % 8))
    (hs : Spec.Rc2.scheduleAt m' ctx = Spec.Rc2.scheduleAt m₁ ctx)
    (hc₁ : Spec.Rc2.blocksAt m' out ((p + len) / 8) = (Spec.Rc2.cbc (Spec.Rc2.scheduleAt m₁ ctx) d
      (Spec.Rc2.blockAt m₁ (ctx + 128)) (Spec.Rc2.blocksAt m₁ out ((p + len) / 8))).1)
    (hc₂ : Spec.Rc2.blockAt m' (ctx + 128) = (Spec.Rc2.cbc (Spec.Rc2.scheduleAt m₁ ctx) d
      (Spec.Rc2.blockAt m₁ (ctx + 128)) (Spec.Rc2.blocksAt m₁ out ((p + len) / 8))).2) :
    let result := Spec.Rc2.update (Spec.Rc2.contextAt m ctx d p) (Spec.Rc2.bytesAt m data len)
    Spec.Rc2.contextAt m' ctx d ((p + len) % 8) = result.1 ∧
      Spec.Rc2.bytesAt m' out ((p + len) / 8 * 8) = result.2 := by
  have hO : (p + len) / 8 * 8 = 8 * ((p + len) / 8) := Nat.mul_comm _ _
  have hk : (p + len) / 8 * 8 - p + (p + len) % 8 = len := by omega
  have hsplit : Spec.Rc2.bytesAt m data len = Spec.Rc2.bytesAt m data ((p + len) / 8 * 8 - p) ++
      Spec.Rc2.bytesAt m (data + BitVec.ofNat 64 ((p + len) / 8 * 8 - p)) ((p + len) % 8) := by
    rw [← VG.Proof.Rc2.bytesAt_add, hk]
  have hl : (Spec.Rc2.bytesAt m (ctx + 136) p ++ Spec.Rc2.bytesAt m data len).length = p + len := by
    simp [VG.Proof.Rc2.bytesAt_length]
  have htake : (Spec.Rc2.bytesAt m (ctx + 136) p ++ Spec.Rc2.bytesAt m data len).take
      (8 * ((p + len) / 8)) = Spec.Rc2.bytesAt m₁ out (8 * ((p + len) / 8)) := by
    rw [← hO, hout, hsplit, ← List.append_assoc, List.take_left' (by simp [VG.Proof.Rc2.bytesAt_length]; omega)]
  have hdrop : (Spec.Rc2.bytesAt m (ctx + 136) p ++ Spec.Rc2.bytesAt m data len).drop
      (8 * ((p + len) / 8)) = Spec.Rc2.bytesAt m' (ctx + 136) ((p + len) % 8) := by
    rw [hpend, hsplit, ← List.append_assoc, List.drop_left' (by simp [VG.Proof.Rc2.bytesAt_length]; omega)]
  have hblocks : Spec.Rc2.blocks (Spec.Rc2.bytesAt m (ctx + 136) p ++ Spec.Rc2.bytesAt m data len) =
      Spec.Rc2.blocksAt m₁ out ((p + len) / 8) := by
    rw [VG.Proof.Rc2.blocks_take, hl, htake, VG.Proof.Rc2.blocks_bytesAt]
  simp only [Spec.Rc2.update, Spec.Rc2.contextAt, hl, hblocks, hdrop, ← hs₁, ← hiv₁]
  refine ⟨?_, ?_⟩
  · rw [hs, ← hc₂]
  · rw [← hc₁, VG.Proof.Rc2.flatMap_blocksAt, hO]

/-! ## `init` -/

/-- The context `init` writes, from the schedule at `ctx` and the IV at
`ctx + 128`. -/
theorem init_post {m m' : Mem} {key iv ctx : Addr} {keyLen effectiveBits ivLen : Nat} {r : BitVec 32}
    (hk : 1 ≤ keyLen ∧ keyLen ≤ 128) (he : 1 ≤ effectiveBits ∧ effectiveBits ≤ 1024) (hi : ivLen = 8)
    (hr : r = 0)
    (hs : Spec.Rc2.scheduleAt m' ctx = Spec.Rc2.expandKey (Spec.Rc2.bytesAt m key keyLen) effectiveBits)
    (hiv : Spec.Rc2.blockAt m' (ctx + 128) = Spec.Rc2.blockAt m iv) :
    ∀ direction, match Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt m key keyLen)
        (Spec.Rc2.bytesAt m iv ivLen) direction effectiveBits with
      | .ok c => r = 0 ∧ Spec.Rc2.contextAt m' ctx direction 0 = c
      | .error e => r.toNat = e.code := by
  intro direction
  subst hi
  have hc : Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt m key keyLen) (Spec.Rc2.bytesAt m iv 8)
      direction effectiveBits = .ok (Spec.Rc2.Context.mk (Spec.Rc2.expandKey (Spec.Rc2.bytesAt m key keyLen)
        effectiveBits) direction (Vector.ofFn fun i => (Spec.Rc2.bytesAt m iv 8).getD i 0) []) := by
    simp only [Spec.Rc2.initWithEffectiveBits, VG.Proof.Rc2.bytesAt_length, ite_eq_left_of_eq_true _ _ (eq_true hk),
      ite_eq_left_of_eq_true _ _ (eq_true he)]
    rfl
  rw [hc]
  refine ⟨hr, ?_⟩
  simp only [Spec.Rc2.contextAt, hs, hiv, Spec.Rc2.Context.mk.injEq, true_and]
  refine ⟨?_, by simp [Spec.Rc2.bytesAt]⟩
  apply Vector.ext
  intro i hi
  simp only [Spec.Rc2.blockAt, Vector.getElem_ofFn, Spec.Rc2.bytesAt]
  rw [VG.Proof.Rc2.getD_of_lt _ _ (by simp; omega), List.getElem_map, List.getElem_range]

/-- The error `init` returns for invalid lengths, in order. -/
theorem init_post_error {m m' : Mem} {key iv ctx : Addr} {keyLen effectiveBits ivLen : Nat} {r : BitVec 32}
    (hr : r.toNat = if ¬(1 ≤ keyLen ∧ keyLen ≤ 128) then 1
      else if ¬(1 ≤ effectiveBits ∧ effectiveBits ≤ 1024) then 2 else 3)
    (hbad : ¬((1 ≤ keyLen ∧ keyLen ≤ 128) ∧ (1 ≤ effectiveBits ∧ effectiveBits ≤ 1024) ∧ ivLen = 8)) :
    ∀ direction, match Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt m key keyLen)
        (Spec.Rc2.bytesAt m iv ivLen) direction effectiveBits with
      | .ok c => r = 0 ∧ Spec.Rc2.contextAt m' ctx direction 0 = c
      | .error e => r.toNat = e.code := by
  intro direction
  by_cases hk : 1 ≤ keyLen ∧ keyLen ≤ 128
  · by_cases he : 1 ≤ effectiveBits ∧ effectiveBits ≤ 1024
    · have hi : ivLen ≠ 8 := fun h => hbad ⟨hk, he, h⟩
      have hc : Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt m key keyLen) (Spec.Rc2.bytesAt m iv ivLen)
          direction effectiveBits = .error .invalidIvLength := by
        simp only [Spec.Rc2.initWithEffectiveBits, VG.Proof.Rc2.bytesAt_length, ite_eq_left_of_eq_true _ _ (eq_true hk), ite_eq_left_of_eq_true _ _ (eq_true he), ite_eq_right_of_eq_false _ _ (eq_false hi)]
        rfl
      rw [hc]; simpa [hk, he, Spec.Rc2.Error.code] using hr
    · have hc : Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt m key keyLen) (Spec.Rc2.bytesAt m iv ivLen)
          direction effectiveBits = .error .invalidEffectiveBits := by
        simp only [Spec.Rc2.initWithEffectiveBits, VG.Proof.Rc2.bytesAt_length, ite_eq_left_of_eq_true _ _ (eq_true hk), ite_eq_right_of_eq_false _ _ (eq_false he)]
        rfl
      rw [hc]; simpa [hk, he, Spec.Rc2.Error.code] using hr
  · have hc : Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt m key keyLen) (Spec.Rc2.bytesAt m iv ivLen)
        direction effectiveBits = .error .invalidKeyLength := by
      simp only [Spec.Rc2.initWithEffectiveBits, VG.Proof.Rc2.bytesAt_length, ite_eq_right_of_eq_false _ _ (eq_false hk)]
      rfl
    rw [hc]; simpa [hk, Spec.Rc2.Error.code] using hr

end VG.Proof.Rc2

end
