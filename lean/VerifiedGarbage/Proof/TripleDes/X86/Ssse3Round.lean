module

public import VerifiedGarbage.Impl.TripleDes.X86.Ssse3
meta import VerifiedGarbage.Impl.TripleDes.X86.Ssse3
public import VerifiedGarbage.Spec.TripleDes
meta import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.Proof.TripleDes.Core
meta import VerifiedGarbage.Proof.TripleDes.Core
public import VerifiedGarbage.Proof.TripleDes.Pieces
meta import VerifiedGarbage.Proof.TripleDes.Pieces
import VerifiedGarbage.Proof.TripleDes.Permutation
meta import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.TripleDes.Round
meta import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.TripleDes.Word
meta import VerifiedGarbage.Proof.TripleDes.Word
public import VerifiedGarbage.TCB.X86.Sse
meta import VerifiedGarbage.TCB.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.ByteMap
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseLanes
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# Triple DES with its S-boxes by `pshufb`: what the words computed are

The arithmetic of `Impl/TripleDes/X86/Ssse3.lean`, apart from the machine:

* `Lin`: a function of bit vectors that respects exclusive-or is known from
  its values on the single bits (`Lin.ext`), so two such functions are
  compared by the kernel on those;
* `ipS`, `fpS`: the five exchanges of bits of the block's two words that the
  code makes before and after the rounds are the initial and the final
  permutation (`ipS_eq`, `fpS_eq`);
* the table's constants (`cst`) and what a byte of the four look-ups of an
  S-box is (`luB`): for each S-box and each of its 64 inputs, the bytes
  under their masks, folded and moved by the six shifts (`pOut`), are the
  S-box's output through the permutation P, rotated right by one (`sp_all`,
  512 checks by the kernel), so a word of such bytes is the round function,
  rotated (`pOut_round`, by `roundFunction_sum`: the round function is the
  sum of its S-boxes' parts);
* the keys' words as `prepare` writes them (`kw0`, `kw1`) and the index
  bytes: those of the half shifted right by two and rotated left by two,
  with the key's words, are the S-boxes' inputs after the expansion E
  (`idx_lo`, `idx_hi`);
* a round in the registers (`roundX`: the index, the look-ups `lkX` at the
  index stepped by 16, their sums `accX`, the fold and P, `pX`), a
  doubleword and a byte at a time, and `round_ok`: its low doubleword is
  the other half with the round function of this one, both rotated right by
  one.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86.Ssse3

open VG VG.Spec.TripleDes VG.Proof.TripleDes

/-! ## Functions that respect exclusive-or -/

/-- `f` respects exclusive-or. -/
def Lin {n m : Nat} (f : BitVec n → BitVec m) : Prop := ∀ a b, f (a ^^^ b) = f a ^^^ f b

theorem Lin.zero {n m : Nat} {f : BitVec n → BitVec m} (h : Lin f) : f 0 = 0 := by
  have := h 0 0
  rwa [BitVec.xor_self, BitVec.xor_self] at this

theorem Lin.comp {n m k : Nat} {g : BitVec m → BitVec k} {f : BitVec n → BitVec m} (hg : Lin g) (hf : Lin f) :
    Lin fun x => g (f x) := fun a b => by
  show g (f (a ^^^ b)) = g (f a) ^^^ g (f b)
  rw [hf, hg]

/-- Two functions that respect exclusive-or and agree on every single bit
are the same. -/
theorem Lin.ext {n m : Nat} {f g : BitVec n → BitVec m} (hf : Lin f) (hg : Lin g)
    (h : ∀ j < n, f (BitVec.twoPow n j) = g (BitVec.twoPow n j)) (x : BitVec n) : f x = g x := by
  suffices H : ∀ k, k ≤ n → ∀ x : BitVec n, (∀ j, k ≤ j → x.getLsbD j = false) → f x = g x from
    H n (Nat.le_refl n) x fun j hj => BitVec.getLsbD_of_ge x j hj
  intro k
  induction k with
  | zero =>
    intro _ x hx
    obtain rfl : x = 0 := BitVec.eq_of_getLsbD_eq fun j _ => by rw [hx j (Nat.zero_le j)]; simp
    rw [hf.zero, hg.zero]
  | succ k ih =>
    intro hk x hx
    by_cases hb : x.getLsbD k = true
    · have e : x = (x ^^^ BitVec.twoPow n k) ^^^ BitVec.twoPow n k := by
        rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
      rw [e, hf, hg, h k (by omega_arith)]
      congr 1
      refine ih (by omega_arith) _ fun j hj => ?_
      rw [BitVec.getLsbD_xor, BitVec.getLsbD_twoPow]
      by_cases hjk : k = j
      · subst hjk; simp [hb, show k < n by omega_arith]
      · rw [hx j (by omega_arith)]; simp [hjk]
    · exact ih (by omega_arith) x fun j hj => by
        by_cases hjk : k = j
        · subst hjk; simpa using hb
        · exact hx j (by omega_arith)

theorem lin_permute {n m : Nat} (positions : Vector Nat m) (hn : 0 < n) :
    Lin (permute (n := n) positions) := fun a b => by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_xor, permute_bit _ _ hn j hj, permute_bit _ _ hn j hj, permute_bit _ _ hn j hj,
    BitVec.getLsbD_xor]

/-! ## The exchanges of bits -/

/-- The high and the low word. -/
abbrev hi (x : BitVec 64) : BitVec 32 := (x >>> 32).setWidth 32
abbrev lo (x : BitVec 64) : BitVec 32 := x.setWidth 32

/-- `t = ((a >> n) ^ b) & m`: the bits of `b` under `m` that differ from
those of `a`, `n` higher. -/
def swT (a b : BitVec 32) (n : Nat) (m : BitVec 32) : BitVec 32 := ((a >>> n) ^^^ b) &&& m
/-- `a` and `b` with those bits exchanged (`Impl`'s `swap`). -/
def swA (a b : BitVec 32) (n : Nat) (m : BitVec 32) : BitVec 32 := a ^^^ (swT a b n m).rotateRight (32 - n)
def swB (a b : BitVec 32) (n : Nat) (m : BitVec 32) : BitVec 32 := b ^^^ swT a b n m

theorem rotateRight_xor (a b : BitVec 32) (r : Nat) :
    (a ^^^ b).rotateRight r = a.rotateRight r ^^^ b.rotateRight r := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_xor]
  by_cases h : j < 32 - r % 32 <;> simp [h, hj]

theorem swT_xor (a a' b b' : BitVec 32) (n : Nat) (m : BitVec 32) :
    swT (a ^^^ a') (b ^^^ b') n m = swT a b n m ^^^ swT a' b' n m := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [swT, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight]
  cases m.getLsbD j
  · simp only [Bool.and_false, Bool.xor_false]
  · simp only [Bool.and_true]
    cases a.getLsbD (n + j) <;> cases a'.getLsbD (n + j) <;> cases b.getLsbD j <;> cases b'.getLsbD j <;> rfl

theorem swA_xor (a a' b b' : BitVec 32) (n : Nat) (m : BitVec 32) :
    swA (a ^^^ a') (b ^^^ b') n m = swA a b n m ^^^ swA a' b' n m := by
  simp only [swA, swT_xor, rotateRight_xor]; ac_rfl

theorem swB_xor (a a' b b' : BitVec 32) (n : Nat) (m : BitVec 32) :
    swB (a ^^^ a') (b ^^^ b') n m = swB a b n m ^^^ swB a' b' n m := by
  simp only [swB, swT_xor]; ac_rfl

/-- An exchange between the high word (`a`) and the low word (`b`), and
between the low word (`a`) and the high word (`b`). -/
def stepL (n : Nat) (m : BitVec 32) (x : BitVec 64) : BitVec 64 := swA (hi x) (lo x) n m ++ swB (hi x) (lo x) n m
def stepR (n : Nat) (m : BitVec 32) (x : BitVec 64) : BitVec 64 := swB (lo x) (hi x) n m ++ swA (lo x) (hi x) n m

theorem hi_xor (x y : BitVec 64) : hi (x ^^^ y) = hi x ^^^ hi y := by
  simp only [hi, BitVec.ushiftRight_xor_distrib, BitVec.setWidth_xor]

theorem lo_xor (x y : BitVec 64) : lo (x ^^^ y) = lo x ^^^ lo y := BitVec.setWidth_xor

theorem lin_stepL (n : Nat) (m : BitVec 32) : Lin (stepL n m) := fun x y => by
  simp only [stepL, hi_xor, lo_xor, swA_xor, swB_xor]
  exact BitVec.xor_append.symm

theorem lin_stepR (n : Nat) (m : BitVec 32) : Lin (stepR n m) := fun x y => by
  simp only [stepR, hi_xor, lo_xor, swA_xor, swB_xor]
  exact BitVec.xor_append.symm

/-- The five exchanges before the rounds, and those after them. -/
def ipS (x : BitVec 64) : BitVec 64 :=
  stepL 1 0x55555555 (stepR 8 0x00ff00ff (stepR 2 0x33333333 (stepL 16 0x0000ffff (stepL 4 0x0f0f0f0f x))))
def fpS (x : BitVec 64) : BitVec 64 :=
  stepL 4 0x0f0f0f0f (stepL 16 0x0000ffff (stepR 2 0x33333333 (stepR 8 0x00ff00ff (stepL 1 0x55555555 x))))

theorem lin_ipS : Lin ipS :=
  (lin_stepL _ _).comp ((lin_stepR _ _).comp ((lin_stepR _ _).comp ((lin_stepL _ _).comp (lin_stepL _ _))))

theorem lin_fpS : Lin fpS :=
  (lin_stepL _ _).comp ((lin_stepL _ _).comp ((lin_stepR _ _).comp ((lin_stepR _ _).comp (lin_stepL _ _))))

theorem ipS_bits : ((List.range 64).all fun j => ipS (BitVec.twoPow 64 j) == permute ip (BitVec.twoPow 64 j)) = true := by
  lit_decide

theorem fpS_bits : ((List.range 64).all fun j => fpS (BitVec.twoPow 64 j) == permute fp (BitVec.twoPow 64 j)) = true := by
  lit_decide

/-- The exchanges before the rounds are the initial permutation. -/
theorem ipS_eq (x : BitVec 64) : ipS x = permute ip x :=
  Lin.ext lin_ipS (lin_permute ip (by decide)) (fun j hj => by
    simpa using List.all_eq_true.mp ipS_bits j (List.mem_range.mpr hj)) x

/-- The exchanges after the rounds are the final permutation. -/
theorem fpS_eq (x : BitVec 64) : fpS x = permute fp x :=
  Lin.ext lin_fpS (lin_permute fp (by decide)) (fun j hj => by
    simpa using List.all_eq_true.mp fpS_bits j (List.mem_range.mpr hj)) x

/-! ## The table's constants, and what a byte of the look-ups is -/

open VG.X86 (byte dword qword ofDwords XBinOp XShiftOp shufDwords)
open VG.Impl.TripleDes.X86.Ssse3 (table oM oStep oT oMask oP)

/-- The constant at the byte offset `off` of the table (what a table load
there gives). -/
def cst (off : Nat) : BitVec 128 := table.getD (off / 8 + 1) 0 ++ table.getD (off / 8) 0

/-- A look-up as `pshufb` makes it of one byte: zero if the index's high bit
is set, else the table's byte at the index's low four bits. -/
def lkb (t : BitVec 128) (b : BitVec 8) : BitVec 8 :=
  if b.msb then 0#8 else byte t (b.extractLsb' 0 4).toNat

/-- The exclusive-or of the pair `p`'s four look-ups from the index byte
`b`, and the index one, two and three steps on. -/
def pairB (p : Nat) (b : BitVec 8) : BitVec 8 :=
  lkb (cst (oT p 0)) b ^^^ lkb (cst (oT p 1)) (b + 16#8) ^^^ lkb (cst (oT p 2)) (b + 32#8) ^^^ lkb (cst (oT p 3)) (b + 48#8)

/-- Byte `i` of the sum of the four pairs under their masks. -/
def luB (i : Nat) (b : BitVec 8) : BitVec 8 :=
  (pairB 0 b &&& byte (cst (oMask 0)) i) ^^^ (pairB 1 b &&& byte (cst (oMask 1)) i) ^^^
    (pairB 2 b &&& byte (cst (oMask 2)) i) ^^^ (pairB 3 b &&& byte (cst (oMask 3)) i)

/-- The mask of P's rotation `i`. -/
def pM (i : Nat) : BitVec 32 := dword (cst (oP i)) 0

/-- P, of the word of the S-boxes' outputs as the look-ups place them: six
rotations under masks. -/
def pOut (w : BitVec 32) : BitVec 32 :=
  (w.rotateRight 7 &&& pM 0) ^^^ (w.rotateRight 15 &&& pM 1) ^^^ (w.rotateRight 16 &&& pM 2) ^^^
    (w.rotateRight 23 &&& pM 3) ^^^ (w.rotateRight 27 &&& pM 4) ^^^ (w.rotateRight 30 &&& pM 5)

/-- The S-box whose six input bits are byte `i` of the index. -/
def bx (i : Nat) : Nat := if i < 4 then 6 - 2 * i else 7 - 2 * (i - 4)

/-- S-box `b`'s part of the round function, of its six input bits. -/
def spS (b : Nat) (c : BitVec 6) : BitVec 32 := permute p ((sBox b c).zeroExtend 32 <<< (4 * (7 - b)))

/-- The look-ups, the masks and P give each S-box's part of the round
function, rotated right by one, from its six input bits with `0x40`. -/
theorem sp_all : ((List.range 8).all fun i => (List.range 64).all fun c =>
    pOut ((luB i (0x40#8 ||| BitVec.ofNat 8 c)).zeroExtend 32 <<< (8 * (i % 4))) ==
      (spS (bx i) (BitVec.ofNat 6 c)).rotateRight 1) = true := by
  lit_decide

/-- The masks of the pairs are zero in the high eight bytes. -/
theorem mask_hi : ((List.range 4).all fun q => (List.range 8).all fun i => byte (cst (oMask q)) (8 + i) == 0#8) = true := by
  lit_decide

/-! ## The round function as the sum of its S-boxes' parts -/

theorem p_bounds : ∀ j < 32, 1 ≤ p.getD j 1 ∧ p.getD j 1 ≤ 32 := by decide

theorem spS_bit {b : Nat} (hb : b < 8) (c : BitVec 6) {j : Nat} (hj : j < 32) :
    (spS b c).getLsbD j =
      (decide ((32 - p.getD (31 - j) 1) / 4 = 7 - b) && (sBox b c).getLsbD ((32 - p.getD (31 - j) 1) % 4)) := by
  obtain ⟨lo, hi⟩ := p_bounds (31 - j) (by omega_arith)
  rw [spS, permute_bit _ _ (by decide) j hj]
  generalize p.getD (32 - 1 - j) 1 = q at lo hi ⊢
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, show 32 - q < 32 by omega_arith, decide_true,
    Bool.true_and]
  by_cases h : (32 - q) / 4 = 7 - b
  · rw [show (32 - q) - 4 * (7 - b) = (32 - q) % 4 by omega_arith]
    simp [h, show ¬ (32 - q < 4 * (7 - b)) by omega_arith, show (32 - q) % 4 < 32 by omega_arith]
  · simp only [h, decide_false, Bool.false_and]
    by_cases h' : 32 - q < 4 * (7 - b)
    · simp [h']
    · rw [BitVec.getLsbD_of_ge (sBox b c) _ (by omega_arith)]; simp

/-- The round function is the exclusive-or of its eight S-boxes' parts. -/
theorem roundFunction_sum (r : BitVec 32) (k : BitVec 48) :
    roundFunction r k =
      spS 0 (roundChunk 0 r k) ^^^ spS 1 (roundChunk 1 r k) ^^^ spS 2 (roundChunk 2 r k) ^^^
        spS 3 (roundChunk 3 r k) ^^^ spS 4 (roundChunk 4 r k) ^^^ spS 5 (roundChunk 5 r k) ^^^
        spS 6 (roundChunk 6 r k) ^^^ spS 7 (roundChunk 7 r k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨lo, hi⟩ := p_bounds (31 - j) (by omega_arith)
  rw [roundFunction_bit r k j hj]
  simp only [BitVec.getLsbD_xor, spS_bit (show 0 < 8 by decide) _ hj, spS_bit (show 1 < 8 by decide) _ hj,
    spS_bit (show 2 < 8 by decide) _ hj, spS_bit (show 3 < 8 by decide) _ hj, spS_bit (show 4 < 8 by decide) _ hj,
    spS_bit (show 5 < 8 by decide) _ hj, spS_bit (show 6 < 8 by decide) _ hj, spS_bit (show 7 < 8 by decide) _ hj,
    roundChunk]
  generalize p.getD (31 - j) 1 = q at lo hi ⊢
  have hq : (32 - q) / 4 < 8 := by omega_arith
  generalize (32 - q) % 4 = t
  generalize hu : (32 - q) / 4 = u at hq ⊢
  match u, hq with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp
  | _ + 8, h => exact absurd h (by omega_arith)

/-! ## The word of the S-boxes' outputs, from its bytes -/

theorem and_xor32 (a b m : BitVec 32) : (a ^^^ b) &&& m = (a &&& m) ^^^ (b &&& m) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases m.getLsbD j <;> simp

theorem pOut_xor (a b : BitVec 32) : pOut (a ^^^ b) = pOut a ^^^ pOut b := by
  simp only [pOut, rotateRight_xor, and_xor32]; ac_rfl

/-- The byte `b` as byte `j` of a word. -/
def place (j : Nat) (b : BitVec 8) : BitVec 32 := b.zeroExtend 32 <<< (8 * j)

/-- A word is its four bytes, each in its place. -/
theorem word_bytes (d : BitVec 32) :
    d = place 0 (d.extractLsb' 0 8) ^^^ place 1 (d.extractLsb' 8 8) ^^^ place 2 (d.extractLsb' 16 8) ^^^
      place 3 (d.extractLsb' 24 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [place, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  by_cases h1 : j < 8
  · simp [h1, hj, show j < 16 by omega_arith, show j < 24 by omega_arith]
  · by_cases h2 : j < 16
    · simp [h1, h2, show j < 24 by omega_arith, show j - 8 < 8 by omega_arith, show j - 8 < 32 by omega_arith,
        show 8 + (j - 8) = j by omega_arith]
    · by_cases h3 : j < 24
      · simp [h1, h2, h3, show j - 16 < 8 by omega_arith, show j - 16 < 32 by omega_arith,
          show ¬ j - 8 < 8 by omega_arith, show 16 + (j - 16) = j by omega_arith]
      · simp [h1, h2, h3, show j - 24 < 8 by omega_arith, show j - 24 < 32 by omega_arith,
          show ¬ j - 8 < 8 by omega_arith, show ¬ j - 16 < 8 by omega_arith, show 24 + (j - 24) = j by omega_arith]

/-- The index byte of the S-box at byte `i`: its six input bits, with `0x40`. -/
def wb (r : BitVec 32) (k : BitVec 48) (i : Nat) : BitVec 8 := 0x40#8 ||| (roundChunk (bx i) r k).zeroExtend 8

theorem sp_byte {i : Nat} (hi : i < 8) (r : BitVec 32) (k : BitVec 48) :
    pOut (place (i % 4) (luB i (wb r k i))) = (spS (bx i) (roundChunk (bx i) r k)).rotateRight 1 := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp sp_all i (List.mem_range.mpr hi))
    (roundChunk (bx i) r k).toNat (List.mem_range.mpr (roundChunk (bx i) r k).isLt)
  simp only [beq_iff_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  exact h

/-- P of the two words of the S-boxes' outputs is the round function,
rotated right by one, when their bytes are the look-ups of the S-boxes'
inputs. -/
theorem pOut_round (d0 d1 : BitVec 32) (r : BitVec 32) (k : BitVec 48)
    (h0 : ∀ i < 4, d0.extractLsb' (8 * i) 8 = luB i (wb r k i))
    (h1 : ∀ i < 4, d1.extractLsb' (8 * i) 8 = luB (4 + i) (wb r k (4 + i))) :
    pOut (d0 ^^^ d1) = (roundFunction r k).rotateRight 1 := by
  rw [word_bytes d0, word_bytes d1]
  have a0 := h0 0 (by decide); have a1 := h0 1 (by decide); have a2 := h0 2 (by decide); have a3 := h0 3 (by decide)
  have b0 := h1 0 (by decide); have b1 := h1 1 (by decide); have b2 := h1 2 (by decide); have b3 := h1 3 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul, Nat.add_zero, Nat.reduceAdd] at a0 a1 a2 a3 b0 b1 b2 b3
  rw [a0, a1, a2, a3, b0, b1, b2, b3]
  simp only [pOut_xor]
  rw [sp_byte (i := 0) (by decide), sp_byte (i := 1) (by decide), sp_byte (i := 2) (by decide),
    sp_byte (i := 3) (by decide), sp_byte (i := 4) (by decide), sp_byte (i := 5) (by decide),
    sp_byte (i := 6) (by decide), sp_byte (i := 7) (by decide), roundFunction_sum]
  simp only [rotateRight_xor, bx, Nat.reduceLT, ↓reduceIte, Nat.reduceMul, Nat.reduceSub, Nat.lt_irrefl]
  ac_rfl

/-! ## The index bytes: the expansion and the key -/

/-- The two words of a round's keys that `prepare` makes of a round key as
the schedule has it (`Impl`'s `key`): the six bits of the S-boxes 6, 4, 2, 0
and of 7, 5, 3, 1 in their bytes, each with `0x40`. -/
def kw0 (s : BitVec 64) : BitVec 32 :=
  ((s.setWidth 32 >>> 6) &&& 0x3f#32) ||| ((s.setWidth 32 >>> 10) &&& 0x3f00#32) |||
    ((s.setWidth 32 >>> 14) &&& 0x30000#32) ||| (((s >>> 32).setWidth 32).rotateRight 14 &&& 0x3c0000#32) |||
    (((s >>> 32).setWidth 32).rotateRight 18 &&& 0x3f000000#32) ||| 0x40404040#32
def kw1 (s : BitVec 64) : BitVec 32 :=
  ((s.setWidth 32 >>> 4) &&& 0x3f00#32) ||| (s.setWidth 32 &&& 0x3f#32) ||| ((s.setWidth 32 >>> 8) &&& 0x3f0000#32) |||
    (((s >>> 32).setWidth 32).rotateRight 12 &&& 0x3f000000#32) ||| 0x40404040#32

theorem e_positions : ∀ b < 8, ∀ j < 6, 32 - expansion.getD (6 * b + 5 - j) 1 = (59 - 4 * b + j) % 32 := by decide

/-- A bit of an S-box's input, of the half and of the round key. -/
theorem chunk_bit {b j : Nat} (hb : b < 8) (hj : j < 6) (r : BitVec 32) (s : BitVec 64) :
    (roundChunk b r (s.setWidth 48)).getLsbD j = (r.getLsbD ((59 - 4 * b + j) % 32) ^^ s.getLsbD (42 - 6 * b + j)) := by
  have ht : 6 * (7 - b) + j < 48 := by omega_arith
  simp only [roundChunk, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_xor]
  rw [permute_bit _ _ (by decide) _ ht, show 48 - 1 - (6 * (7 - b) + j) = 6 * b + 5 - j by omega_arith,
    e_positions b hb j hj, show 6 * (7 - b) + j = 42 - 6 * b + j by omega_arith]
  simp [show 42 - 6 * b + j < 48 by omega_arith]

theorem chunk_elem {b j : Nat} (hb : b < 8) (hj : j < 6) (r : BitVec 32) (s : BitVec 64) :
    (roundChunk b r (s.setWidth 48))[j] = (r.getLsbD ((59 - 4 * b + j) % 32) ^^ s.getLsbD (42 - 6 * b + j)) := by
  rw [← BitVec.getLsbD_eq_getElem]; exact chunk_bit hb hj r s

/-- The low word of the index: the half (rotated right by one) shifted
right by two under the mask, and the first word of the keys. -/
theorem idx_lo (r : BitVec 32) (s : BitVec 64) {i : Nat} (hi : i < 4) :
    (((r.rotateRight 1 >>> 2) &&& 0x3f3f3f3f#32) ^^^ kw0 s).extractLsb' (8 * i) 8 = wb r (s.setWidth 48) i := by
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega_arith
  all_goals
    apply BitVec.eq_of_getLsbD_eq
    intro t ht
    match t, ht with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
      simp [wb, bx, kw0, chunk_elem]
    | _ + 8, h => exact absurd h (by omega_arith)

/-- The second word: the half rotated left by two, and the second word of
the keys. -/
theorem idx_hi (r : BitVec 32) (s : BitVec 64) {i : Nat} (hi : i < 4) :
    ((((r.rotateRight 1).rotateLeft 2) &&& 0x3f3f3f3f#32) ^^^ kw1 s).extractLsb' (8 * i) 8 =
      wb r (s.setWidth 48) (4 + i) := by
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega_arith
  all_goals
    apply BitVec.eq_of_getLsbD_eq
    intro t ht
    match t, ht with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
      simp [wb, bx, kw1, chunk_elem]
    | _ + 8, h => exact absurd h (by omega_arith)

/-! ## A round in the registers -/

open VG.X86.ByteMap (byte_xor byte_and byte_pshufb byte_eq_dword)

/-- The index register after the expansion of the half in `X`'s low
doubleword and the key `K`. -/
def idxX (X K : BitVec 128) : BitVec 128 :=
  (XBinOp.eval .punpckldq (XShiftOp.eval .psrld X (BitVec.ofNat 8 2))
      (XShiftOp.eval .psrlq (shufDwords X 0) (BitVec.ofNat 8 30)) &&& cst oM) ^^^ K

/-- The look-up of the pair `p`'s table for the index `s` steps on. -/
def lkX (q s : Nat) (W : BitVec 128) : BitVec 128 := XBinOp.eval .pshufb (cst (oT q s)) W

/-- The index a step on, with the step `c`. -/
abbrev stepC (c W : BitVec 128) : BitVec 128 := XBinOp.eval .paddd W c

/-- The exclusive-or of the pair `q`'s four look-ups, as `round` forms it
for the first two pairs and for the last two. -/
def yA (q : Nat) (c W : BitVec 128) : BitVec 128 :=
  lkX q 3 (stepC c (stepC c (stepC c W))) ^^^ ((lkX q 1 (stepC c W) ^^^ lkX q 0 W) ^^^ lkX q 2 (stepC c (stepC c W)))
def yB (q : Nat) (c W : BitVec 128) : BitVec 128 :=
  (lkX q 2 (stepC c (stepC c W)) ^^^ (lkX q 1 (stepC c W) ^^^ lkX q 0 W)) ^^^ lkX q 3 (stepC c (stepC c (stepC c W)))

/-- The sum of the four pairs' look-ups under their masks, as `round`
forms it. -/
def accX (W : BitVec 128) : BitVec 128 :=
  ((yA 0 (cst oStep) W &&& cst (oMask 0)) ^^^ (yA 1 (cst oStep) W &&& cst (oMask 1))) ^^^
    ((yB 2 (cst oStep) W &&& cst (oMask 2)) ^^^ (yB 3 (cst oStep) W &&& cst (oMask 3)))

/-- P's term of the rotation by `n` under the mask `i`. -/
def termX (A : BitVec 128) (i n : Nat) : BitVec 128 :=
  XShiftOp.eval .psrlq (shufDwords A 0xe1 ^^^ A) (BitVec.ofNat 8 n) &&& cst (oP i)

/-- The target `T` with P of the sum `A`, as `round` forms it. -/
def pX (A T : BitVec 128) : BitVec 128 :=
  (T ^^^ (termX A 4 27 ^^^ termX A 5 30)) ^^^ ((termX A 0 7 ^^^ termX A 1 15) ^^^ (termX A 2 16 ^^^ termX A 3 23))

/-- What a round leaves in `xmm7`. -/
def roundX (X K T : BitVec 128) : BitVec 128 := pX (accX (idxX X K)) T

theorem step_dwords : dword (cst oStep) 0 = 0x10101010#32 ∧ dword (cst oStep) 1 = 0x10101010#32 ∧
    dword (cst oStep) 2 = 0#32 ∧ dword (cst oStep) 3 = 0#32 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> lit_decide

theorem m_dwords : dword (cst oM) 0 = 0x3f3f3f3f#32 ∧ dword (cst oM) 1 = 0x3f3f3f3f#32 ∧
    dword (cst oM) 2 = 0#32 ∧ dword (cst oM) 3 = 0#32 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> lit_decide

theorem ext_toNat (x : BitVec 32) (n : Nat) : (x.extractLsb' n 8).toNat = x.toNat / 2 ^ n % 2 ^ 8 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- Adding 16 to every byte of a word whose bytes are below 240. -/
theorem add16 (d : BitVec 32) (h : ∀ j < 4, (d.extractLsb' (8 * j) 8).toNat < 240) {j : Nat} (hj : j < 4) :
    (d + 0x10101010#32).extractLsb' (8 * j) 8 = d.extractLsb' (8 * j) 8 + 16#8 := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide); have h3 := h 3 (by decide)
  rw [ext_toNat] at h0 h1 h2 h3
  apply BitVec.eq_of_toNat_eq
  rw [ext_toNat, BitVec.toNat_add, BitVec.toNat_add, ext_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega_arith
  all_goals omega

/-- A step of the index adds 16 to each of its low eight bytes, while they
are below 240, and keeps the others. -/
theorem byte_step (W : BitVec 128) (h : ∀ i < 8, (byte W i).toNat < 240) :
    (∀ i < 8, byte (stepC (cst oStep) W) i = byte W i + 16#8) ∧ ∀ i, 8 ≤ i → i < 16 → byte (stepC (cst oStep) W) i = byte W i := by
  obtain ⟨s0, s1, s2, s3⟩ := step_dwords
  refine ⟨fun i hi => ?_, fun i h8 hi => ?_⟩
  · rw [byte_eq_dword, VG.X86.dword_paddd _ _ (show i / 4 < 4 by omega_arith), byte_eq_dword W]
    obtain e | e : i / 4 = 0 ∨ i / 4 = 1 := by omega_arith
    · rw [e, s0]
      refine add16 _ (fun j hj => ?_) (by omega_arith)
      have := h j (by omega_arith)
      rwa [byte_eq_dword, show j / 4 = 0 by omega_arith, show j % 4 = j by omega_arith] at this
    · rw [e, s1]
      refine add16 _ (fun j hj => ?_) (by omega_arith)
      have := h (4 + j) (by omega_arith)
      rwa [byte_eq_dword, show (4 + j) / 4 = 1 by omega_arith, show (4 + j) % 4 = j by omega_arith] at this
  · rw [byte_eq_dword, VG.X86.dword_paddd _ _ (show i / 4 < 4 by omega_arith), byte_eq_dword W]
    obtain e | e : i / 4 = 2 ∨ i / 4 = 3 := by omega_arith
    · rw [e, s2, BitVec.add_zero]
    · rw [e, s3, BitVec.add_zero]

theorem byte_lkX (q s : Nat) (W : BitVec 128) {i : Nat} (hi : i < 16) : byte (lkX q s W) i = lkb (cst (oT q s)) (byte W i) :=
  byte_pshufb _ _ hi

/-- The sum's low eight bytes are the look-ups of the index bytes, while
those are below 128, and its high eight are zero. -/
theorem byte_accX (W : BitVec 128) (h : ∀ i < 8, (byte W i).toNat < 128) :
    (∀ i < 8, byte (accX W) i = luB i (byte W i)) ∧ ∀ i, 8 ≤ i → i < 16 → byte (accX W) i = 0#8 := by
  obtain ⟨a1, -⟩ := byte_step W fun i hi => by have := h i hi; omega_arith
  obtain ⟨a2, -⟩ := byte_step (stepC (cst oStep) W) fun i hi => by
    rw [a1 i hi]; have := h i hi; rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  obtain ⟨a3, -⟩ := byte_step (stepC (cst oStep) (stepC (cst oStep) W)) fun i hi => by
    rw [a2 i hi, a1 i hi]; have := h i hi; rw [BitVec.toNat_add, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  refine ⟨fun i hi => ?_, fun i h8 hi => ?_⟩
  · have hi' : i < 16 := by omega_arith
    simp only [accX, yA, yB, byte_xor, byte_and, byte_lkX _ _ _ hi', a3 i hi, a2 i hi, a1 i hi, luB, pairB, BitVec.add_assoc,
      BitVec.reduceAdd]
    ac_rfl
  · have hm : ∀ q < 4, byte (cst (oMask q)) i = 0#8 := fun q hq => by
      have := List.all_eq_true.mp (List.all_eq_true.mp mask_hi q (List.mem_range.mpr hq)) (i - 8)
        (List.mem_range.mpr (by omega_arith))
      rwa [beq_iff_eq, show 8 + (i - 8) = i by omega_arith] at this
    simp only [accX, byte_xor, byte_and, hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide),
      BitVec.and_zero, BitVec.xor_zero]

/-! ## The fold and P -/

theorem dword_xor (a b : BitVec 128) (k : Nat) : dword (a ^^^ b) k = dword a k ^^^ dword b k := VG.X86.dword_pxor a b k
theorem dword_and (a b : BitVec 128) (k : Nat) : dword (a &&& b) k = dword a k &&& dword b k := VG.X86.Lanes.dword_pand a b k

/-- The low doubleword of a quadword shift right by fewer than 32 bits. -/
theorem dword_psrlq (A : BitVec 128) {n : Nat} (h0 : 0 < n) (hn : n < 32) :
    dword (XShiftOp.eval .psrlq A (BitVec.ofNat 8 n)) 0 = (dword A 0 >>> n) ||| (dword A 1 <<< (32 - n)) := by
  have e : (BitVec.ofNat 8 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega_arith
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [XShiftOp.eval, e, show ¬ 63 < n by omega_arith, ite_false, VG.X86.getLsbD_dword, hj, decide_true,
    Bool.true_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, Nat.mul_zero, Nat.zero_add,
    Nat.mul_one, BitVec.getLsbD_append, qword, BitVec.getLsbD_extractLsb', show j < 64 by omega_arith,
    show n + j < 64 by omega_arith, ite_true]
  by_cases h : n + j < 32
  · simp [h, show j < 32 - n by omega_arith]
  · simp [h, show ¬ j < 32 - n by omega_arith, show j - (32 - n) < 32 by omega_arith,
      show 32 + (j - (32 - n)) = n + j by omega_arith]

theorem dword_fold (A : BitVec 128) :
    dword (shufDwords A 0xe1 ^^^ A) 0 = dword A 0 ^^^ dword A 1 ∧ dword (shufDwords A 0xe1 ^^^ A) 1 = dword A 0 ^^^ dword A 1 := by
  refine ⟨?_, ?_⟩
  · rw [dword_xor, VG.X86.dword_shufDwords _ _ (by decide), BitVec.xor_comm]; rfl
  · rw [dword_xor, VG.X86.dword_shufDwords _ _ (by decide)]; rfl

theorem dword_termX (A : BitVec 128) (i : Nat) {n : Nat} (h0 : 0 < n) (hn : n < 32) :
    dword (termX A i n) 0 = (dword A 0 ^^^ dword A 1).rotateRight n &&& pM i := by
  obtain ⟨f0, f1⟩ := dword_fold A
  rw [termX, dword_and, dword_psrlq _ h0 hn, f0, f1, pM, BitVec.rotateRight_def, Nat.mod_eq_of_lt hn]

/-- The target with P of the word of the S-boxes' outputs. -/
theorem dword_pX (A T : BitVec 128) : dword (pX A T) 0 = dword T 0 ^^^ pOut (dword A 0 ^^^ dword A 1) := by
  simp only [pX, dword_xor, dword_termX A _ (show 0 < 7 by decide) (show 7 < 32 by decide),
    dword_termX A _ (show 0 < 15 by decide) (show 15 < 32 by decide),
    dword_termX A _ (show 0 < 16 by decide) (show 16 < 32 by decide),
    dword_termX A _ (show 0 < 23 by decide) (show 23 < 32 by decide),
    dword_termX A _ (show 0 < 27 by decide) (show 27 < 32 by decide),
    dword_termX A _ (show 0 < 30 by decide) (show 30 < 32 by decide), pOut]
  ac_rfl

/-! ## A round -/

theorem wb_lt (r : BitVec 32) (k : BitVec 48) (i : Nat) : (wb r k i).toNat < 128 := by
  have h := (roundChunk (bx i) r k).isLt
  rw [wb, BitVec.toNat_or]
  refine Nat.or_lt_two_pow (n := 7) (by decide) ?_
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

theorem rotl2 (q : BitVec 32) : (q >>> 30) ||| (q <<< (32 - 30)) = q.rotateLeft 2 := by
  rw [BitVec.rotateLeft_def, BitVec.or_comm]

/-- A round: from the half `r` rotated right by one in `X`'s low doubleword
and the two words of the round key `s` in `K`'s, the target's low doubleword
with the round function of `r`, rotated right by one. -/
theorem round_ok (X K T : BitVec 128) (r : BitVec 32) (s : BitVec 64) (hX : dword X 0 = r.rotateRight 1)
    (k0 : dword K 0 = kw0 s) (k1 : dword K 1 = kw1 s) :
    dword (roundX X K T) 0 = dword T 0 ^^^ (roundFunction r (s.setWidth 48)).rotateRight 1 := by
  obtain ⟨m0, m1, -, -⟩ := m_dwords
  have d0 : dword (idxX X K) 0 = ((r.rotateRight 1 >>> 2) &&& 0x3f3f3f3f#32) ^^^ kw0 s := by
    rw [idxX, dword_xor, dword_and, VG.X86.punpckldq_eq, VG.X86.dword_ofDwords_0,
      VG.X86.dword_psrld _ _ (by decide) (by decide), hX, m0, k0]
    rfl
  have d1 : dword (idxX X K) 1 = (((r.rotateRight 1).rotateLeft 2) &&& 0x3f3f3f3f#32) ^^^ kw1 s := by
    rw [idxX, dword_xor, dword_and, VG.X86.punpckldq_eq, VG.X86.dword_ofDwords_1,
      dword_psrlq _ (show 0 < 30 by decide) (by decide), VG.X86.dword_shufDwords _ _ (show 0 < 4 by decide),
      VG.X86.dword_shufDwords _ _ (show 1 < 4 by decide), m1, k1]
    show ((dword X 0 >>> 30 ||| dword X 0 <<< (32 - 30)) &&& 0x3f3f3f3f#32) ^^^ kw1 s = _
    rw [rotl2, hX]
  have hb : ∀ i < 8, byte (idxX X K) i = wb r (s.setWidth 48) i := fun i hi => by
    rw [byte_eq_dword]
    by_cases h : i < 4
    · rw [show i / 4 = 0 by omega_arith, show i % 4 = i by omega_arith, d0]; exact idx_lo r s h
    · have := idx_hi r s (i := i - 4) (by omega_arith)
      rw [show 4 + (i - 4) = i by omega_arith] at this
      rw [show i / 4 = 1 by omega_arith, show i % 4 = i - 4 by omega_arith, d1]; exact this
  obtain ⟨hA, -⟩ := byte_accX (idxX X K) fun i hi => by rw [hb i hi]; exact wb_lt _ _ _
  rw [roundX, dword_pX]
  congr 1
  refine pOut_round _ _ r _ (fun i hi => ?_) (fun i hi => ?_)
  · have := hA i (by omega_arith)
    rwa [byte_eq_dword, show i / 4 = 0 by omega_arith, show i % 4 = i by omega_arith, hb i (by omega_arith)] at this
  · have := hA (4 + i) (by omega_arith)
    rwa [byte_eq_dword, show (4 + i) / 4 = 1 by omega_arith, show (4 + i) % 4 = i by omega_arith,
      hb (4 + i) (by omega_arith)] at this

end VG.Proof.TripleDes.X86.Ssse3
