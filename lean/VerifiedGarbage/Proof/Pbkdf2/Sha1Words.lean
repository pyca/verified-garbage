module

public import VerifiedGarbage.Proof.Pbkdf2.MdStep
public import VerifiedGarbage.Proof.Sha1.Md

/-!
# PBKDF2-HMAC-SHA-1's iteration on words

Untrusted: everything here is checked by Lean. SHA-1's digest is its hash
value's words, big-endian, so the block a step compresses after a hash
value `x` (the `D = 20` bytes of a digest, then the padding of an 84-byte
message) is `x`'s words, `0x80000000`, nine zero words and the bit count
`672` (`blk`, `tailBlock_digest`). So one step of the iteration
(`Md.step`, `Proof/Pbkdf2/MdStep.lean`) on a digest is the digest of two
compressions of such blocks (`step_digest`), and the iteration on digests
is the digest of an iteration on hash values (`iterate_digest`), with `T`
updated by the words' XOR (`xorBytes_digest`). The digests of the arguments
are the big-endian words of their bytes (`digest_beWords`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Sha1Words

open VG.Spec.Sha1 (HashValue Word Block compress wordBytes parseBlock)
open VG.Proof.Sha1 (md)

/-- The block after the digest of `x`: its words, then SHA-1's padding of an
84-byte message. -/
def blk (x : HashValue) : Block := fun j =>
  if h : j.val < 5 then x[j.val] else if j.val = 5 then 0x80000000 else if j.val = 15 then 672 else 0

/-! ## Bytes and words -/

/-- The four bytes of a word, big-endian, make the word. -/
theorem be4 (x : Word) :
    (x.extractLsb' 24 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 0 8 : Word) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) by omega) with h | h | h | h
  · simp [h]
  · simp only [show ¬ i < 8 by omega, show i - 8 < 8 by omega, ite_true, ite_false, decide_true, Bool.true_and]
    congr 1; omega
  · simp only [show ¬ i < 8 by omega, show ¬ i - 8 < 8 by omega, show i - 8 - 8 < 8 by omega, ite_true,
      ite_false, decide_true, Bool.true_and]
    congr 1; omega
  · simp only [show ¬ i < 8 by omega, show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega,
      show i - 8 - 8 - 8 < 8 by omega, ite_false, decide_true, Bool.true_and]
    congr 1; omega

/-- The bytes of a word made of four bytes. -/
theorem ex24 (a b c d : BitVec 8) : (a ++ b ++ c ++ d : Word).extractLsb' 24 8 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  simp only [show ¬ 24 + i < 8 by omega, show ¬ 24 + i - 8 < 8 by omega, show ¬ 24 + i - 8 - 8 < 8 by omega,
    ite_false]
  congr 1; omega

theorem ex16 (a b c d : BitVec 8) : (a ++ b ++ c ++ d : Word).extractLsb' 16 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  simp only [show ¬ 16 + i < 8 by omega, show ¬ 16 + i - 8 < 8 by omega, show 16 + i - 8 - 8 < 8 by omega,
    ite_false, ite_true]
  congr 1; omega

theorem ex8 (a b c d : BitVec 8) : (a ++ b ++ c ++ d : Word).extractLsb' 8 8 = c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  simp only [show ¬ 8 + i < 8 by omega, show 8 + i - 8 < 8 by omega, ite_false, ite_true]
  congr 1; omega

theorem ex0 (a b c d : BitVec 8) : (a ++ b ++ c ++ d : Word).extractLsb' 0 8 = d := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  rw [Nat.zero_add]; simp [hi]

/-- The digest, word by word. -/
theorem digest_eq (x : HashValue) :
    md.digest x = wordBytes x[0] ++ wordBytes x[1] ++ wordBytes x[2] ++ wordBytes x[3] ++ wordBytes x[4] := by
  obtain ⟨⟨l⟩, hl⟩ := x
  match l, hl with
  | [a, b, c, d, e], _ => simp [md, wordBytes]

theorem take_digest (x : md.HV) : (md.digest x).take 20 = md.digest x :=
  List.take_of_length_le (Nat.le_of_eq (md.digest_length _))

/-- The five big-endian words of the 20 bytes at `p`. -/
def beWords (m : Mem) (p : Addr) : HashValue := Vector.ofFn fun k =>
  (m (p + BitVec.ofNat 64 (4 * k)) ++ m (p + BitVec.ofNat 64 (4 * k + 1)) ++ m (p + BitVec.ofNat 64 (4 * k + 2)) ++
    m (p + BitVec.ofNat 64 (4 * k + 3)) : Word)

theorem digest_beWords (m : Mem) (p : Addr) : md.digest (beWords m p) = Spec.Sha256.bytesAt m p 20 := by
  simp only [digest_eq, beWords, Vector.getElem_ofFn, wordBytes, ex24, ex16, ex8, ex0]
  simp [Spec.Sha256.bytesAt, List.range_succ]

/-! ## One step -/

theorem tailPad_eq : md.tailPad 20 = [0x80] ++ List.replicate 35 0 ++ [0, 0, 0, 0, 0, 0, 2, 0xa0] := by
  decide +kernel

/-- The block after the digest of `x`. -/
theorem tailBlock_digest (x : md.HV) : md.tailBlock 20 (md.digest x) = blk x := by
  unfold MdStream.Md.tailBlock
  rw [tailPad_eq, digest_eq x, show md.parse = parseBlock from rfl]
  simp only [wordBytes, List.cons_append, List.nil_append, List.replicate_succ, List.replicate_zero]
  funext j
  obtain ⟨j, hj⟩ := j
  simp only [parseBlock, blk]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨
    j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [List.getD_cons_succ, List.getD_cons_zero, be4, Nat.reduceMul, Nat.reduceAdd, Nat.reduceLT,
    ↓reduceDIte, ↓reduceIte, Nat.reduceEqDiff] <;> decide

/-- One step on hash values: the inner compression, with `hi`, of the block
after `x`, then the outer one, with `ho`, of the block after that. -/
def wstep (hi ho x : HashValue) : HashValue := compress ho (blk (compress hi (blk x)))

theorem step_digest (hi ho x : HashValue) : md.step 20 hi ho (md.digest x) = md.digest (wstep hi ho x) := by
  unfold MdStream.Md.step
  rw [tailBlock_digest x, take_digest (md.compress hi (blk x)), tailBlock_digest, take_digest]
  rfl

/-! ## The iteration -/

/-- `n` steps on hash values from `U = x` and `T = y`: the final `T`. -/
def wIter (hi ho : HashValue) : Nat → HashValue → HashValue → HashValue
  | 0, _, y => y
  | n + 1, x, y => wIter hi ho n (wstep hi ho x) (Vector.zipWith (· ^^^ ·) y (wstep hi ho x))

theorem wordBytes_xor (a b : Word) :
    wordBytes (a ^^^ b) = List.zipWith (· ^^^ ·) (wordBytes a) (wordBytes b) := by
  simp [wordBytes, BitVec.extractLsb'_xor]

theorem xorBytes_digest (y x : HashValue) :
    Spec.Pbkdf2.xorBytes (md.digest y) (md.digest x) = md.digest (Vector.zipWith (· ^^^ ·) y x) := by
  simp only [digest_eq, Spec.Pbkdf2.xorBytes, Vector.getElem_zipWith, wordBytes_xor]
  simp [wordBytes]

theorem iterate_digest (hi ho : HashValue) (n : Nat) (x y : HashValue) :
    Spec.Pbkdf2.iterate (md.step 20 hi ho) n (md.digest x) (md.digest y) = md.digest (wIter hi ho n x y) := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih => simp only [Spec.Pbkdf2.iterate, wIter, step_digest, xorBytes_digest, ih]

end VG.Proof.Pbkdf2.Sha1Words
