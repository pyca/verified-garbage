import VerifiedGarbage.Proof.Camellia.Layout
import VerifiedGarbage.Proof.Camellia.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.Camellia.KeyOrder

/-!
# The key schedule on 64-bit halves

The implementations compute the key schedule on the 64-bit halves of `KL`,
`KR`, `KA` and `KB`: `klkr_halves` gives `KL` and `KR`'s from the key's
bytes, `kakb_halves` `KA` and `KB`'s from theirs through the same pairs of
rounds as encryption (`pair`), and `hi_eq` and `lo_eq` a half of a 128-bit
rotation from the two halves (`rotHalf`).
-/

namespace VG.Proof.Camellia

open VG VG.Spec.Camellia

/-- The high and low halves of a 128-bit value. -/
def hiW (x : BitVec 128) : BitVec 64 := (x >>> 64).setWidth 64
def loW (x : BitVec 128) : BitVec 64 := x.setWidth 64

theorem hiW_xor (x y : BitVec 128) : hiW (x ^^^ y) = hiW x ^^^ hiW y := by
  simp only [hiW, BitVec.ushiftRight_xor_distrib, BitVec.setWidth_xor]

theorem loW_xor (x y : BitVec 128) : loW (x ^^^ y) = loW x ^^^ loW y := by
  simp only [loW, BitVec.setWidth_xor]

theorem hiW_append (x y : BitVec 64) : hiW (x ++ y) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  change (((x ++ y : BitVec (64 + 64)) >>> 64).setWidth 64).getLsbD i = _
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  simp [hi]

theorem loW_append (x y : BitVec 64) : loW (x ++ y) = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  change ((x ++ y : BitVec (64 + 64)).setWidth 64).getLsbD i = _
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  simp [hi]

/-- `KA` and `KB` from the halves of `KL` and `KR`. -/
theorem kakb_halves (kl kr : BitVec 128) :
    let d₁ := pair sigma1 sigma2 (hiW kl ^^^ hiW kr, loW kl ^^^ loW kr)
    let d₂ := pair sigma3 sigma4 (d₁.1 ^^^ hiW kl, d₁.2 ^^^ loW kl)
    let d₃ := pair sigma5 sigma6 (d₂.1 ^^^ hiW kr, d₂.2 ^^^ loW kr)
    hiW (kakb kl kr).1 = d₂.1 ∧ loW (kakb kl kr).1 = d₂.2 ∧ hiW (kakb kl kr).2 = d₃.1 ∧
      loW (kakb kl kr).2 = d₃.2 := by
  have h1 : ∀ x : BitVec 128, (x >>> 64).setWidth 64 = hiW x := fun _ => rfl
  have h2 : ∀ x : BitVec 128, x.setWidth 64 = loW x := fun _ => rfl
  simp only [kakb, pair, h1, h2, hiW_xor, loW_xor, hiW_append, loW_append, and_self]

theorem getLsbD_ofBytes_bytesAt (m : Mem) (p : Addr) {n len k : Nat} (hk : k < n) (hl : 8 * len = n) :
    (ofBytes n (bytesAt m p len)).getLsbD k = (m (p + BitVec.ofNat 64 (len - 1 - k / 8))).getLsbD (k % 8) := by
  rw [getLsbD_ofBytes n _ hk (by simp [bytesAt, hl])]
  simp [bytesAt, show len - 1 - k / 8 < len by omega]

theorem getLsbD_wordAt (m : Mem) (p : Addr) {k : Nat} (hk : k < 64) :
    (wordAt m p).getLsbD k = (m (p + BitVec.ofNat 64 (7 - k / 8))).getLsbD (k % 8) :=
  getLsbD_ofBytes_bytesAt m p hk rfl

theorem wordAt_off_bit (m : Mem) (p : Addr) (d : Nat) {k : Nat} (hk : k < 64) :
    (wordAt m (p + BitVec.ofNat 64 d)).getLsbD k = (m (p + BitVec.ofNat 64 (d + (7 - k / 8)))).getLsbD (k % 8) := by
  rw [getLsbD_wordAt m _ hk, Offset.add_add]

/-- `KL` and `KR`'s halves from the key's bytes. -/
theorem klkr_halves (m : Mem) (p : Addr) {len : Nat} (hlen : len = 16 ∨ len = 24 ∨ len = 32) :
    hiW (klkr (bytesAt m p len)).1 = wordAt m p ∧
    loW (klkr (bytesAt m p len)).1 = wordAt m (p + BitVec.ofNat 64 8) ∧
    hiW (klkr (bytesAt m p len)).2 = (if len = 16 then 0 else wordAt m (p + BitVec.ofNat 64 16)) ∧
    loW (klkr (bytesAt m p len)).2 = (if len = 16 then 0 else if len = 24 then ~~~ wordAt m (p + BitVec.ofNat 64 16)
      else wordAt m (p + BitVec.ofNat 64 24)) := by
  have hl : (bytesAt m p len).length = len := by simp [bytesAt]
  rcases hlen with rfl | rfl | rfl
  · simp only [klkr, hl, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro t ht
    · simp only [hiW, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, ht, decide_true, Bool.true_and]
      rw [getLsbD_ofBytes_bytesAt m p (n := 128) (len := 16) (k := 64 + t) (by omega) rfl, getLsbD_wordAt m p ht]
      rw [show 16 - 1 - (64 + t) / 8 = 7 - t / 8 by omega, show (64 + t) % 8 = t % 8 by omega]
    · simp only [loW, BitVec.getLsbD_setWidth, ht, decide_true, Bool.true_and]
      rw [getLsbD_ofBytes_bytesAt m p (n := 128) (len := 16) (k := t) (by omega) rfl, wordAt_off_bit m p 8 ht,
        show 16 - 1 - t / 8 = 8 + (7 - t / 8) by omega]
    · simp [hiW]
    · simp [loW]
  · simp only [klkr, hl, show (24 : Nat) ≠ 16 by decide, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro t ht
    · simp only [hiW, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, ht, decide_true, Bool.true_and,
        show 64 + t < 128 by omega]
      rw [getLsbD_ofBytes_bytesAt m p (n := 192) (len := 24) (k := 64 + (64 + t)) (by omega) rfl,
        getLsbD_wordAt m p ht, show 24 - 1 - (64 + (64 + t)) / 8 = 7 - t / 8 by omega,
        show (64 + (64 + t)) % 8 = t % 8 by omega]
    · simp only [loW, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, ht, decide_true, Bool.true_and,
        show t < 128 by omega]
      rw [getLsbD_ofBytes_bytesAt m p (n := 192) (len := 24) (k := 64 + t) (by omega) rfl,
        wordAt_off_bit m p 8 ht, show 24 - 1 - (64 + t) / 8 = 8 + (7 - t / 8) by omega,
        show (64 + t) % 8 = t % 8 by omega]
    · simp only [hiW, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
        BitVec.getLsbD_shiftLeft, BitVec.getLsbD_not, ht, decide_true, Bool.true_and,
        show 64 + t < 128 by omega, show ¬ 64 + t < 64 by omega, show 64 + t - 64 = t by omega,
        decide_false, Bool.false_and, Bool.or_false, Bool.not_false, Bool.and_true]
      rw [getLsbD_ofBytes_bytesAt m p (n := 192) (len := 24) (k := t) (by omega) rfl,
        wordAt_off_bit m p 16 ht, show 24 - 1 - t / 8 = 16 + (7 - t / 8) by omega]
      simp only [show t < 128 by omega, decide_true, Bool.true_and]
    · simp only [loW, BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_not,
        ht, decide_true, Bool.true_and, show t < 128 by omega]
      rw [getLsbD_ofBytes_bytesAt m p (n := 192) (len := 24) (k := t) (by omega) rfl,
        wordAt_off_bit m p 16 ht, show 24 - 1 - t / 8 = 16 + (7 - t / 8) by omega]
      simp only [Bool.not_true, Bool.false_and, Bool.false_or]
  · simp only [klkr, hl, show (32 : Nat) ≠ 16 by decide, show (32 : Nat) ≠ 24 by decide, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro t ht
    · simp only [hiW, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, ht, decide_true, Bool.true_and,
        show 64 + t < 128 by omega]
      rw [getLsbD_ofBytes_bytesAt m p (n := 256) (len := 32) (k := 128 + (64 + t)) (by omega) rfl,
        getLsbD_wordAt m p ht, show 32 - 1 - (128 + (64 + t)) / 8 = 7 - t / 8 by omega,
        show (128 + (64 + t)) % 8 = t % 8 by omega]
    · simp only [loW, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, ht, decide_true, Bool.true_and,
        show t < 128 by omega]
      rw [getLsbD_ofBytes_bytesAt m p (n := 256) (len := 32) (k := 128 + t) (by omega) rfl,
        wordAt_off_bit m p 8 ht, show 32 - 1 - (128 + t) / 8 = 8 + (7 - t / 8) by omega,
        show (128 + t) % 8 = t % 8 by omega]
    · simp only [hiW, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, ht, decide_true, Bool.true_and,
        show 64 + t < 128 by omega]
      rw [getLsbD_ofBytes_bytesAt m p (n := 256) (len := 32) (k := 64 + t) (by omega) rfl,
        wordAt_off_bit m p 16 ht, show 32 - 1 - (64 + t) / 8 = 16 + (7 - t / 8) by omega,
        show (64 + t) % 8 = t % 8 by omega]
    · simp only [loW, BitVec.getLsbD_setWidth, ht, decide_true, Bool.true_and, show t < 128 by omega]
      rw [getLsbD_ofBytes_bytesAt m p (n := 256) (len := 32) (k := t) (by omega) rfl,
        wordAt_off_bit m p 24 ht, show 32 - 1 - t / 8 = 24 + (7 - t / 8) by omega]

/-- A half of `H ++ L` rotated left by `r`, from the halves: the high one
if `hi`. -/
def rotHalf (H L : BitVec 64) (r : Nat) (hi : Bool) : BitVec 64 :=
  let a := if decide (r < 64) = hi then H else L
  let b := if decide (r < 64) = hi then L else H
  if r % 64 = 0 then a else (a <<< (r % 64)) ||| (b >>> (64 - r % 64))

theorem rot128_bit (H L : BitVec 64) {r k : Nat} (hr : r < 128) (hk : k < 128) :
    ((H ++ L : BitVec (64 + 64)).rotateLeft r).getLsbD k =
      if (k + 128 - r) % 128 < 64 then L.getLsbD ((k + 128 - r) % 128) else H.getLsbD ((k + 128 - r) % 128 - 64) := by
  rw [BitVec.getLsbD_rotateLeft]
  simp only [show r % (64 + 64) = r by omega]
  split <;> rename_i h1 <;> simp only [BitVec.getLsbD_append, show k < 64 + 64 by omega, decide_true, Bool.true_and] <;>
    split <;> rename_i h2 <;> split <;> rename_i h3 <;> first | omega | (congr 1; omega)

theorem hi_eq (H L : BitVec 64) {r : Nat} (hr : r < 128) : hi (H ++ L) r = rotHalf H L r true := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  change ((((H ++ L : BitVec (64 + 64)).rotateLeft r) >>> 64).setWidth 64).getLsbD t = _
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, rot128_bit H L hr (by omega)]
  simp only [ht, decide_true, Bool.true_and, rotHalf]
  by_cases h64 : r < 64 <;> by_cases h0 : r % 64 = 0 <;>
    simp only [h64, h0, decide_true, decide_false, ↓reduceIte, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, ht, Bool.true_and]
  all_goals (try simp only [Bool.false_eq_true, ↓reduceIte])
  all_goals (by_cases h2 : t < r % 64 <;>
    (try simp only [h2, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and,
      Bool.false_or]) <;>
    split <;> rename_i h1 <;>
    (try rw [BitVec.getLsbD_of_ge _ (64 - r % 64 + t) (by omega), Bool.or_false]) <;>
    first | omega | (congr 1; omega))

theorem lo_eq (H L : BitVec 64) {r : Nat} (hr : r < 128) : lo (H ++ L) r = rotHalf H L r false := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  change (((H ++ L : BitVec (64 + 64)).rotateLeft r).setWidth 64).getLsbD t = _
  rw [BitVec.getLsbD_setWidth, rot128_bit H L hr (by omega)]
  simp only [ht, decide_true, Bool.true_and, rotHalf]
  by_cases h64 : r < 64 <;> by_cases h0 : r % 64 = 0 <;>
    simp only [h64, h0, decide_true, decide_false, ↓reduceIte, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, ht, Bool.true_and]
  all_goals (try simp only [Bool.false_eq_true, ↓reduceIte])
  all_goals (by_cases h2 : t < r % 64 <;>
    (try simp only [h2, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and,
      Bool.false_or]) <;>
    split <;> rename_i h1 <;>
    (try rw [BitVec.getLsbD_of_ge _ (64 - r % 64 + t) (by omega), Bool.or_false]) <;>
    first | omega | (congr 1; omega))


theorem split128 (x : BitVec 128) : x = hiW x ++ loW x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  change _ = (hiW x ++ loW x : BitVec (64 + 64)).getLsbD i
  rw [BitVec.getLsbD_append]
  simp only [hiW, loW, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  split
  · simp [*]
  · simp only [show i - 64 < 64 by omega, decide_true, Bool.true_and]; congr 1; omega

theorem hi_split (x : BitVec 128) {r : Nat} (hr : r < 128) : hi x r = rotHalf (hiW x) (loW x) r true := by
  rw [← hi_eq _ _ hr, ← split128]

theorem lo_split (x : BitVec 128) {r : Nat} (hr : r < 128) : lo x r = rotHalf (hiW x) (loW x) r false := by
  rw [← lo_eq _ _ hr, ← split128]

/-- The stored subkeys, from the four values: `[KL, KR, KA, KB]`. -/
def subkeyWords (vs : List (BitVec 128)) (ks : List (Nat × Nat × Bool)) : List (BitVec 64) :=
  ks.map fun (v, r, h) => rotHalf (hiW (vs.getD v 0)) (loW (vs.getD v 0)) r h

theorem scheduleWords_expandKey (key : List Byte) :
    scheduleWords (expandKey key) = subkeyWords
      [(klkr key).1, (klkr key).2, (kakb (klkr key).1 (klkr key).2).1, (kakb (klkr key).1 (klkr key).2).2]
      (if key.length = 16 then Impl.Camellia.subkeys128 else Impl.Camellia.subkeys256) := by
  by_cases h : key.length = 16
  · simp only [expandKey, h, ↓reduceIte, scheduleWords, subkeyWords, Impl.Camellia.subkeys128,
      Impl.Camellia.KL, Impl.Camellia.KA]
    simp (disch := decide) only [hi_split, lo_split]
    simp [List.range_succ, List.flatMap_cons]
  · simp only [expandKey, h, ↓reduceIte, scheduleWords, subkeyWords, Impl.Camellia.subkeys256,
      Impl.Camellia.KL, Impl.Camellia.KR, Impl.Camellia.KA, Impl.Camellia.KB]
    simp (disch := decide) only [hi_split, lo_split]
    simp [List.range_succ, List.flatMap_cons]

end VG.Proof.Camellia
