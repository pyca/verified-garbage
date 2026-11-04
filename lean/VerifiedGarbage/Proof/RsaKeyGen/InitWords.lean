module

public import VerifiedGarbage.Spec.RsaKeyGen.Generation
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Ffdh.ControlMemory

/-! # Starting the RSA prime search, for any target

What `vg_rsa_prime_search_init` computes, in terms every target's proof
shares: whether `e` is 3 (`os2ip_eq_three`, by the OR of its octets), the
four words (`initWords`, `primeInit_eq`) and the state with them written
(`written`, `written_words`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.SearchInit

open VG VG.Proof.Bignum

/-- The OR of octets, widened. -/
def orOf (bs : List Byte) : BitVec 64 := bs.foldl (fun a b => a ||| b.setWidth 64) 0

theorem orOf_snoc (bs : List Byte) (b : Byte) : orOf (bs ++ [b]) = orOf bs ||| b.setWidth 64 := by
  simp only [orOf, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem or_eq_zero (x y : BitVec 64) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_or, show (0 : BitVec 64).toNat = 0 from rfl] at this
    have := Nat.or_eq_zero_iff.mp this
    exact ⟨BitVec.eq_of_toNat_eq (by rw [this.1]; rfl), BitVec.eq_of_toNat_eq (by rw [this.2]; rfl)⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem widen_eq_zero (b : Byte) : b.setWidth 64 = 0 ↔ b = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.isLt (by decide)),
      show (0 : BitVec 64).toNat = 0 from rfl] at this
    exact BitVec.eq_of_toNat_eq (by rw [this]; rfl)
  · rintro rfl; rfl

private theorem foldl_or_eq_zero (bs : List Byte) (a : BitVec 64) :
    bs.foldl (fun a b => a ||| b.setWidth 64) a = 0 ↔ a = 0 ∧ ∀ b ∈ bs, b = 0 := by
  induction bs generalizing a with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, ih, or_eq_zero, widen_eq_zero, List.forall_mem_cons, and_assoc]

theorem orOf_eq_zero (bs : List Byte) : orOf bs = 0 ↔ ∀ b ∈ bs, b = 0 := by
  simp only [orOf, foldl_or_eq_zero, true_and]

private theorem foldl_os2ip_eq_zero (bs : List Byte) (a : Nat) :
    bs.foldl (fun x b => 256 * x + b.toNat) a = 0 ↔ a = 0 ∧ ∀ b ∈ bs, b = 0 := by
  induction bs generalizing a with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldl_cons, ih, List.forall_mem_cons, ← and_assoc]
    refine and_congr_left' ⟨fun h => ⟨by omega, BitVec.eq_of_toNat_eq (by
      rw [show (0 : Byte).toNat = 0 from rfl]; omega)⟩, ?_⟩
    rintro ⟨rfl, rfl⟩; rfl

private theorem os2ip_eq_zero (bs : List Byte) : Spec.Rsa.os2ip bs = 0 ↔ ∀ b ∈ bs, b = 0 := by
  simp only [Spec.Rsa.os2ip, foldl_os2ip_eq_zero, true_and]

/-- `e` is 3 iff its leading octets are zeros and its last is 3. -/
theorem os2ip_eq_three (bs : List Byte) (b : Byte) :
    Spec.Rsa.os2ip (bs ++ [b]) = 3 ↔ orOf bs ||| (b.setWidth 64 ^^^ 3) = 0 := by
  rw [Proof.Rsa.os2ip_snoc]
  have hb := b.isLt
  have hx : b.setWidth 64 ^^^ 3 = 0 ↔ b = 3 := by
    constructor
    · intro h
      have h' : b.setWidth 64 = 3 := by
        have := congrArg (· ^^^ (3 : BitVec 64)) h
        simpa [BitVec.xor_assoc] using this
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)] at this
      simpa using this
    · rintro rfl; rfl
  rw [or_eq_zero, hx, orOf_eq_zero, ← os2ip_eq_zero]
  constructor
  · intro h
    refine ⟨by omega, BitVec.eq_of_toNat_eq ?_⟩
    have : b.toNat = 3 := by omega
    simpa using this
  · rintro ⟨h1, rfl⟩
    rw [h1]
    rfl

theorem bytesAt_succ (m : Mem) (P : Addr) (n : Nat) :
    Spec.Rsa.bytesAt m P (n + 1) = Spec.Rsa.bytesAt m P n ++ [m (P + BitVec.ofNat 64 n)] := by
  simp only [Spec.Rsa.bytesAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem shl_ofNat (L k : Nat) (h : L * 2 ^ k < 2 ^ 64) :
    BitVec.ofNat 64 L <<< k = BitVec.ofNat 64 (L * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  have hL : L < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)) h
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem add_ofNat (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

/-- The four words `primeInit` gives, for a width `L` and whether `e` is 3. -/
def initWords (L : Nat) (three : Bool) : List (BitVec 64) :=
  [BitVec.ofNat 64 (if three then 64 * L else 40 * L), BitVec.ofNat 64 L,
    BitVec.ofNat 64 (32769 * L), BitVec.ofNat 64 (32 * L)]

/-- The state with its four words written. -/
def written (m : Mem) (B : Addr) (w : List (BitVec 64)) : Mem :=
  (((m.writeW B (w.getD 0 0)).writeW (off B 8) (w.getD 1 0)).writeW
    (off B 16) (w.getD 2 0)).writeW (off B 24) (w.getD 3 0)

abbrev initValid (L len : Nat) : Prop := 32 ≤ L ∧ L ≤ 512 ∧ L % 8 = 0 ∧ 1 ≤ len ∧ len ≤ 8

open VG.Proof.Ffdh.Control (controller_store_word)

theorem written_words (m : Mem) (B : Addr) (a b c d : BitVec 64) :
    Spec.Rsa.wordsAt (written m B [a, b, c, d]) B 4 = [a, b, c, d] := by
  change [word (written m B [a, b, c, d]) B 0, word (written m B [a, b, c, d]) B 8,
    word (written m B [a, b, c, d]) B 16, word (written m B [a, b, c, d]) B 24] = _
  have hm : written m B [a, b, c, d] =
      (((m.writeW (off B (8 * 0)) a).writeW (off B (8 * 1)) b).writeW (off B (8 * 2)) c).writeW
        (off B (8 * 3)) d := by
    simp only [written, off, Nat.mul_zero, BitVec.add_zero, List.getD_cons_zero, List.getD_cons_succ]
  rw [hm]
  have hword (j : Nat) (hj : j < 16) :
      word ((((m.writeW (off B (8 * 0)) a).writeW (off B (8 * 1)) b).writeW (off B (8 * 2)) c).writeW
        (off B (8 * 3)) d) B (8 * j) =
        if j = 3 then d else if j = 2 then c else if j = 1 then b else if j = 0 then a
        else word m B (8 * j) := by
    rw [controller_store_word _ _ _ (i := 3) (by decide) hj,
      controller_store_word _ _ _ (i := 2) (by decide) hj,
      controller_store_word _ _ _ (i := 1) (by decide) hj,
      controller_store_word _ _ _ (i := 0) (by decide) hj]
  rw [hword 0 (by decide), hword 1 (by decide), hword 2 (by decide), hword 3 (by decide)]
  rfl

theorem primeInit_eq (L : Nat) (eB : List Byte) :
    Spec.RsaKeyGen.primeInit L eB =
      if initValid L eB.length then
        some [if Spec.Rsa.os2ip eB = 3 then 64 * L else 40 * L, L, 32769 * L, 32 * L]
      else none := by
  unfold Spec.RsaKeyGen.primeInit initValid
  by_cases hv : 32 ≤ L ∧ L ≤ 512 ∧ L % 8 = 0 ∧ 1 ≤ eB.length ∧ eB.length ≤ 8
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hv
    have hb : (32 ≤ L && L ≤ 512 && L % 8 == 0 && 1 ≤ eB.length && eB.length ≤ 8) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]; omega
    rw [hb, ite_eq_left_of_eq_true _ _ (eq_true rfl),
      ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, h2, h3, h4, h5⟩)]
    simp only [Spec.RsaKeyGen.primeLimit, Spec.RsaKeyGen.primeRequest, Spec.RsaKeyGen.primeEntropy,
      Spec.Entropy.request, Option.some.injEq, List.cons.injEq, and_true]
    exact ⟨by split <;> omega, trivial, trivial, by omega⟩
  · have hb : (32 ≤ L && L ≤ 512 && L % 8 == 0 && 1 ≤ eB.length && eB.length ≤ 8) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq]
      omega
    rw [hb, ite_eq_right_of_eq_false _ _ (eq_false hv)]
    rfl

end VG.Proof.RsaKeyGen.SearchInit
