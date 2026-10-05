import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Spec.Ecdsa.Rfc6979
import VerifiedGarbage.Spec.Ecdsa.P256

/-!
# Deterministic ECDSA: big-endian numbers

The 32 bytes at an address, big-endian, from the byte reversals of their
four words (`ofBytes_32`); a number's encoding is determined by its value
(`toBytes_ofBytes`), and a number's value by its encoding (`ofBytes_toBytes`);
RFC 6979's conversions at P-256, of a hash of at least 32 bytes, which take
its leftmost 32 (`hashToInt_take`, `bits2octets_eq`); and, for any curve,
`bits2int` of at least `rlen` bytes, from its leftmost `rlen`
(`hashToInt_takeR`), and `bits2octets` of a hash shorter than `n`, which
is the hash after zero bytes (`bits2octets_short`).
Each target's proof uses them, its byte reversal being `byteRev64`.
-/

namespace VG.Proof.Ecdsa.Rfc6979

open VG VG.Proof.Weierstrass

/-- The bytes at an address, whichever specification names them. -/
theorem ecdsa_bytesAt : Spec.Ecdsa.bytesAt = Spec.Sha256.bytesAt := rfl

theorem ofBytes_32 (m : Mem) (q : Addr) :
    Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m q 32) =
      (byteRev64 (m.readW q 64)).toNat * 2 ^ 192 +
        (byteRev64 (m.readW (q + BitVec.ofNat 64 8) 64)).toNat * 2 ^ 128 +
        (byteRev64 (m.readW (q + BitVec.ofNat 64 16) 64)).toNat * 2 ^ 64 +
        (byteRev64 (m.readW (q + BitVec.ofNat 64 24) 64)).toNat := by
  rw [byteRev64_ofBytes, byteRev64_ofBytes, byteRev64_ofBytes, byteRev64_ofBytes, ← ecdsa_bytesAt,
    show 32 = 8 + (8 + (8 + 8)) from rfl, bytesAt_add, bytesAt_add, bytesAt_add,
    ofBytes_append, ofBytes_append, ofBytes_append, length_bytesAt, List.length_append, length_bytesAt,
    List.length_append, length_bytesAt, length_bytesAt, Offset.add_add, Offset.add_add]
  simp only [Nat.reduceAdd, Nat.reducePow]
  omega

theorem toBytes_succ (len x : Nat) :
    Spec.Weierstrass.toBytes (len + 1) x = BitVec.ofNat 8 (x >>> (8 * len)) :: Spec.Weierstrass.toBytes len x := by
  simp only [Spec.Weierstrass.toBytes, List.range_succ, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.map_cons]

theorem toBytes_add (len a y : Nat) :
    Spec.Weierstrass.toBytes len (a * 2 ^ (8 * len) + y) = Spec.Weierstrass.toBytes len y := by
  simp only [Spec.Weierstrass.toBytes]
  refine List.map_congr_left fun i hi => ?_
  have hi : i < len := by simpa using hi
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have e : a * 2 ^ (8 * len) = (a * 2 ^ (8 * (len - i - 1)) * 2 ^ 8) * 2 ^ (8 * i) := by
    rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]; congr 2; omega
  rw [e, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_right]

theorem ofBytes_single (b : Byte) : Spec.Weierstrass.ofBytes [b] = b.toNat := by
  simp [Spec.Weierstrass.ofBytes]

theorem pow256 (n : Nat) : (256 : Nat) ^ n = 2 ^ (8 * n) := by
  rw [Nat.pow_mul]

theorem ofBytes_lt : ∀ l : List Byte, Spec.Weierstrass.ofBytes l < 2 ^ (8 * l.length)
  | [] => by decide
  | b :: l => by
    have := ofBytes_lt l
    have hb := b.isLt
    rw [show b :: l = [b] ++ l from rfl, ofBytes_append, ofBytes_single, pow256,
      List.length_append, List.length_singleton, Nat.mul_add, Nat.pow_add, Nat.mul_one]
    have : b.toNat * 2 ^ (8 * l.length) + 2 ^ (8 * l.length) ≤ 2 ^ 8 * 2 ^ (8 * l.length) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega

theorem toBytes_ofBytes : ∀ (l : List Byte), Spec.Weierstrass.toBytes l.length (Spec.Weierstrass.ofBytes l) = l
  | [] => rfl
  | b :: l => by
    have hl := ofBytes_lt l
    have hb := b.isLt
    rw [show b :: l = [b] ++ l from rfl, ofBytes_append, ofBytes_single, pow256,
      List.length_append, List.length_singleton, Nat.add_comm 1, toBytes_succ, toBytes_add, toBytes_ofBytes l]
    refine congrArg (· :: l) ?_
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hl, Nat.zero_add, Nat.mod_eq_of_lt hb]

theorem toBytes_mod (len x : Nat) : Spec.Weierstrass.toBytes len x = Spec.Weierstrass.toBytes len (x % 2 ^ (8 * len)) := by
  conv => lhs; rw [← Nat.div_add_mod x (2 ^ (8 * len)), Nat.mul_comm]
  exact toBytes_add _ _ _

/-- A number below `2^(8 len)` is the number of its `len` bytes. -/
theorem ofBytes_toBytes : ∀ (len x : Nat), x < 2 ^ (8 * len) →
    Spec.Weierstrass.ofBytes (Spec.Weierstrass.toBytes len x) = x
  | 0, x, h => by simp only [Nat.mul_zero, Nat.pow_zero] at h; simp [Spec.Weierstrass.toBytes, Spec.Weierstrass.ofBytes]; omega
  | len + 1, x, h => by
    rw [toBytes_succ, show BitVec.ofNat 8 (x >>> (8 * len)) :: Spec.Weierstrass.toBytes len x =
        [BitVec.ofNat 8 (x >>> (8 * len))] ++ Spec.Weierstrass.toBytes len x from rfl, ofBytes_append,
      ofBytes_single, toBytes_mod, ofBytes_toBytes len _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
    simp only [Spec.Weierstrass.toBytes, List.length_map, List.length_reverse, List.length_range, pow256,
      BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have h₁ : x / 2 ^ (8 * len) < 2 ^ 8 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show 8 + 8 * len = 8 * (len + 1) by omega]
      exact h
    rw [Nat.mod_eq_of_lt h₁, Nat.mul_comm]
    exact Nat.div_add_mod x _

/-- The bytes of a number of `len` bytes, after `k` zero bytes. -/
theorem toBytes_pad (k len x : Nat) (hx : x < 2 ^ (8 * len)) :
    Spec.Weierstrass.toBytes (k + len) x = List.replicate k 0 ++ Spec.Weierstrass.toBytes len x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show k + 1 + len = (k + len) + 1 by omega, toBytes_succ, ih, List.replicate_succ, List.cons_append]
    refine congrArg (· :: _) ?_
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))]
    rfl

/-- A number with zero bytes before it. -/
theorem ofBytes_zeros (k : Nat) (l : List Byte) :
    Spec.Weierstrass.ofBytes (List.replicate k 0 ++ l) = Spec.Weierstrass.ofBytes l := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, show (0 : Byte) :: (List.replicate k 0 ++ l) =
      [0] ++ (List.replicate k 0 ++ l) from rfl, ofBytes_append, ofBytes_single, ih]
    simp

/-- A number with zero bytes after it. -/
theorem ofBytes_append_zeros (l : List Byte) (k : Nat) :
    Spec.Weierstrass.ofBytes (l ++ List.replicate k 0) = Spec.Weierstrass.ofBytes l * 2 ^ (8 * k) := by
  have hz : Spec.Weierstrass.ofBytes (List.replicate k 0) = 0 := by
    have := ofBytes_zeros k []
    rwa [List.append_nil] at this
  rw [ofBytes_append, List.length_replicate, pow256, hz, Nat.add_zero]

/-! ## For any curve -/

/-- `rlen` is `R` when `n` has more than `8 (R - 1)` bits, and at most `8 R`. -/
theorem rlenR {C : Spec.Weierstrass.Curve} {R : Nat} (h₁ : Spec.Ecdsa.nBits C ≤ 8 * R)
    (h₂ : 8 * R < Spec.Ecdsa.nBits C + 8) : Spec.Ecdsa.Rfc6979.rlen C = R := by
  rw [Spec.Ecdsa.Rfc6979.rlen]; omega

/-- A hash of at least `R` bytes is the number of its leftmost `R`, shifted
right by the bits of them beyond `nBits`. -/
theorem hashToInt_takeR {C : Spec.Weierstrass.Curve} {R : Nat} (h₁ : Spec.Ecdsa.nBits C ≤ 8 * R)
    {h : List Byte} (hl : R ≤ h.length) :
    Spec.Ecdsa.hashToInt C h = Spec.Weierstrass.ofBytes (h.take R) >>> (8 * R - Spec.Ecdsa.nBits C) := by
  have hd : (h.drop R).length = h.length - R := List.length_drop
  have key : Spec.Weierstrass.ofBytes h =
      Spec.Weierstrass.ofBytes (h.take R) * 2 ^ (8 * (h.length - R)) + Spec.Weierstrass.ofBytes (h.drop R) := by
    conv => lhs; rw [← List.take_append_drop R h]
    rw [ofBytes_append, hd, pow256]
  rw [Spec.Ecdsa.hashToInt]
  by_cases hQ : 8 * h.length ≤ Spec.Ecdsa.nBits C
  · have hR : h.length = R := by omega
    simp only [hQ, ite_true]
    rw [show h.take R = h from List.take_of_length_le (by omega),
      show 8 * R - Spec.Ecdsa.nBits C = 0 by omega, Nat.shiftRight_zero]
  · simp only [hQ, ite_false]
    rw [key, show 8 * h.length - Spec.Ecdsa.nBits C = 8 * (h.length - R) + (8 * R - Spec.Ecdsa.nBits C) by
      omega, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow (_ + _),
      Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (by have := ofBytes_lt (h.drop R); rwa [hd] at this), Nat.zero_add]

/-- A hash of `D` bytes, fewer than `n` has bits, is its number, below `n`. -/
theorem hashToInt_short {C : Spec.Weierstrass.Curve} {h : List Byte} (hl : 8 * h.length < Spec.Ecdsa.nBits C)
    (hn : C.n ≠ 0) : Spec.Ecdsa.hashToInt C h = Spec.Weierstrass.ofBytes h ∧ Spec.Weierstrass.ofBytes h < C.n := by
  refine ⟨by rw [Spec.Ecdsa.hashToInt]; simp only [show 8 * h.length ≤ Spec.Ecdsa.nBits C by omega, ite_true],
    Nat.lt_of_lt_of_le (ofBytes_lt h) ?_⟩
  have h₁ : 2 ^ C.n.log2 ≤ C.n := (Nat.le_log2 hn).mp (Nat.le_refl _)
  have h₂ : Spec.Ecdsa.nBits C = C.n.log2 + 1 := rfl
  exact Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) h₁

/-- `bits2octets` of such a hash: zero bytes, then the hash. -/
theorem bits2octets_short {C : Spec.Weierstrass.Curve} {R : Nat} (h₁ : Spec.Ecdsa.nBits C ≤ 8 * R)
    (h₂ : 8 * R < Spec.Ecdsa.nBits C + 8) {h : List Byte} (hl : 8 * h.length < Spec.Ecdsa.nBits C)
    (hn : C.n ≠ 0) :
    Spec.Ecdsa.Rfc6979.bits2octets C h = List.replicate (R - h.length) 0 ++ h := by
  obtain ⟨e₁, e₂⟩ := hashToInt_short hl hn
  rw [Spec.Ecdsa.Rfc6979.bits2octets, Spec.Ecdsa.Rfc6979.int2octets, Spec.Ecdsa.Rfc6979.bits2int, rlenR h₁ h₂,
    e₁, Nat.mod_eq_of_lt e₂, show R = (R - h.length) + h.length by omega, toBytes_pad _ _ _ (ofBytes_lt h),
    toBytes_ofBytes, Nat.add_sub_cancel]

/-! ## For a curve whose `n` has `8 Q` bits -/

/-- A hash of at least `Q` bytes is the number of its leftmost `Q`, for a
curve whose `n` has `8 Q` bits. -/
theorem hashToInt_takeQ {C : Spec.Weierstrass.Curve} {Q : Nat} (hq : Spec.Ecdsa.nBits C = 8 * Q)
    {h : List Byte} (hl : Q ≤ h.length) :
    Spec.Ecdsa.hashToInt C h = Spec.Weierstrass.ofBytes (h.take Q) := by
  have hd : (h.drop Q).length = h.length - Q := List.length_drop
  have key : Spec.Weierstrass.ofBytes h =
      Spec.Weierstrass.ofBytes (h.take Q) * 2 ^ (8 * (h.length - Q)) + Spec.Weierstrass.ofBytes (h.drop Q) := by
    conv => lhs; rw [← List.take_append_drop Q h]
    rw [ofBytes_append, hd, pow256]
  rw [Spec.Ecdsa.hashToInt, hq]
  by_cases hQ : h.length = Q
  · rw [show h.take Q = h from List.take_of_length_le (by omega), hQ]; simp
  · simp only [show ¬ 8 * h.length ≤ 8 * Q by omega, ite_false]
    rw [key, show 8 * h.length - 8 * Q = 8 * (h.length - Q) by omega, Nat.shiftRight_eq_div_pow,
      Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (by have := ofBytes_lt (h.drop Q); rwa [hd] at this), Nat.zero_add]

theorem rlenQ {C : Spec.Weierstrass.Curve} {Q : Nat} (hq : Spec.Ecdsa.nBits C = 8 * Q) :
    Spec.Ecdsa.Rfc6979.rlen C = Q := by
  rw [Spec.Ecdsa.Rfc6979.rlen, hq]; omega

theorem bits2octets_eqQ {C : Spec.Weierstrass.Curve} {Q : Nat} (hq : Spec.Ecdsa.nBits C = 8 * Q)
    {h : List Byte} (hl : Q ≤ h.length) :
    Spec.Ecdsa.Rfc6979.bits2octets C h =
      Spec.Weierstrass.toBytes Q (Spec.Weierstrass.ofBytes (h.take Q) % C.n) := by
  rw [Spec.Ecdsa.Rfc6979.bits2octets, Spec.Ecdsa.Rfc6979.int2octets, Spec.Ecdsa.Rfc6979.bits2int, rlenQ hq,
    hashToInt_takeQ hq hl]

/-- A number below `2^K < 2N` modulo `N`: itself if subtracting `N` borrows,
the difference `D` if not. -/
theorem mod_mathK (X N D K : Nat) (c : Bool) (hsum : D + N = X + 2 ^ K * c.toNat) (hD : D < 2 ^ K)
    (hX : X < 2 ^ K) (hN : 2 ^ K < 2 * N) : (if c then X else D) = X % N := by
  cases c
  · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hsum
    simp only [Bool.false_eq_true, ite_false]
    have hge : N ≤ X := by omega
    have hlt : X - N < N := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    omega
  · simp only [Bool.toNat_true, Nat.mul_one] at hsum
    simp only [ite_true]
    have hlt : X < N := by omega
    rw [Nat.mod_eq_of_lt hlt]

/-! ## At P-256 -/

theorem nBits_p256 : Spec.Ecdsa.nBits Spec.P256.curve = 256 := by
  have h₁ : 255 ≤ Spec.P256.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P256.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  show Spec.P256.curve.n.log2 + 1 = 256
  omega

theorem hashToInt_32 {h : List Byte} (hl : h.length = 32) :
    Spec.Ecdsa.hashToInt Spec.P256.curve h = Spec.Weierstrass.ofBytes h := by
  rw [Spec.Ecdsa.hashToInt, nBits_p256, hl]; rfl

/-- A hash of at least 32 bytes is the number of its leftmost 32. -/
theorem hashToInt_take {h : List Byte} (hl : 32 ≤ h.length) :
    Spec.Ecdsa.hashToInt Spec.P256.curve h = Spec.Weierstrass.ofBytes (h.take 32) := by
  have hd : (h.drop 32).length = h.length - 32 := List.length_drop
  have key : Spec.Weierstrass.ofBytes h =
      Spec.Weierstrass.ofBytes (h.take 32) * 2 ^ (8 * (h.length - 32)) + Spec.Weierstrass.ofBytes (h.drop 32) := by
    conv => lhs; rw [← List.take_append_drop 32 h]
    rw [ofBytes_append, hd, pow256]
  rw [Spec.Ecdsa.hashToInt, nBits_p256]
  by_cases h32 : h.length = 32
  · rw [show h.take 32 = h from List.take_of_length_le (by omega), h32]; rfl
  · simp only [show ¬ 8 * h.length ≤ 256 by omega, ite_false]
    rw [key, show 8 * h.length - 256 = 8 * (h.length - 32) by omega, Nat.shiftRight_eq_div_pow,
      Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (by have := ofBytes_lt (h.drop 32); rwa [hd] at this), Nat.zero_add]

theorem rlen_p256 : Spec.Ecdsa.Rfc6979.rlen Spec.P256.curve = 32 := by
  rw [Spec.Ecdsa.Rfc6979.rlen, nBits_p256]

theorem bits2octets_eq {h : List Byte} (hl : 32 ≤ h.length) :
    Spec.Ecdsa.Rfc6979.bits2octets Spec.P256.curve h =
      Spec.Weierstrass.toBytes 32 (Spec.Weierstrass.ofBytes (h.take 32) % Spec.P256.n) := by
  rw [Spec.Ecdsa.Rfc6979.bits2octets, Spec.Ecdsa.Rfc6979.int2octets, Spec.Ecdsa.Rfc6979.bits2int, rlen_p256,
    hashToInt_take hl]; rfl

/-- A number below `2^256 < 2N` modulo `N`: itself if subtracting `N` borrows, the
difference `D` if not. -/
theorem mod_math (X N D : Nat) (c : Bool) (hsum : D + N = X + 2 ^ 256 * c.toNat) (hD : D < 2 ^ 256)
    (hX : X < 2 ^ 256) (hN : 2 ^ 255 ≤ N) : (if c then X else D) = X % N := by
  cases c
  · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hsum
    simp only [Bool.false_eq_true, ite_false]
    have hge : N ≤ X := by omega
    have hlt : X - N < N := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    omega
  · simp only [Bool.toNat_true, Nat.mul_one] at hsum
    simp only [ite_true]
    have hlt : X < N := by omega
    rw [Nat.mod_eq_of_lt hlt]

end VG.Proof.Ecdsa.Rfc6979
