import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Weierstrass.Words32

/-!
# Deterministic ECDSA: numbers of 32-bit words

The 32-bit targets' proofs of `bits2octets` (x86, 32-bit ARM) hold the
digest and `n` as eight 32-bit words, least significant first: their value
(`wsum`), `n`'s (`nW`, `nW_sum`), the selection of one number or
another by a mask, word by word (`sel_mask32`, `wsum_sel`), and the number
that `4 k` bytes are, big-endian, from the byte reversals of their words
(`ofBytes_words`).
-/

namespace VG.Proof.Ecdsa.Rfc6979

open VG

/-- The words of `n`, least significant first. -/
def nW (j : Nat) : BitVec 32 := BitVec.ofNat 32 (Spec.P256.n >>> (32 * j))

/-- The words `j < k` of a number, least significant first. -/
def wsum (f : Nat → BitVec 32) : Nat → Nat
  | 0 => 0
  | k + 1 => (f k).toNat * 2 ^ (32 * k) + wsum f k

theorem wsum_lt (f : Nat → BitVec 32) : ∀ k, wsum f k < 2 ^ (32 * k)
  | 0 => by simp [wsum]
  | k + 1 => by
    have := wsum_lt f k
    have := (f k).isLt
    simp only [wsum]
    rw [show 32 * (k + 1) = 32 + 32 * k by omega, Nat.pow_add]
    have h1 : (f k).toNat * 2 ^ (32 * k) ≤ (2 ^ 32 - 1) * 2 ^ (32 * k) := Nat.mul_le_mul_right _ (by omega)
    have h2 : (2 ^ 32 - 1) * 2 ^ (32 * k) + 2 ^ (32 * k) = 2 ^ 32 * 2 ^ (32 * k) := by
      rw [Nat.sub_mul, Nat.one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (by decide))]
    omega

/-- The 32-bit words of `N`, least significant first. -/
abbrev nWn (N j : Nat) : BitVec 32 := BitVec.ofNat 32 (N >>> (32 * j))

/-- The low `i` words of `N`. -/
theorem wsum_nWn (N : Nat) : ∀ i, wsum (nWn N) i = N % 2 ^ (32 * i)
  | 0 => by simp [wsum, Nat.mod_one]
  | i + 1 => by
    rw [wsum, wsum_nWn N i, show 32 * (i + 1) = 32 * i + 32 by omega, Nat.pow_add, Nat.mod_mul,
      BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mul_comm, Nat.add_comm]

theorem nW_sum : wsum nW 8 = Spec.P256.n := by
  simp only [wsum, nW]
  decide +kernel

theorem n_ge : 2 ^ 255 ≤ Spec.P256.n := by decide +kernel

theorem sel_mask32 (x d : BitVec 32) (c : Bool) :
    ((x ^^^ d) &&& (if c then BitVec.allOnes 32 else 0)) ^^^ d = if c then x else d := by
  cases c
  · simp
  · simp only [ite_true, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem wsum_sel (f g : Nat → BitVec 32) (c : Bool) :
    ∀ k, wsum (fun i => if c then f i else g i) k = if c then wsum f k else wsum g k := by
  intro k; cases c <;> simp

/-- The words of `4 k` bytes, each the byte reversal of a word, big-endian. -/
theorem ofBytes_words (m : Mem) (f : Nat → BitVec 32) : ∀ (p : Addr) (k : Nat),
    (∀ j < k, byteRev32 (m.readW (p + BitVec.ofNat 64 (4 * (k - 1 - j))) 32) = f j) →
    Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt m p (4 * k)) = wsum f k
  | _, 0, _ => rfl
  | p, k + 1, h => by
    have h0 := h k (by omega)
    simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.mul_zero, BitVec.add_zero] at h0
    rw [show 4 * (k + 1) = 4 + 4 * k by omega, Proof.Weierstrass.bytesAt_add,
      Proof.Weierstrass.ofBytes_append, Proof.Weierstrass.length_bytesAt,
      ofBytes_words m f (p + BitVec.ofNat 64 4) k fun j hj => by
        rw [Offset.add_add, show 4 + 4 * (k - 1 - j) = 4 * (k + 1 - 1 - j) by omega]; exact h j (by omega),
      ← Proof.Weierstrass.byteRev32_ofBytes, h0, wsum, show (256 : Nat) ^ (4 * k) = 2 ^ (32 * k) by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; congr 1; omega]

end VG.Proof.Ecdsa.Rfc6979
