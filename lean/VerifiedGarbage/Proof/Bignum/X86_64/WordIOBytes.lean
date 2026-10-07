import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.X86_64.Sse

namespace VG.Proof.Bignum.X86_64.WordIO
open VG VG.X86_64 VG.Proof.Bignum

/-- Byte reversal maps byte `j` to byte `7-j`. -/
theorem bswap_byte (v : BitVec 64) {j : Nat} (hj : j < 8) :
    (bswap64 v).extractLsb' (8*j) 8 = v.extractLsb' (8*(7-j)) 8 := by
  ext r hr
  simp only [BitVec.getElem_extractLsb', bswap64, getLsbD_append_block _ _ _ hr]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    h | h | h | h | h | h | h | h <;> subst h <;>
  simp (disch := omega) only [↓reduceIte, Nat.reduceSub, Nat.reduceEqDiff, Nat.mul_zero, Nat.zero_add,
    Nat.reduceMul, BitVec.getLsbD_extractLsb', decide_eq_true, Bool.true_and, Nat.add_comm]

/-- An input byte is the corresponding radix-256 digit of OS2IP. -/
theorem os2ip_byte (bs : List Byte) {i : Nat} (hi : i < bs.length) :
    bs[i] = BitVec.ofNat 8 (Spec.Rsa.os2ip bs / 256^(bs.length-1-i)) := by
  have h := congrArg (fun xs : List Byte => xs[i]?) (VG.Proof.Rsa.i2osp_os2ip bs)
  simpa [Spec.Rsa.i2osp, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (show i < (List.range bs.length).length by simpa using hi)] using h.symm

/-- Extracting a byte of a word is division by its radix-256 position. -/
theorem extract_nat (x : Nat) {j : Nat} (hj : j < 8) :
    (BitVec.ofNat 64 x).extractLsb' (8*j) 8 = BitVec.ofNat 8 (x / 256^j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [show (2:Nat)^64 = 2^(8*j) * 2^(64-8*j) by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  rw [show (256:Nat)^j = 2^(8*j) by rw [show (256:Nat) = 2^8 from rfl, ← Nat.pow_mul]]

/-- Equality of all eight bytes is equality of words. -/
theorem eq_of_bytes {x y : BitVec 64}
    (h : ∀ j < 8, x.extractLsb' (8*j) 8 = y.extractLsb' (8*j) 8) : x = y := by
  ext i hi
  have e := congrArg (fun v : Byte => v.getLsbD (i%8)) (h (i/8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show i%8 < 8 from Nat.mod_lt _ (by decide),
    decide_true, Bool.true_and] at e
  rw [show 8*(i/8)+i%8 = i by omega] at e
  simpa only [BitVec.getLsbD_eq_getElem hi] using e

theorem read_digit {m : Mem} {src : Addr} {bs : List Byte} {q : Nat}
    (hq : 8*(q+1) ≤ bs.length)
    (hb : ∀ i (hi : i < bs.length), m (src + BitVec.ofNat 64 i) = bs[i]) :
    bswap64 (m.readW (src + BitVec.ofNat 64 (bs.length-8*(q+1))) 64) =
      BitVec.ofNat 64 (Spec.Rsa.os2ip bs / 256^(8*q)) := by
  apply eq_of_bytes
  intro j hj
  rw [bswap_byte _ hj, extract_nat _ hj]
  change (m.read (src + BitVec.ofNat 64 (bs.length-8*(q+1))) 8).extractLsb' (8*(7-j)) 8 = _
  rw [Mem.extractLsb'_read _ _ (by omega), BitVec.add_assoc, BitVec.ofNat_add_ofNat,
    hb _ (by omega), os2ip_byte]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3
  omega

end VG.Proof.Bignum.X86_64.WordIO
