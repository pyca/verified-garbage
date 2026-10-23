module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The precomputed values of an RSA modulus on PPC64LE: the function

`setup_ok`: `w`, the arrays' bases and `2 w`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pre

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Precompute

theorem ofNat_add7_shr3 (k : Nat) (hk : k < 2 ^ 32) :
    (BitVec.ofNat 64 k + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((k + 7) / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega

theorem ofNat_shl3 (a : Nat) : BitVec.ofNat 64 a <<< 3 = BitVec.ofNat 64 (8 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem ofNat_shl1 (a : Nat) : BitVec.ofNat 64 a <<< 1 = BitVec.ofNat 64 (2 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- `setup`, `n` at `r5`, `k` in `r6` and the working space at `r21`. -/
theorem setup_ok {s : State} {N S : Addr} {Z k : Nat} (hs : Scr s S Z) (h5 : s.gpr .r5 = N)
    (h6 : s.gpr .r6 = BitVec.ofNat 64 k) (h21 : s.gpr .r21 = S) (hk : 1 ≤ k) (hk' : k ≤ 1024)
    (hZ : 56 ≤ Z) :
    WP isa (.block setup) s fun t =>
      (t.gpr .r12 = N ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * ((k + 7) / 8)) ∧
        t.gpr .r10 = off S (slot ((k + 7) / 8) 0) ∧ t.gpr .r5 = off S (slot ((k + 7) / 8) 1) ∧
        t.gpr .r8 = off S (slot ((k + 7) / 8) 2) ∧ t.gpr .r9 = off S (slot ((k + 7) / 8) 3) ∧
        t.mem = s.mem.writeW (off S 48) (BitVec.ofNat 64 ((k + 7) / 8))) ∧
      Keep [.r4, .r5, .r8, .r9, .r10, .r11, .r12] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold setup
  prun [h5, h6, h21, BitVec.add_zero, ofNat_add7_shr3 k (by omega), ofNat_shl3, ofNat_shl1, sW, hdrBytes, Nat.reduceMul, hs.st (d := 48) (n := 8) (by omega)]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [off, slot, hdrBytes, BitVec.add_assoc, BitVec.ofNat_add_ofNat] <;>
    congr 2 <;> omega

end VG.Proof.Bignum.PPC64LE.Pre
