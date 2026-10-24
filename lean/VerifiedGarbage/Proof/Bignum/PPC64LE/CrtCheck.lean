module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The RSA private-key operation on PPC64LE: the checks

`checkN_ok`: the mask of whether `n` is valid. `checkLt_ok`: the mask of
whether one array is below another, and-ed in.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- Whether a word is zero, as a bit. -/
theorem isZero_bits (v : BitVec 64) :
    (((v >>> 1) ||| (v &&& 1#64)) - 1#64) >>> 63 = BitVec.ofNat 64 (if v = 0 then 1 else 0) := by
  by_cases h : v.toNat ≤ 1
  · rcases (show v = 0 ∨ v = 1 by
      rcases (show v.toNat = 0 ∨ v.toNat = 1 by omega) with h | h
      · exact Or.inl (BitVec.eq_of_toNat_eq h)
      · exact Or.inr (BitVec.eq_of_toNat_eq h)) with rfl | rfl <;> decide
  · have hu1 : 1 ≤ ((v >>> 1) ||| (v &&& 1#64)).toNat := by
      have := Nat.left_le_or (n := (v >>> 1).toNat) (m := (v &&& 1#64).toNat)
      rw [BitVec.toNat_or]
      have : (v >>> 1).toNat = v.toNat / 2 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      omega
    have hu2 : ((v >>> 1) ||| (v &&& 1#64)).toNat < 2 ^ 63 := by
      rw [BitVec.toNat_or]
      apply Nat.or_lt_two_pow
      · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := v.isLt; omega
      · rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have hv : v ≠ 0 := fun e => by subst e; simp at h
    simp only [hv, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    omega

/-- `checkN`: `r26 :=` all ones if the `k` bytes of `n` (at `N`, from the
header) are a valid modulus, else 0. -/
theorem checkN_ok {s : State} {S N : Addr} {Z k : Nat} {nb : List Byte} (hs : Scr s S Z) (hZ : 256 ≤ Z)
    (h23 : s.gpr .r23 = S) (hN : word s.mem S oN = off N 0) (hNL : word s.mem S oNLen = BitVec.ofNat 64 k)
    (hk : 64 ≤ k) (hk' : k ≤ 1024) (hlen : nb.length = k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1)
    (hb : ∀ i (h : i < k), s.mem (off N i) = nb[i]'(by omega)) :
    WP isa checkN s fun t =>
      (t.gpr .r26 = BitVec.ofNat 64 0 -
          BitVec.ofNat 64 (if Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k then 1 else 0) ∧ t.mem = s.mem) ∧
        Keep [.r0, .r3, .r4, .r6, .r12, .r15, .r16, .r18, .r26] s t := by
  have hnw := hs.nowrap
  unfold checkN
  refine WP.seq (WP.mono (WP.keep [.r12, .r6] (Q := fun t => t.gpr .r12 = off N 0 ∧
    t.gpr .r6 = BitVec.ofNat 64 k ∧ t.mem = s.mem) ?_ (by decide)) fun s₁ ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  · have hN' : s.mem.readW (off S 8) 64 = off N 0 := hN
    have hNL' : s.mem.readW (off S 16) 64 = BitVec.ofNat 64 k := hNL
    prun [h23, oN, oNLen, hs.ld (show 8 + 8 ≤ Z by omega), hs.ld (show 16 + 8 ≤ Z by omega), hN', hNL']
  refine WP.seq (WP.mono (check_ok (nb := nb) a12 a6 hk hk' hlen (by rw [k1.rd, k1.wr]; exact hrd)
    fun i hi => by rw [m1]; exact hb i hi) fun s₂ ⟨hv, m2, k2⟩ => ?_)
  refine WP.mono (WP.keep [.r3, .r4, .r26] (Q := fun t => t.gpr .r26 = BitVec.ofNat 64 0 -
    ((((s₂.gpr .r0 >>> 1) ||| (s₂.gpr .r0 &&& 1#64)) - 1#64) >>> 63) ∧ t.mem = s₂.mem) ?_ (by decide))
    fun t ⟨⟨t26, tm⟩, k3⟩ => ⟨⟨?_, tm.trans (m2.trans m1)⟩, ((k1.trans k2).trans k3).mono⟩
  · prun
  · rw [t26, isZero_bits]
    by_cases h0 : s₂.gpr .r0 = 0
    · simp only [h0, hv.mp h0, ↓reduceIte]
    · have h1 : ¬ Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true := fun h => h0 (hv.mpr h)
      simp only [h0, h1, Bool.false_eq_true, ↓reduceIte]

end VG.Proof.Bignum.PPC64LE.Crt
