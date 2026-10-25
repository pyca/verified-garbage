module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA public-key operation on PPC64LE: the exponent

`readE_ok`: `e`'s bytes into `r24`, saturated at `2^33` (`sat`).
`checkE_ok`: the mask of `Spec.Rsa.exponentValid` into `r26`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pub

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE.PublicChecked

/-- A number saturated at `2^33`. -/
def sat (v : Nat) : Nat := min v (2 ^ 33)

/-- A step of `readE`, on bit vectors: `acc 256 + b`, saturated. -/
theorem sat_step (acc : BitVec 64) (b : BitVec 64) (ha : acc.toNat ≤ 2 ^ 33) (hb : b.toNat < 256) :
    let a := acc <<< 8 ||| b
    let m := BitVec.ofNat 64 0 - (BitVec.ofNat 64 0 - a >>> 33) >>> 63
    (a ^^^ ((a ^^^ BitVec.ofNat 64 1 <<< 33) &&& m)).toNat = sat (acc.toNat * 256 + b.toNat) := by
  intro a m
  have hA : a.toNat = acc.toNat * 256 + b.toNat := by
    have e1 : (acc <<< 8).toNat = acc.toNat <<< 8 := by
      rw [BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega_arith)]
    simp only [a, BitVec.toNat_or, e1]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega_arith), Nat.shiftLeft_eq]
  have hT : (a >>> 33).toNat = a.toNat / 2 ^ 33 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases h : a.toNat < 2 ^ 33
  · have h0 : a >>> 33 = 0 := BitVec.eq_of_toNat_eq (by rw [hT]; simp; omega_arith)
    have hm : m = 0#64 := by simp only [m, h0]; rfl
    rw [hm, BitVec.and_zero, BitVec.xor_zero, hA]
    unfold sat; omega_arith
  · have hm : m = BitVec.allOnes 64 := by
      apply BitVec.eq_of_toNat_eq
      have h1 : ((BitVec.ofNat 64 0 - a >>> 33) >>> 63).toNat = 1 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, hT, BitVec.toNat_ofNat]
        omega_arith
      simp only [m, BitVec.toNat_sub, h1, BitVec.toNat_ofNat, BitVec.toNat_allOnes]
    rw [hm, BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    unfold sat; simp; omega_arith

theorem sat_snoc (v b : Nat) : sat (sat v * 256 + b) = sat (256 * v + b) := by
  unfold sat; omega_arith

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    Spec.Rsa.bytesAt m p (i + 1) = Spec.Rsa.bytesAt m p i ++ [m (off p i)] := by
  simp only [Spec.Rsa.bytesAt, List.range_succ, List.map_append, List.map_cons, List.map_nil, off]

/-- `readE`, `e`'s `L ≥ 1` bytes at `E` (`r7`, `r8`): `r24` is their number,
saturated at `2^33`. -/
theorem readE_ok {s : State} {E : Addr} {L : Nat} (h7 : s.gpr .r7 = off E 0)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L < 2 ^ 63)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off E i) 1) :
    WP isa readE s fun t =>
      (t.gpr .r24 = BitVec.ofNat 64 (sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem E L))) ∧ t.mem = s.mem) ∧
        Keep [.r0, .r3, .r4, .r7, .r8, .r24] s t := by
  unfold readE
  refine WP.seq ?_
  have hpre : WP isa (.block [.li .r24 0]) s fun s₁ =>
      (s₁.gpr .r24 = 0 ∧ s₁.mem = s.mem) ∧ Keep [.r24] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun
    rfl
  refine WP.mono hpre fun s₁ ⟨⟨i24, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r24 = BitVec.ofNat 64 (sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem E i))) ∧
      t.gpr .r7 = off E i ∧ t.mem = s.mem ∧ Keep [.r0, .r3, .r4, .r7, .r8, .r24] s t
  refine WP.mono (wp_countdown (cnt := .r8) (N := L) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨t24, t7, tm, tk⟩ hc => ?_)
    ⟨by rw [i24]; rfl, by rw [k₁.gpr .r7 (by decide), h7], im, k₁.mono⟩ ((k₁.gpr .r8 (by decide)).trans h8))
    fun t ⟨t24, _, tm, tk⟩ => ⟨⟨t24, tm⟩, tk⟩
  have hb : InRegions (t.rd ++ t.wr) (off E i) 1 := by rw [tk.rd, tk.wr]; exact hrd i hi
  refine WP.mono (WP.keep [.r0, .r3, .r4, .r7, .r8, .r24] (Q := fun t' =>
    t'.gpr .r24 = BitVec.ofNat 64 (sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem E (i + 1)))) ∧
      t'.gpr .r7 = off E (i + 1) ∧ t'.mem = t.mem ∧ t'.gpr .r8 = t.gpr .r8 - BitVec.ofNat 64 1) ?_ (by decide))
    fun t' ⟨⟨a, b, c, d⟩, k⟩ => ⟨⟨a, b, c.trans tm, tk.trans' k⟩, d⟩
  prun [t7, t24, exec_lbz' (show Reg.r7 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
    hb, read_byte64]
  have hbt := (t.mem (off E i)).isLt
  have hs := Nat.min_le_right (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem E i)) (2 ^ 33)
  apply BitVec.eq_of_toNat_eq
  rw [sat_step _ _ (by rw [BitVec.toNat_ofNat]; unfold sat; omega_arith) (by rw [BitVec.toNat_ofNat]; omega_arith),
    bytesAt_succ, VG.Proof.Rsa.os2ip_snoc, tm]
  simp only [BitVec.toNat_ofNat]
  unfold sat at hs ⊢
  omega_arith

theorem odd_bit (E : Nat) : BitVec.ofNat 64 E &&& 1#64 = BitVec.ofNat 64 (E % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1#64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_ofNat]
  omega_arith

theorem ge3_bit {E : Nat} (hE : E ≤ 2 ^ 33) :
    (BitVec.ofNat 64 E - 3#64) >>> 63 ^^^ 1#64 = BitVec.ofNat 64 (if 3 ≤ E then 1 else 0) := by
  have e : (BitVec.ofNat 64 E - 3#64) >>> 63 = BitVec.ofNat 64 (if 3 ≤ E then 0 else 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    split <;> omega_arith
  rw [e]
  split <;> decide

theorem lt_bit {E : Nat} (hE : E ≤ 2 ^ 33) :
    (BitVec.ofNat 64 E - 1#64 <<< 33) >>> 63 = BitVec.ofNat 64 (if E < 2 ^ 33 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub,
    show (1#64 <<< 33).toNat = 2 ^ 33 from rfl]
  simp only [BitVec.toNat_ofNat]
  split <;> omega_arith

theorem valid_bits {E : Nat} (hE : E ≤ 2 ^ 33) :
    BitVec.ofNat 64 E &&& 1#64 &&& ((BitVec.ofNat 64 E - 3#64) >>> 63 ^^^ 1#64) &&&
        (BitVec.ofNat 64 E - 1#64 <<< 33) >>> 63 =
      BitVec.ofNat 64 (if Spec.Rsa.exponentValid E then 1 else 0) := by
  rw [odd_bit, ge3_bit hE, lt_bit hE]
  simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  rcases Nat.mod_two_eq_zero_or_one E with h | h <;> rw [h] <;>
    by_cases h3 : 3 ≤ E <;> by_cases h33 : E < 2 ^ 33 <;> simp [h3, h33] <;> decide

/-- `checkE`, `r24` a number at most `2^33`: the mask of whether it is a valid
exponent in `r26`, and its bit 32 at the top of `r24`. -/
theorem checkE_ok {s : State} {E : Nat} (h24 : s.gpr .r24 = BitVec.ofNat 64 E) (hE : E ≤ 2 ^ 33) :
    WP isa (.block checkE) s fun t =>
      (t.gpr .r26 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if Spec.Rsa.exponentValid E then 1 else 0) ∧
        t.gpr .r24 = BitVec.ofNat 64 E <<< 31 ∧ t.mem = s.mem) ∧ Keep [.r0, .r3, .r4, .r24, .r26] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold checkE
  prun [h24, valid_bits hE]

end VG.Proof.Bignum.PPC64LE.Pub
