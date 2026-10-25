module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Trial
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.RsaKeyGen.Trial64
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Trial division on PPC64LE: one word

`digit_ok`: one 64-bit word `x` of the candidate reduced into the
accumulator by Montgomery's reduction by `2⁶⁴` (`redc64_math`): from `acc <
2 s`, `acc' < 2 s` and `acc' 2⁶⁴ ≡ x + acc (mod s)`. The carries make the
sum exact (`redc_word`): `X = acc + x` is `c 2⁶⁴ + X₀`, and `X₀` plus the low
word of `q s` is a multiple of `2⁶⁴`, so `(X + q s) / 2⁶⁴` is the high word of
`q s` plus `c` plus that sum's carry.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Trial

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Impl.RsaKeyGen.PPC64LE.Trial VG.Proof.Bignum.PPC64LE VG.Proof.Mont

/-- The reduction's value in 64-bit words, through the carries: `(X + q s) /
2⁶⁴` for `X = x + acc` and `q = X m' mod 2⁶⁴`, when `X + q s` is a multiple
of `2⁶⁴` and `q s` (`s < 2⁶³`) leaves room for the carries in its high word. -/
theorem redc_word (x a s m : BitVec 64) (hs : s.toNat < 2 ^ 63)
    (hd : (x.toNat + a.toNat + (x.toNat + a.toNat) * m.toNat % 2 ^ 64 * s.toNat) % 2 ^ 64 = 0) :
    (BitVec.ofNat 64 ((BitVec.ofNat 64 ((BitVec.ofNat 64 (x.toNat + a.toNat) * m).toNat * s.toNat / 2 ^ 64)).toNat +
        (decide (2 ^ 64 ≤ x.toNat + a.toNat)).toNat)).toNat +
      (decide (2 ^ 64 ≤ (BitVec.ofNat 64 (x.toNat + a.toNat) * m * s).toNat +
        (BitVec.ofNat 64 (x.toNat + a.toNat)).toNat)).toNat =
      (x.toNat + a.toNat + (x.toNat + a.toNat) * m.toNat % 2 ^ 64 * s.toNat) / 2 ^ 64 := by
  have hx := x.isLt
  have ha := a.isLt
  have hm := m.isLt
  have hq : (BitVec.ofNat 64 (x.toNat + a.toNat) * m).toNat = (x.toNat + a.toNat) * m.toNat % 2 ^ 64 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_mul_mod]
  have hqs : (BitVec.ofNat 64 (x.toNat + a.toNat) * m * s).toNat = (x.toNat + a.toNat) * m.toNat % 2 ^ 64 *
      s.toNat % 2 ^ 64 := by rw [BitVec.toNat_mul, hq]
  rw [hqs, hq]
  have hql : (x.toNat + a.toNat) * m.toNat % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hXl : x.toNat + a.toNat < 2 ^ 65 := by omega
  generalize (x.toNat + a.toNat) * m.toNat % 2 ^ 64 = q at *
  have hP : q * s.toNat < 2 ^ 64 * 2 ^ 63 := Nat.mul_lt_mul'' hql hs
  generalize q * s.toNat = P at *
  generalize x.toNat + a.toNat = X at *
  simp only [BitVec.toNat_ofNat]
  by_cases h1 : 2 ^ 64 ≤ X <;> by_cases h2 : 2 ^ 64 ≤ P % 2 ^ 64 + X % 2 ^ 64 <;>
    simp only [h1, h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- The registers `digit` writes. -/
def digitRegs : List Reg := [.r0, .r3, .r5, .r6, .r7]

/-- One word `x` at `o + 8 j` into `acc`. -/
theorem digit_ok {u : State} {B : Addr} {Z o j s acc : Nat} {m : BitVec 64} (hs : Scr u B Z)
    (h5 : u.gpr .r5 = off B (o + 8 * j)) (h3 : u.gpr .r3 = BitVec.ofNat 64 acc)
    (h8 : u.gpr .r8 = BitVec.ofNat 64 s) (h9 : u.gpr .r9 = m) (hacc : acc < 2 * s)
    (hs2 : 2 ≤ s) (hs' : s < 2 ^ 14) (hinv : (s * m.toNat + 1) % 2 ^ 64 = 0)
    (hZ : o + 8 * j + 8 ≤ Z) :
    WP isa (.block digit) u fun t =>
      ((∃ r, t.gpr .r3 = BitVec.ofNat 64 r ∧ r < 2 * s ∧
        r * 2 ^ 64 % s = ((word u.mem B (o + 8 * j)).toNat + acc) % s) ∧
        t.gpr .r5 = off B (o + 8 * (j + 1)) ∧ t.mem = u.mem) ∧ Keep digitRegs u t := by
  refine WP.keep _ ?_ (by decide)
  simp only [digit]
  mcrun [h5, h3, h8, h9, hs.ld hZ, BitVec.add_zero]
  have ea : (BitVec.ofNat 64 acc).toNat = acc := by rw [BitVec.toNat_ofNat]; omega
  have es : (BitVec.ofNat 64 s).toNat = s := by rw [BitVec.toNat_ofNat]; omega
  have hx := (word u.mem B (o + 8 * j)).isLt
  obtain ⟨hd, hlt, hcong⟩ := VG.Proof.RsaKeyGen.redc64_math (X := (word u.mem B (o + 8 * j)).toNat + acc) hinv (by
    have : 2 * 2 ^ 64 ≤ s * 2 ^ 64 := Nat.mul_le_mul_right _ hs2
    omega)
  have hw := redc_word (word u.mem B (o + 8 * j)) (BitVec.ofNat 64 acc) (BitVec.ofNat 64 s) m
    (by rw [es]; omega) (by rw [ea, es]; exact hd)
  simp only [Nat.reducePow, word] at hw
  rw [hw, ea, es]
  exact ⟨⟨_, rfl, hlt, hcong⟩, by rw [Nat.mul_succ, Nat.add_assoc]⟩

end VG.Proof.RsaKeyGen.PPC64LE.Trial
