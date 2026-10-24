module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Trial
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.RsaKeyGen.Trial32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Trial division on PPC64LE: one digit

`digit_ok`: one 32-bit digit `x` of the candidate reduced into the
accumulator by Montgomery's reduction by `2³²` (`redc32_math`): from
`acc < 2 s`, `acc' < 2 s` and `acc' 2³² ≡ x + acc (mod s)`. The model's
64-bit arithmetic is exact: `X = acc + x < 2³³` and `q s < 2⁴⁶` (`redc_word`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Trial

open VG VG.PPC64LE VG.Impl.RsaKeyGen.PPC64LE.Trial VG.Proof.Bignum.PPC64LE VG.Proof.Mont

/-- The reduction's value in 64-bit words: exact, since nothing overflows. -/
theorem redc_word {X s sv : Nat} (hX : X < 2 ^ 34) (hs : s < 2 ^ 14) :
    ((BitVec.ofNat 64 X * BitVec.ofNat 64 sv) <<< 32 >>> 32 * BitVec.ofNat 64 s + BitVec.ofNat 64 X) >>> 32 =
      BitVec.ofNat 64 ((X + X * sv % 2 ^ 32 * s) / 2 ^ 32) := by
  have hq : ((BitVec.ofNat 64 X * BitVec.ofNat 64 sv) <<< 32 >>> 32).toNat = X * sv % 2 ^ 32 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_mul_mod,
      show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from rfl, Nat.mul_mod_mul_right,
      Nat.mul_div_cancel _ (Nat.two_pow_pos 32), Nat.mod_eq_of_lt (show X < 2 ^ 32 * 2 ^ 32 by omega),
      Nat.mul_mod, Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right _ _), ← Nat.mul_mod]
  have hq' : X * sv % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hqs : X * sv % 2 ^ 32 * s < 2 ^ 46 := by
    calc X * sv % 2 ^ 32 * s < 2 ^ 32 * 2 ^ 14 := Nat.mul_lt_mul'' hq' hs
      _ = 2 ^ 46 := (Nat.pow_add 2 32 14).symm
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_mul, hq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show s < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show X < 2 ^ 64 by omega)]
  generalize X * sv % 2 ^ 32 * s = qs at hqs ⊢
  omega

/-- The registers `digit` writes. -/
def digitRegs : List Reg := [.r0, .r3, .r5, .r6]

/-- One digit `x` at `o + 4 j` into `acc`. -/
theorem digit_ok {u : State} {B : Addr} {Z o j s sv acc : Nat} (hs : Scr u B Z)
    (h5 : u.gpr .r5 = off B (o + 4 * j)) (h3 : u.gpr .r3 = BitVec.ofNat 64 acc)
    (h8 : u.gpr .r8 = BitVec.ofNat 64 s) (h9 : u.gpr .r9 = BitVec.ofNat 64 sv) (hacc : acc < 2 * s)
    (hs2 : 2 ≤ s) (hs' : s < 2 ^ 14) (hinv : (s * sv + 1) % 2 ^ 32 = 0) (hZ : o + 4 * j + 4 ≤ Z) :
    WP isa (.block digit) u fun t =>
      ((∃ r, t.gpr .r3 = BitVec.ofNat 64 r ∧ r < 2 * s ∧ r * 2 ^ 32 % s = (w32 u.mem B (o + 4 * j) + acc) % s) ∧
        t.gpr .r5 = off B (o + 4 * (j + 1)) ∧ t.mem = u.mem) ∧ Keep digitRegs u t := by
  refine WP.keep _ ?_ (by decide)
  have hld : InRegions (u.rd ++ u.wr) (off B (o + 4 * j)) 4 := hs.ld hZ
  have hx : w32 u.mem B (o + 4 * j) < 2 ^ 32 := (u.mem.readW (off B (o + 4 * j)) 32).isLt
  have eX : (u.mem.readW (off B (o + 4 * j)) 32).setWidth 64 + BitVec.ofNat 64 acc =
      BitVec.ofNat 64 (w32 u.mem B (o + 4 * j) + acc) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [w32]
    omega
  simp only [digit]
  prun [h5, h3, h8, h9, hld, BitVec.add_zero]
  rw [eX, redc_word (by omega) hs']
  obtain ⟨-, hlt, hcong⟩ := redc32_math (X := w32 u.mem B (o + 4 * j) + acc) hinv (by
    have : 2 ^ 32 + 2 * s ≤ s * 2 ^ 32 := by
      have : 2 * 2 ^ 32 ≤ s * 2 ^ 32 := Nat.mul_le_mul_right _ hs2
      omega
    omega)
  refine ⟨⟨_, rfl, hlt, hcong⟩, ?_⟩
  rw [show o + 4 * j + 4 = o + 4 * (j + 1) by omega]

end VG.Proof.RsaKeyGen.PPC64LE.Trial
