module

public import VerifiedGarbage.Proof.Mont.X86.WindowWords
public import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.Words32

/-! # The window's exponent words: their top four bits, and the arithmetic of their shift -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86

theorem times2_toNat (x : BitVec 32) : (x+x).toNat = x.toNat*2%2^32 := by
  rw [BitVec.toNat_add]; congr 1; omega

theorem shr31_toNat (x : BitVec 32) : (x >>> 31).toNat = x.toNat / 2 ^ 31 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- `(V + P w) · 2 mod P 2³²`, for `V < P`: the low part times 2 mod `P`, and
the top word times 2 mod 2³² with the four bits carried up from below. -/
theorem shift_top_one {V P w : Nat} (hP : 0 < P) (hV : V < P) :
    (V + P * w) * 2 % (P * 2 ^ 32) = V * 2 % P + P * (w * 2 % 2 ^ 32 + V * 2 / P) :=
  shift_top_scale (by decide) (by decide) hP hV

theorem val32_top_bit (m : Mem) (base : Addr) (d j : Nat) :
    val32 m base d (j + 1) * 2 / 2 ^ (32 * (j + 1)) = w32 m base (d + 4 * j) / 2 ^ 31 := by
  have hP : 0 < 2 ^ (32 * j) := Nat.two_pow_pos _
  have hV := val32_lt m base d j
  have hq : val32 m base d j * 2 / 2 ^ (32 * j) < 2 := (Nat.div_lt_iff_lt_mul hP).2 (by omega)
  rw [val32_succ, pow32_succ, Nat.mul_comm (2 ^ 32), ← Nat.div_div_eq_div_mul, Nat.add_mul,
    Nat.mul_assoc, Nat.add_mul_div_left _ _ hP]
  generalize val32 m base d j * 2 / 2 ^ (32 * j) = q at hq
  omega


end VG.Proof.Mont.X86.Dynamic
