module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# PPC64LE: constants built with `lis`, `ori`, `sldi` and `oris`

Untrusted: everything here is checked by Lean. A 64-bit constant is built as
`lis d, hi₁; ori d, d, lo₁; sldi d, d, 32; oris d, d, hi₀; ori d, d, lo₀`
(the high word, shifted up, then the low word), and a 32-bit one as `lis d,
hi; ori d, d, lo`, which leaves it in the low word (`lis` sign-extends).
These are the values those instructions leave.
-/

@[expose] public section

namespace VG.PPC64LE

/-- The five instructions of a 64-bit constant leave it in the register. -/
theorem movImm64_eq (x : BitVec 64) :
    ((x.extractLsb' 48 16 ++ (0 : BitVec 16)).signExtend 64 ||| (x.extractLsb' 32 16).setWidth 64) <<< 32 |||
      (x.extractLsb' 16 16).setWidth 64 <<< 16 ||| (x.extractLsb' 0 16).setWidth 64 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_signExtend, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h16 : i < 16
  · simp [h16, show i < 32 by omega, hi]
  by_cases h32 : i < 32
  · simp [h16, h32, hi, show i - 16 < 64 by omega, show i - 16 < 16 by omega,
      show 16 + (i - 16) = i by omega]
  by_cases h48 : i < 48
  · simp [h16, h32, hi, show i - 32 < 64 by omega, show i - 32 < 32 by omega,
      show i - 32 < 16 by omega, show ¬i - 16 < 16 by omega, show 32 + (i - 32) = i by omega]
  · simp [h16, h32, hi, show i - 32 < 64 by omega, show i - 32 < 32 by omega,
      show ¬i - 32 < 16 by omega, show i - 32 - 16 < 16 by omega, show ¬i - 16 < 16 by omega,
      show 48 + (i - 32 - 16) = i by omega]

/-- `lis` and `ori` of a 32-bit constant leave it in the low 32 bits. -/
theorem movImm32_eq (x : BitVec 32) :
    (((x.setWidth 64).extractLsb' 16 16 ++ (0 : BitVec 16)).signExtend 64 |||
      ((x.setWidth 64).extractLsb' 0 16).setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : i < 16
  · simp [h, show i < 32 from hi, show i < 64 by omega]
  · simp [h, show i < 32 from hi, show i < 64 by omega, show i - 16 < 16 by omega,
      show 16 + (i - 16) = i by omega]

end VG.PPC64LE
