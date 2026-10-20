module

import VerifiedGarbage.Proof.Bignum.Arm.WideMath
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The word-level value of ARMv7's full product -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (mask16 toNat_and_mask16 toNat_shr toNat_shl toNat_add_lt toNat_mul_lt)

/-- Four 16-bit partial products give the exact 64-bit result. All
intermediate additions are bounded before interpreting the word operations. -/
theorem wide_value (x y : BitVec 32) :
    let a0 := x &&& mask16
    let a1 := x >>> 16
    let b0 := y &&& mask16
    let b1 := y >>> 16
    let p := a0 * b0
    let t := a1 * b0 + (p >>> 16)
    let u := a0 * b1 + (t &&& mask16)
    ((p &&& mask16) + (u <<< 16)).toNat +
      (a1 * b1 + (t >>> 16) + (u >>> 16)).toNat * 2 ^ 32 = x.toNat * y.toNat := by
  let a0 := x &&& mask16
  let a1 := x >>> 16
  let b0 := y &&& mask16
  let b1 := y >>> 16
  let p := a0 * b0
  let t := a1 * b0 + (p >>> 16)
  let u := a0 * b1 + (t &&& mask16)
  change ((p &&& mask16) + (u <<< 16)).toNat +
    (a1 * b1 + (t >>> 16) + (u >>> 16)).toNat * 2 ^ 32 = _
  have ha0 : a0.toNat < 65536 := by rw [toNat_and_mask16]; omega
  have ha1 : a1.toNat < 65536 := by rw [toNat_shr]; have := x.isLt; omega
  have hb0 : b0.toNat < 65536 := by rw [toNat_and_mask16]; omega
  have hb1 : b1.toNat < 65536 := by rw [toNat_shr]; have := y.isLt; omega
  have hx : a0.toNat + a1.toNat * 65536 = x.toNat := by
    rw [toNat_and_mask16, toNat_shr]; omega
  have hy : b0.toNat + b1.toNat * 65536 = y.toNat := by
    rw [toNat_and_mask16, toNat_shr]; omega
  obtain ⟨hp, ht, hu, hh⟩ := wide_bounds ha0 ha1 hb0 hb1
  have pval : p.toNat = a0.toNat * b0.toNat := toNat_mul_lt hp
  have ab : a1.toNat * b0.toNat < 2 ^ 32 := by omega
  have tval : t.toNat = a1.toNat * b0.toNat + a0.toNat * b0.toNat / 65536 := by
    change (a1 * b0 + (p >>> 16)).toNat = _
    rw [toNat_add_lt (by rw [toNat_mul_lt ab, toNat_shr p 16, pval]; exact ht),
      toNat_mul_lt ab, toNat_shr p 16, pval]
  have ac : a0.toNat * b1.toNat < 2 ^ 32 := by omega
  have uval : u.toNat = a0.toNat * b1.toNat +
      (a1.toNat * b0.toNat + a0.toNat * b0.toNat / 65536) % 65536 := by
    change (a0 * b1 + (t &&& mask16)).toNat = _
    rw [toNat_add_lt (by rw [toNat_mul_lt ac, toNat_and_mask16 t, tval]; exact hu),
      toNat_mul_lt ac, toNat_and_mask16 t, tval]
  have ad : a1.toNat * b1.toNat < 2 ^ 32 := by omega
  have hval : (a1 * b1 + (t >>> 16)).toNat = a1.toNat * b1.toNat +
      (a1.toNat * b0.toNat + a0.toNat * b0.toNat / 65536) / 65536 := by
    rw [toNat_add_lt (by rw [toNat_mul_lt ad, toNat_shr t 16, tval]; omega),
      toNat_mul_lt ad, toNat_shr t 16, tval]
  rw [toNat_add_lt (x := a1 * b1 + _) (by rw [hval, toNat_shr u 16, uval]; exact hh),
    hval, toNat_shr u 16, uval]
  rw [BitVec.toNat_add, toNat_and_mask16 p, pval, toNat_shl u 16, uval]
  have he := wide_product a0.toNat a1.toNat b0.toNat b1.toNat
  rw [hx, hy] at he
  have hlo : (a0.toNat * b0.toNat % 65536 +
      (a0.toNat * b1.toNat + (a1.toNat * b0.toNat + a0.toNat * b0.toNat / 65536) % 65536) * 2 ^ 16 % 2 ^ 32) % 2 ^ 32 =
      a0.toNat * b0.toNat % 65536 +
        (a0.toNat * b1.toNat + (a1.toNat * b0.toNat + a0.toNat * b0.toNat / 65536) % 65536) % 65536 * 65536 := by omega
  rw [hlo]
  exact he

end VG.Proof.Bignum.Arm
