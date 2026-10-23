module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul
import VerifiedGarbage.Proof.Bignum.Fios32
import VerifiedGarbage.Proof.Framework.Offset

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE

theorem toNat_ext32 (v : BitVec 32) : (v.setWidth 64).toNat = v.toNat := by
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide : 2 ^ 32 < 2 ^ 64))]

theorem toNat_add_lt {x y : BitVec 64} (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem toNat_mul_lt {x y : BitVec 64} (h : x.toNat * y.toNat < 2 ^ 64) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

theorem toNat_shr32 (x : BitVec 64) : (x >>> 32).toNat = x.toNat / 2 ^ 32 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_lo32 (x : BitVec 64) : ((x.setWidth 32).setWidth 64).toNat = x.toNat % 2 ^ 32 := by
  rw [toNat_ext32, BitVec.toNat_setWidth]

theorem lo32_ofNat (x : BitVec 64) : x.setWidth 32 = BitVec.ofNat 32 x.toNat := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

/-- The arithmetic of a digit step, on bit vectors: `x = t + a b + c₁`, `y = x
mod 2³² + u m + c₂`. -/
theorem mac2 (t b m : BitVec 32) (a u c₁ c₂ : BitVec 64) (ha : a.toNat < 2 ^ 32)
    (hu : u.toNat < 2 ^ 32) (hc1 : c₁.toNat < 2 ^ 32) (hc2 : c₂.toNat < 2 ^ 32) :
    let X := t.setWidth 64 + a * b.setWidth 64 + c₁
    let Y := (X.setWidth 32 >>> 0).setWidth 64 + u * m.setWidth 64 + c₂
    let x := t.toNat + a.toNat * b.toNat + c₁.toNat
    let y := x % 2 ^ 32 + u.toNat * m.toNat + c₂.toNat
    (X >>> 32).toNat = x / 2 ^ 32 ∧ (Y >>> 32).toNat = y / 2 ^ 32 ∧
      Y.setWidth 32 = BitVec.ofNat 32 y := by
  intro X Y x y
  have ht := t.isLt
  have hb := b.isLt
  have hm := m.isLt
  have e1 := Fios32.mac_lt ha hb ht hc1
  have hx := Nat.mod_lt x (show 0 < 2 ^ 32 by decide)
  have e2 := Fios32.mac_lt hu hm hx hc2
  have p1 : (a * b.setWidth 64).toNat = a.toNat * b.toNat := by
    rw [toNat_mul_lt] <;> rw [toNat_ext32]; omega
  have p2 : (u * m.setWidth 64).toNat = u.toNat * m.toNat := by
    rw [toNat_mul_lt] <;> rw [toNat_ext32]; omega
  have s1 : (t.setWidth 64 + a * b.setWidth 64).toNat = t.toNat + a.toNat * b.toNat := by
    rw [toNat_add_lt (by rw [toNat_ext32, p1]; omega), toNat_ext32, p1]
  have vx : X.toNat = x := by
    simp only [X, x]
    rw [toNat_add_lt (by rw [s1]; omega), s1]
  have s2 : ((X.setWidth 32).setWidth 64 + u * m.setWidth 64).toNat = x % 2 ^ 32 + u.toNat * m.toNat := by
    rw [toNat_add_lt (by rw [toNat_lo32, vx, p2]; omega), toNat_lo32, vx, p2]
  have vy : Y.toNat = y := by
    simp only [Y, y]
    rw [BitVec.ushiftRight_zero, toNat_add_lt (by rw [s2]; omega), s2]
  refine ⟨by rw [toNat_shr32, vx], by rw [toNat_shr32, vy], ?_⟩
  rw [lo32_ofNat, vy]

/-- The registers a digit step writes. -/
def stepRegs : List Reg := [.r0, .r3, .r14, .r15, .r16, .r20, .r22]

/-- A digit step (`step`), the pointers at digit `j - 1` (byte offsets `dA`,
`dB`, `dM` of `B`): with `x = tⱼ + aᵢ bⱼ + c₁` and `y = x mod 2³² + u mⱼ +
c₂`, the carries `x / 2³²` and `y / 2³²`, the digit `y mod 2³²` stored at
`dA`, and the pointers advanced. -/
theorem step_ok {s : State} {B : Addr} {Z dA dB dM : Nat} (hs : Scr s B Z)
    (h14 : s.gpr .r14 = off B dA) (h15 : s.gpr .r15 = off B dB) (h16 : s.gpr .r16 = off B dM)
    (hA : dA + 8 ≤ Z) (hB : dB + 8 ≤ Z) (hM : dM + 8 ≤ Z)
    (ha : (s.gpr .r18).toNat < 2 ^ 32) (hu : (s.gpr .r19).toNat < 2 ^ 32)
    (hc1 : (s.gpr .r20).toNat < 2 ^ 32) (hc2 : (s.gpr .r22).toNat < 2 ^ 32) :
    WP isa (.block step) s fun s' =>
      let x := w32 s.mem B (dA + 4) + (s.gpr .r18).toNat * w32 s.mem B (dB + 4) + (s.gpr .r20).toNat
      let y := x % 2 ^ 32 + (s.gpr .r19).toNat * w32 s.mem B (dM + 4) + (s.gpr .r22).toNat
      (s'.gpr .r14 = off B (dA + 4) ∧ s'.gpr .r15 = off B (dB + 4) ∧ s'.gpr .r16 = off B (dM + 4) ∧
        (s'.gpr .r20).toNat = x / 2 ^ 32 ∧ (s'.gpr .r22).toNat = y / 2 ^ 32 ∧
        s'.mem = s.mem.writeW (off B dA) (BitVec.ofNat 32 y)) ∧ Keep stepRegs s s' := by
  refine WP.keep stepRegs ?_ (by decide)
  unfold step
  prun [h14, h15, h16, hs.ld (show dA + 4 + 4 ≤ Z by omega), hs.ld (show dB + 4 + 4 ≤ Z by omega),
    hs.ld (show dM + 4 + 4 ≤ Z by omega), hs.st (show dA + 4 ≤ Z by omega)]
  obtain ⟨k1, k2, k3⟩ := mac2 (s.mem.readW (off B (dA + 4)) 32) (s.mem.readW (off B (dB + 4)) 32)
    (s.mem.readW (off B (dM + 4)) 32) _ _ _ _ ha hu hc1 hc2
  exact ⟨k1, k2, by rw [k3]⟩

end VG.Proof.Bignum.PPC64LE
