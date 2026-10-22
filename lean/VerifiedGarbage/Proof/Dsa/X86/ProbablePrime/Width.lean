module

public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Environment

/-! # The geometry of a candidate of `bits` bits -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG.Impl.Dsa.X86.ProbablePrime

theorem Bits.width_low {bits : Nat} (_ : Bits bits) : 4 ≤ width bits := by
  unfold width; omega

theorem Bits.width_high {bits : Nat} (b : Bits bits) : width bits ≤ 64 := by
  have := b.high
  unfold width; omega

theorem Bits.words_two {bits : Nat} (b : Bits bits) : 2 ≤ bits / 32 := by
  have := b.low; omega

theorem Bits.words_le {bits : Nat} (b : Bits bits) : bits / 32 ≤ 2 * width bits := by
  have := b.whole
  unfold width; omega

theorem Bits.bytes_eq {bits : Nat} (b : Bits bits) : 4 * (bits / 32) = bits / 8 := by
  have := b.whole; omega

theorem Bits.draw_le {bits : Nat} (_ : Bits bits) : 8 * ((bits + 63) / 64) ≤ 8 * width bits := by
  unfold width; omega

theorem Bits.draw_ge {bits : Nat} (b : Bits bits) : 4 * (bits / 32) ≤ 8 * ((bits + 63) / 64) := by
  have := b.whole; omega

theorem Environment.Valid.width_low {E : Environment} (v : E.Valid) : 4 ≤ E.width := v.bits.width_low

theorem Environment.Valid.width_high {E : Environment} (v : E.Valid) : E.width ≤ 64 := v.bits.width_high

theorem Environment.Valid.words_le {E : Environment} (v : E.Valid) : E.words ≤ 2 * E.width := v.bits.words_le

theorem Environment.Valid.words_two {E : Environment} (v : E.Valid) : 2 ≤ E.words := v.bits.words_two

end VG.Proof.Dsa.X86.ProbablePrime
