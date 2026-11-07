module
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Bignum.ExponentCheckMath
public import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
public import VerifiedGarbage.Proof.Bignum.ExponentWords

import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Save a validated exponent and derive the public limb count -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem saveExponent_ok {s : State} {base : Addr} {bytes e : Nat}
    (hs : Scr s base bytes) (hb : 136 ≤ bytes) (he : e < 2 ^ 33)
    (lo : s.gpr .ebx = BitVec.ofNat 32 (e % 2 ^ 32))
    (hi : s.gpr .edx = BitVec.ofNat 32 (exponentHigh e)) :
    WP isa (.block PublicFn.saveExponent) s fun t =>
      val32 t.mem base 128 2 = e ∧ Outside base 128 8 s.mem t.mem ∧ Keeps [] s t := by
  unfold PublicFn.saveExponent
  refine wp_storeS (hs.ea (by omega)) (hs.write (by omega)) fun u A => ?_
  have hu := hs.of_keeps (A.keeps []) (by decide)
  refine wp_storeS (hu.ea (by omega)) (hu.write (by omega)) fun t B => WP.block_nil ?_
  have Oa : Outside base 128 4 s.mem u.mem := by rw [A.mem]; exact writeW32_outside _ _ _ (by decide)
  have Ob : Outside base 132 4 u.mem t.mem := by rw [B.mem]; exact writeW32_outside _ _ _ (by decide)
  refine ⟨?_, (Oa.mono (by omega) (by omega)).trans (Ob.mono (by omega) (by omega)),
    (A.keeps []).trans (B.keeps [])⟩
  have low : w32 t.mem base 128 = e % 2 ^ 32 := by
    rw [Outside.w32 Ob (.inl (by decide)) (by decide), A.mem, w32_write_self, lo, BitVec.toNat_ofNat,
      Nat.mod_mod]
  have high : w32 t.mem base 132 = e / 2 ^ 32 := by
    rw [B.mem, w32_write_self, A.gpr, hi, BitVec.toNat_ofNat]
    unfold exponentHigh
    omega
  simp only [val32, Nat.mul_zero, Nat.add_zero]
  change w32 t.mem base 128 + 2 ^ 32 * w32 t.mem base 132 = e
  rw [low, high]
  omega

end VG.Proof.Bignum.X86
