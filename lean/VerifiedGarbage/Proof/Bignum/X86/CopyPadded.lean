module

public import VerifiedGarbage.Impl.Bignum.X86.CopyPadded
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Bignum.X86.CopyArray
import VerifiedGarbage.Proof.Mont.X86.WordOps

/-! # A padded transfer retains both the narrow and double-width integer values -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem copyPadded_ok {s : State} {base : Addr} {bytes n src dst : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hsrc : src + 8 * n ≤ bytes) (hdst : dst + 16 * n ≤ bytes)
    (apart : dst + 16 * n ≤ src ∨ src + 8 * n ≤ dst) :
    WP isa (copyPadded n src dst) s fun t =>
      wordsVal t.mem base dst n = wordsVal s.mem base src n ∧
      wordsVal t.mem base dst (2 * n) = wordsVal s.mem base src n ∧
      Outside base dst (16 * n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  unfold copyPadded
  refine WP.seq (WP.mono (zerosW_ok hs (by omega) (by omega)) fun u ⟨O, Z, K⟩ => ?_)
  have Src : wordsVal u.mem base src n = wordsVal s.mem base src n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact O.val32 (by omega) (by have := hs.nowrap; omega)
  have Upper : val32 u.mem base (dst + 8 * n) (2 * n) = 0 := by
    have S := val32_append u.mem base dst (2 * n) (2 * n)
    rw [show 2 * n + 2 * n = 4 * n by omega, Z] at S
    have Pos := Nat.two_pow_pos (32 * (2 * n))
    have Eq : dst + 4 * (2 * n) = dst + 8 * n := by omega
    rw [Eq] at S
    by_contra H
    have positive : 1 ≤ val32 u.mem base (dst + 8 * n) (2 * n) := by omega
    have := Nat.mul_le_mul_left (2 ^ (32 * (2 * n))) positive
    omega
  refine WP.mono (copyArray_ok (hs.of_keeps K (by decide)) hn hsrc (by omega) (by omega))
    fun t ⟨V, Ot, Kt⟩ => ?_
  refine ⟨V.trans Src, ?_, ?_, (K.mono (by decide)).trans Kt⟩
  · rw [wordsVal_eq_val32, show 2 * (2 * n) = 2 * n + 2 * n by omega, val32_append,
      show dst + 4 * (2 * n) = dst + 8 * n by omega,
      Ot.val32 (d := dst + 8 * n) (k := 2 * n) (by omega) (by have := hs.nowrap; omega),
      Upper, Nat.mul_zero, Nat.add_zero, ← wordsVal_eq_val32, V, Src]
  · have O' : Outside base dst (16 * n) s.mem u.mem := by
      simpa only [show 4 * (4 * n) = 16 * n by omega] using O
    exact O'.trans (Ot.mono (Nat.le_refl _) (by omega))

end VG.Proof.Bignum.X86
