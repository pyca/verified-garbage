module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.FastR2
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.WordConst
public import VerifiedGarbage.Proof.Mont.Words

/-! # The top-bit seed is a reduced residue for an odd full-width candidate -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.FastR2
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.FastR2

theorem seed_lt {n m : Nat} (positive : 0 < n) (odd : m % 2 = 1)
    (top : 2 ^ (64 * n - 1) ≤ m) : 2 ^ (64 * n - 1) < m := by
  have even : 2 ^ (64 * n - 1) % 2 = 0 := by
    rw [show 64 * n - 1 = (64 * n - 2) + 1 by omega, Nat.pow_succ, Nat.mul_mod_left]
  omega

theorem seed_ok {s : State} {base : Addr} {size n out : Nat} (scratch : Scr s base size)
    (positive : 0 < n) (fit : out + 8 * n ≤ size) :
    WP isa (seed n out) s fun t => wordsVal t.mem base out n = 2 ^ (64 * n - 1) ∧
      Outside base out (8 * n) s.mem t.mem ∧ Keeps [.eax, .ebp, .edx] s t := by
  refine WP.mono (VG.Proof.Mont.X86.setConstW_ok scratch (by omega) (by omega)
    (show 2 ^ (64 * n - 1) < 2 ^ (32 * (2 * n)) from
      Nat.pow_lt_pow_right (by decide) (by omega))) fun t ⟨value, K, O⟩ => ?_
  exact ⟨by rw [wordsVal_eq_val32]; exact value, by simpa only [show 4 * (2 * n) = 8 * n by omega] using O, K⟩

end VG.Proof.RsaKeyGen.X86.FastR2
