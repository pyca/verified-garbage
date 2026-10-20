module

public import VerifiedGarbage.Impl.Bignum.X86.SanitizeModulus
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Bignum.X86.SmallConstant
import VerifiedGarbage.Proof.Mont.X86.WordOps

/-! # Secret modulus replacement preserves the accepted value without branching -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem sanitizeModulus_ok {s : State} {base : Addr} {bytes n modulus temporary : Nat}
    (hs : Scr s base bytes) (hn : 0 < n)
    (hm : modulus + 8 * n ≤ bytes) (ht : temporary + 8 * n ≤ bytes)
    (apart : modulus + 8 * n ≤ temporary ∨ temporary + 8 * n ≤ modulus)
    (valid : Bool) (mask : s.gpr .ecx = if valid then BitVec.allOnes 32 else 0) :
    WP isa (sanitizeModulus n modulus temporary) s fun t =>
      wordsVal t.mem base modulus n = (if valid then wordsVal s.mem base modulus n else 3) ∧
      Outs base [(temporary, 8 * n), (modulus, 8 * n)] s.mem t.mem ∧
      Keeps [.eax, .ebp, .edx] s t := by
  unfold sanitizeModulus
  refine WP.seq (WP.mono (smallConstant_ok hs hn (by decide) ht) fun u ⟨O, V, K⟩ => ?_)
  have H := hs.of_keeps K (by decide)
  have N : wordsVal u.mem base modulus n = wordsVal s.mem base modulus n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact O.val32 (by omega) (by have := hs.nowrap; omega)
  refine WP.mono (selectsW_ok H valid (by rw [K.1 _ (by decide)]; exact mask)
    (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl rfl))
    fun t ⟨Ot, Value, Kt⟩ => ?_
  have Ot' : Outside base modulus (8 * n) u.mem t.mem := by
    simpa only [show 4 * (2 * n) = 8 * n by omega] using Ot
  refine ⟨?_, (Outs.of_outside O (by simp)).trans
    (Outs.of_outside Ot' (by simp)), K.trans (Kt.mono (by decide))⟩
  rw [wordsVal_eq_val32, Value]
  cases valid <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · simpa only [wordsVal_eq_val32] using V
  · rw [← wordsVal_eq_val32]; exact N

end VG.Proof.Bignum.X86
