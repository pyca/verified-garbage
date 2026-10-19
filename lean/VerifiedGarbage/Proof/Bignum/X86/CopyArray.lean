module

public import VerifiedGarbage.Impl.Bignum.X86.CopyArray
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Internal array transfers preserve integer values -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem copyArray_ok {s : State} {base : Addr} {bytes n src dst : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hsrc : src + 8 * n ≤ bytes) (hdst : dst + 8 * n ≤ bytes)
    (apart : dst = src ∨ dst + 8 * n ≤ src ∨ src + 8 * n ≤ dst) :
    WP isa (copyArray n src dst) s fun t =>
      wordsVal t.mem base dst n = wordsVal s.mem base src n ∧
      Outside base dst (8 * n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  unfold copyArray
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  refine WP.mono (selectsW_ok (hs.of_keeps U.keeps (by decide)) false U.gpr (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun t ⟨O, V, K⟩ => ?_
  refine ⟨?_, ?_, (U.keeps.mono (by decide)).trans (K.mono (by decide))⟩
  · rw [wordsVal_eq_val32, wordsVal_eq_val32, V, U.mem]
    simp only [ite_self]
  · rw [U.mem] at O
    simpa only [show 4 * (2 * n) = 8 * n by omega] using O

end VG.Proof.Bignum.X86
