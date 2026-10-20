module

public import VerifiedGarbage.Proof.Bignum.X86.WideLoop
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Complete full-width multiplication for factor validation and CRT recombination -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem wideProduct_ok {s : State} {base : Addr} {bytes N out a b mult : Nat}
    (hs : Scr s base bytes) (hn : 0 < N) (L : WideLayout N bytes out a b mult) :
    WP isa (wideProduct N out a b mult) s fun t =>
      val32 t.mem base out (2 * N + 1) = val32 s.mem base a N * val32 s.mem base b N ∧
      Outs base [(out, 4 * (2 * N + 1)), (mult, 4)] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold wideProduct
  refine WP.seq (WP.mono (zerosW_ok hs (by omega) L.outBound) fun u ⟨O, V, K⟩ => ?_)
  refine WP.seq (wp_movS rfl fun v U _ => WP.block_nil ?_)
  have init : WideInv base N out a b mult 0 s v := by
    refine ⟨?_, ?_, ?_, (K.mono (by decide)).trans (U.keeps.mono (by decide))⟩
    · rw [U.gpr, U.other _ (by decide)]; simp
    · rw [U.mem, V]; simp only [val32, Nat.zero_mul]
    · rw [U.mem]; exact Outs.of_outside O (by simp)
  exact WP.mono (wideLoop_ok hs hn L init) fun t I => ⟨I.value, I.mem, I.keeps⟩

end VG.Proof.Bignum.X86
