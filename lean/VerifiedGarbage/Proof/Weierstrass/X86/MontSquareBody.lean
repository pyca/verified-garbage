import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareInit
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareLoop

/-! # The x86 P-256 square before its common final subtraction -/
namespace VG.Proof.Weierstrass.X86.Mont
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Proof.Mont VG.Proof.Mont.X86

theorem squareBody_ok {s : State} {base : Addr} {a : Nat} (hb : Bx s base 8192)
    (hp : Ptr s .esi a) (ha : a + 32 ≤ own 4) (hA : val32 s.mem base a 8 < p256Prime) :
    WP isa (.block squareBody) s fun u =>
      Outside base (own 4) 100 s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .edi] s u ∧
      val32 u.mem base (own 4 + 32) 9 < 2 * p256Prime ∧
      ∃ U, 2 ^ 256 * val32 u.mem base (own 4 + 32) 9 =
        val32 s.mem base a 8 * val32 s.mem base a 8 + U * p256Prime := by
  unfold squareBody
  refine WP.block_append (WP.mono (squareInit_ok hb hp ha) fun t ⟨O, K, V⟩ => ?_)
  refine WP.mono (squareReduce_ok (hb.of_keeps K (by decide)) hA V) fun u ⟨O', K', H, E⟩ =>
    ⟨O.trans (O'.mono (by omega) (by omega)), K.widen K' (by decide), H, E⟩

end VG.Proof.Weierstrass.X86.Mont
