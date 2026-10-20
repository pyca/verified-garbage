module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Factor
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.Generation.FactorTest
import VerifiedGarbage.Proof.Mont.X86.ExponentShift

/-! # Each factor step divides the exponent by two and counts it -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

theorem factorStep_ok {s : State} {base : Addr} {size n count : Nat}
    (S : Scr s base size) (hn : 0 < n) (room : slot n 8 + 8 * n ≤ size)
    (bx : s.gpr .ebx = BitVec.ofNat 32 count) :
    WP isa (factorStep n) s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 (count + 1) ∧
      val32 t.mem base (slot n 8) (2 * n) = val32 s.mem base (slot n 8) (2 * n) / 2 ∧
      t.zf = some (decide (val32 t.mem base (slot n 8) (2 * n) % 2 = 0)) ∧
      Outside base (slot n 8) (8 * n) s.mem t.mem ∧ Keeps [.eax, .ebx, .edx] s t := by
  unfold factorStep
  refine WP.seq (WP.mono (shiftExponent_ok S (2 * n) (slot n 8) (by omega)) fun a ⟨Oa, va, Ka⟩ => ?_)
  refine WP.mono (factorTest_ok (count := count) (S.of_keeps Ka (by decide)) hn room (by rw [Ka.1 _ (by decide), bx]))
    fun t ⟨bt, zt, mt, Kt⟩ => ?_
  refine ⟨bt, by rw [mt, va], by rw [mt]; exact zt, ?_, (Ka.mono (by decide)).trans (Kt.mono (by decide))⟩
  rw [mt]
  simpa only [show 4 * (2 * n) = 8 * n by omega] using Oa
end VG.Proof.Dsa.X86.Generation
