module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrepareExponent
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Rsa.X86.DivCopy

/-! # Reload the saved exponent and the exact squaring count -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

theorem restoreExponentCount_ok {s : State} {base : Addr} {size count : Nat} (S : Scr s base size)
    (room : primeTwos + 4 ≤ size) (positive : 1 ≤ count)
    (saved : s.mem.readW (off base primeTwos) 32 = BitVec.ofNat 32 count) :
    WP isa (.block restoreExponentCount) s fun t =>
      t.mem.readW (off base roundCount) 32 = BitVec.ofNat 32 (count - 1) ∧
      Outside base roundCount 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold restoreExponentCount
  refine wp_movS (v := BitVec.ofNat 32 count) (by rw [readSrc_sc S room, saved]) fun a sa _ =>
    wp_subi fun b ab _ _ => ?_
  have K := sa.keeps.trans ab.keeps
  have sb := S.of_keeps K (by decide)
  have cr : roundCount + 4 ≤ size := by unfold primeTwos roundCount at *; omega
  refine wp_storeS (sb.ea (by omega)) (sb.write cr) fun t bt => WP.block_nil ?_
  refine ⟨?_, ?_, K.trans (bt.keeps _)⟩
  · rw [bt.mem, Mem.readW_writeW_self32, ab.gpr, sa.gpr]
    exact sub_ofNat positive
  · rw [bt.mem, ab.mem, sa.mem]
    exact writeW32_outside _ _ _ (by have := S.nowrap; omega)

theorem restoreExponent_ok {s : State} {base : Addr} {size n count : Nat} (S : Scr s base size)
    (hn : 0 < n) (width : n ≤ 48) (room : primeExponent + 8 * n ≤ size)
    (positive : 1 ≤ count) (saved : s.mem.readW (off base primeTwos) 32 = BitVec.ofNat 32 count) :
    WP isa (restoreExponent n) s fun t =>
      t.mem.readW (off base roundCount) 32 = BitVec.ofNat 32 (count - 1) ∧
      val32 t.mem base (slot n 8) (2 * n) = val32 s.mem base primeExponent (2 * n) ∧
      Outs base [(slot n 8, 8 * n), (roundCount, 4)] s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have far : slot n 8 + 8 * n ≤ roundCount := by simp only [slot, stride, roundCount]; omega
  have cr : primeTwos + 4 ≤ size := by unfold primeTwos primeExponent at *; omega
  unfold restoreExponent
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Div.copyWords_ok S (by omega) (by omega)
    (by unfold primeExponent roundCount at *; omega) (.inr (.inl (by unfold primeExponent roundCount at *; omega))))
    fun a ⟨Oa, va, Ka⟩ => ?_)
  have counta : a.mem.readW (off base primeTwos) 32 = BitVec.ofNat 32 count := by
    have same : a.mem.readW (off base primeTwos) 32 = s.mem.readW (off base primeTwos) 32 := by
      apply BitVec.eq_of_toNat_eq
      exact Oa.w32 (by unfold primeTwos roundCount at *; omega) (by decide)
    exact same.trans saved
  refine WP.mono (restoreExponentCount_ok (S.of_keeps Ka (by decide)) cr positive counta)
    fun t ⟨ct, Ot, Kt⟩ => ?_
  refine ⟨ct, ?_, ?_, Ka.trans (Kt.mono (by decide))⟩
  · rw [Ot.val32 (by omega) (by unfold roundCount at *; omega), va]
  · rw [show 4 * (2 * n) = 8 * n by omega] at Oa
    exact (Outs.of_outside Oa (by simp)).trans (Outs.of_outside Ot (by simp))
end VG.Proof.Dsa.X86.Generation
