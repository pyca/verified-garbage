module
import VerifiedGarbage.Proof.Mont.X86.Instr
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Factor
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Rsa
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.FactorLoop

/-! # Save the candidate's exact power-of-two decomposition -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation
open VG.Spec.Rsa

theorem factor_ok {s : State} {base : Addr} {size n original : Nat}
    (S : Scr s base size) (hn : 0 < n) (width : n ≤ 48)
    (room : slot n 8 + 8 * n ≤ size) (control : primeTwos + 4 ≤ size)
    (pos : 0 < original) (even : original % 2 = 0)
    (value : val32 s.mem base (slot n 8) (2 * n) = original) :
    WP isa (factor n) s fun t =>
      t.mem.readW (off base primeTwos) 32 = BitVec.ofNat 32 (splitTwos original).1 ∧
      val32 t.mem base (slot n 8) (2 * n) = (splitTwos original).2 ∧
      Outs base [(slot n 8, 8 * n), (primeTwos, 4)] s.mem t.mem ∧ Keeps [.eax, .ebx, .edx] s t := by
  unfold factor factorInit
  refine WP.seq (wp_movS rfl fun a sa _ => WP.block_nil ?_)
  refine WP.seq (WP.mono (factorLoop_ok (S.of_keeps sa.keeps (by decide)) hn room pos even
    (by rw [sa.mem]; exact value) (count := 0) sa.gpr) fun b ⟨bx, vb, Ob, Kb⟩ => ?_)
  have K : Keeps [.eax, .ebx, .edx] s b := (sa.keeps.mono (by decide)).trans Kb
  have sb := S.of_keeps K (by decide)
  refine wp_storeS (sb.ea (by omega)) (sb.write control) fun t bt => WP.block_nil ?_
  have Ot : Outside base primeTwos 4 b.mem t.mem := by
    rw [bt.mem]
    exact writeW32_outside _ _ _ (by have := S.nowrap; omega)
  refine ⟨by rw [bt.mem, Mem.readW_writeW_self32, bx, Nat.zero_add], ?_, ?_, K.trans (bt.keeps _)⟩
  · rw [Ot.val32 (by simp only [slot, stride, primeTwos]; omega) (by have := S.nowrap; omega), vb]
  · rw [sa.mem] at Ob
    exact (Outs.of_outside Ob (by simp)).trans (Outs.of_outside Ot (by simp))
end VG.Proof.Dsa.X86.Generation
