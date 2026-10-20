module

public import VerifiedGarbage.Proof.Rsa.X86.DivContext
public import VerifiedGarbage.Impl.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Initialize division with a zero remainder and public iteration count -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Div
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic

theorem init_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa (.seq (zerosW (g.offsets 1) (g.n + 1))
      (.block [.mov .esi (.imm (BitVec.ofNat 32 (32 * g.n)))])) s fun t =>
      g.value t.mem 1 = 0 ∧ g.value t.mem 0 = g.value s.mem 0 ∧
      t.gpr .esi = BitVec.ofNat 32 (32 * g.n) ∧ Context g t ∧
      Outs g.base g.ranges s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have f1 : g.offsets 1 + 4 * (g.n + 1) ≤ g.size := h.fits 1
  have f0 : g.offsets 0 + 4 * g.n ≤ g.size := h.fits 0
  have sep : g.offsets 0 + 4 * g.n ≤ g.offsets 1 ∨
      g.offsets 1 + 4 * (g.n + 1) ≤ g.offsets 0 := h.separate 0 1 (by decide)
  have nowrap := h.workspace.nowrap
  refine WP.seq (WP.mono (zerosW_ok h.workspace (by omega) f1) ?_)
  rintro u ⟨frameU, zero, restU⟩
  refine wp_movS rfl fun t T _ => WP.block_nil ?_
  refine ⟨?_, ?_, T.gpr, (h.after restU).after T.keeps, ?_,
    (restU.mono (by decide)).trans (T.keeps.mono (by decide))⟩
  · rw [T.mem]; exact zero
  · rw [T.mem]
    change val32 _ _ _ g.n = val32 _ _ _ g.n
    exact frameU.val32 sep (by omega)
  · rw [T.mem]
    exact Outs.of_outside frameU (by simp [Geometry.ranges])
end VG.Proof.Rsa.X86.Div
