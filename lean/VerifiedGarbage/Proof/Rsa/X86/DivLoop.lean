module

public import VerifiedGarbage.Impl.Rsa.X86.Div
public import VerifiedGarbage.Proof.Rsa.KeyMath
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.DivContext

import VerifiedGarbage.Proof.Rsa.X86.DivStep
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Impl.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr
/-! # Termination and quotient/remainder correctness of fixed-count division -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/DivInit.lean`, which only this module imported.
section

/-! # Initialize division with a zero remainder and public iteration count -/

section
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
end

end

@[expose] public section

namespace VG.Proof.Rsa.X86.Div
open VG VG.X86 VG.Impl.Rsa.X86.Div VG.Proof.Mont VG.Proof.Mont.X86
open VG.X86.Wp (ofNat_beq_zero)

structure Invariant (g : Geometry) (s0 : State) (D N i : Nat) (s : State) : Prop where
  ctx : Context g s
  index : i ≤ 32 * g.n
  count : s.gpr .esi = BitVec.ofNat 32 (32 * g.n - i)
  frame : Outs g.base g.ranges s0.mem s.mem
  rest : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s0 s
  divisor : g.value s.mem 2 = D
  value : 0 < D → D < 2 ^ (32 * g.n) →
    (g.value s.mem 1, g.value s.mem 0) = divIter D (32 * g.n) i (0, N)

theorem loop_ok {g : Geometry} {s0 s : State} {D N : Nat}
    (h : Invariant g s0 D N 0 s) (boundN : N < 2 ^ (32 * g.n)) :
    WP isa (.loop (step g.n (g.offsets 0) (g.offsets 1) (g.offsets 2) (g.offsets 3)) .ne) s (Invariant g s0 D N (32 * g.n)) := by
  have positive := h.ctx.positive
  have bound := h.ctx.bound
  let I := fun k t => ∃ i, i + k = 32 * g.n ∧ 0 < k ∧ Invariant g s0 D N i t
  refine WP.loop (M := isa) I ?_ (32 * g.n) s ⟨0, by omega_arith, by omega_arith, h⟩
  intro k t pre
  obtain ⟨i, sum, hk, inv⟩ := pre
  refine WP.mono (step_ok inv.ctx) ?_
  rintro u ⟨count, zero, ctxU, frameU, restU, valueU⟩
  have countU : u.gpr .esi = BitVec.ofNat 32 (32 * g.n - (i + 1)) := by
    rw [count, inv.count]
    change BitVec.ofNat 32 (32 * g.n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith)]
    congr 1
  have zeroU : u.zf = some (decide (i + 1 = 32 * g.n)) := by
    rw [zero, inv.count]
    change some (BitVec.ofNat 32 (32 * g.n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith), ofNat_beq_zero (by omega_arith)]
    simp only [show 32 * g.n - i - 1 = 0 ↔ i + 1 = 32 * g.n by omega_arith]
  have next : Invariant g s0 D N (i + 1) u := by
    refine ⟨ctxU, by omega_arith, countU, inv.frame.trans frameU, inv.rest.trans restU,
      (inv.ctx.divisor_frame frameU).trans inv.divisor, ?_⟩
    intro dPos dBound
    have previous := inv.value dPos dBound
    obtain ⟨q, less, _, _, _⟩ := divIter_inv dPos boundN i (by omega_arith)
    rw [← previous] at less
    rw [inv.divisor] at valueU
    exact (valueU less dBound).trans (by rw [previous]; rfl)
  by_cases done : i + 1 = 32 * g.n
  · left
    refine ⟨?_, done ▸ next⟩
    change u.zf.map not = some false
    simp only [zeroU, done, decide_true, Option.map_some, Bool.not_true]
  · right
    refine ⟨?_, k - 1, by omega_arith, i + 1, by omega_arith, by omega_arith, next⟩
    change u.zf.map not = some true
    simp only [zeroU, done, decide_false, Option.map_some, Bool.not_false]

theorem code_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa (code g.n (g.offsets 0) (g.offsets 1) (g.offsets 2) (g.offsets 3)) s fun t =>
      Context g t ∧ Outs g.base g.ranges s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t ∧
      (0 < g.value s.mem 2 → g.value s.mem 2 < 2 ^ (32 * g.n) →
        g.value t.mem 1 = g.value s.mem 0 % g.value s.mem 2 ∧
        g.value t.mem 0 = g.value s.mem 0 / g.value s.mem 2) := by
  unfold code
  refine WP.seq (WP.mono (init_ok h) ?_)
  rintro u ⟨rU, qU, count, ctxU, frameU, restU⟩
  have boundN : g.value s.mem 0 < 2 ^ (32 * g.n) := val32_lt _ _ _ _
  have inv : Invariant g s (g.value s.mem 2) (g.value s.mem 0) 0 u :=
    ⟨ctxU, by omega, by simpa only [Nat.sub_zero] using count, frameU, restU,
      h.divisor_frame frameU, fun _ _ => by rw [rU, qU]; rfl⟩
  refine WP.mono (loop_ok inv boundN) ?_
  intro t done
  refine ⟨done.ctx, done.frame, done.rest, fun dPos dBound => ?_⟩
  have value := done.value dPos dBound
  rw [divIter_done dPos boundN] at value
  exact Prod.mk.inj value

end VG.Proof.Rsa.X86.Div
