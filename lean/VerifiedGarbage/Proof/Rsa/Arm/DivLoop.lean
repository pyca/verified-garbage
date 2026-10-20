module
public import VerifiedGarbage.Proof.Rsa.KeyMath
public import VerifiedGarbage.Proof.Rsa.Arm.DivReduce

import VerifiedGarbage.Proof.Rsa.Arm.DivStep
import VerifiedGarbage.Proof.Rsa.Arm.DivInit
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.WideMul

/-! # Termination and quotient/remainder correctness of fixed-count division -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Div
open VG VG.Arm VG.Impl.Rsa.Arm.Div VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

structure Invariant (g : Geometry) (s0 : State) (D N i : Nat) (s : State) : Prop where
  ctx : Context g s
  index : i ≤ 32 * g.n
  count : s.gpr .r6 = BitVec.ofNat 32 (32 * g.n - i)
  frame : Outs (State.addr g.base) g.ranges s0.mem s.mem
  rest : Rest (.r6 :: clobbers) s0 s
  divisor : g.value s.mem 2 = D
  value : 0 < D → D < 2 ^ (32 * g.n) →
    (g.value s.mem 1, g.value s.mem 0) = divIter D (32 * g.n) i (0, N)

theorem loop_ok {g : Geometry} {s0 s : State} {D N : Nat}
    (h : Invariant g s0 D N 0 s) (boundN : N < 2 ^ (32 * g.n)) :
    WP isa (.loop step .ne) s (Invariant g s0 D N (32 * g.n)) := by
  have positive := h.ctx.positive
  have bound := h.ctx.bound
  let I := fun k t => ∃ i, i + k = 32 * g.n ∧ 0 < k ∧ Invariant g s0 D N i t
  refine WP.loop (M := isa) I ?_ (32 * g.n) s ⟨0, by omega, by omega, h⟩
  intro k t pre
  obtain ⟨i, sum, hk, inv⟩ := pre
  refine WP.mono (step_ok inv.ctx) ?_
  rintro u ⟨count, zero, ctxU, frameU, restU, valueU⟩
  have countU : u.gpr .r6 = BitVec.ofNat 32 (32 * g.n - (i + 1)) := by
    rw [count, inv.count]
    change BitVec.ofNat 32 (32 * g.n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  have zeroU : u.z = decide (i + 1 = 32 * g.n) := by
    rw [zero, inv.count]
    change (BitVec.ofNat 32 (32 * g.n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show 32 * g.n - i - 1 = 0 ↔ i + 1 = 32 * g.n by omega]
  have next : Invariant g s0 D N (i + 1) u := by
    refine ⟨ctxU, by omega, countU, inv.frame.trans frameU, inv.rest.trans restU,
      (inv.ctx.divisor_frame frameU).trans inv.divisor, ?_⟩
    intro dPos dBound
    have previous := inv.value dPos dBound
    obtain ⟨q, less, _, _, _⟩ := divIter_inv dPos boundN i (by omega)
    rw [← previous] at less
    rw [inv.divisor] at valueU
    exact (valueU less dBound).trans (by rw [previous]; rfl)
  by_cases done : i + 1 = 32 * g.n
  · left
    refine ⟨?_, done ▸ next⟩
    change some (!u.z) = some false
    simp only [zeroU, done, decide_true, Bool.not_true]
  · right
    refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, next⟩
    change some (!u.z) = some true
    simp only [zeroU, done, decide_false, Bool.not_false]

theorem code_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa code s fun t =>
      Context g t ∧ Outs (State.addr g.base) g.ranges s.mem t.mem ∧ Rest (.r6 :: clobbers) s t ∧
      (0 < g.value s.mem 2 → g.value s.mem 2 < 2 ^ (32 * g.n) →
        g.value t.mem 1 = g.value s.mem 0 % g.value s.mem 2 ∧
        g.value t.mem 0 = g.value s.mem 0 / g.value s.mem 2) := by
  rw [code, WP.seq_iff]
  refine WP.mono (init_ok h) ?_
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

end VG.Proof.Rsa.Arm.Div
