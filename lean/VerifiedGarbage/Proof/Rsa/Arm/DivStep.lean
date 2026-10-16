module

public import VerifiedGarbage.Proof.Rsa.Arm.DivShift
public import VerifiedGarbage.Proof.Rsa.Arm.DivBit
public import VerifiedGarbage.Proof.Rsa.KeyMath
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A native division iteration implements the shared arithmetic model -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Div
open VG VG.Arm VG.Impl.Rsa.Arm.Div VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem step_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa step s fun t =>
      t.gpr .r6 = s.gpr .r6 - 1 ∧ t.z = (s.gpr .r6 - 1 == 0) ∧ Context g t ∧
      Outs (State.addr g.base) g.ranges s.mem t.mem ∧ Rest (.r6 :: clobbers) s t ∧
      (g.value s.mem 1 < g.value s.mem 2 → g.value s.mem 2 < 2 ^ (32 * g.n) →
        (g.value t.mem 1, g.value t.mem 0) =
          VG.Proof.Rsa.divStep (g.value s.mem 2) (32 * g.n) (g.value s.mem 1, g.value s.mem 0)) := by
  have f0 : g.offsets 0 + 4 * g.n ≤ g.size := h.fits 0
  have f1 : g.offsets 1 + 4 * (g.n + 1) ≤ g.size := h.fits 1
  have nowrap := h.workspace.nowrap
  have sep01 : g.offsets 0 + 4 * g.n ≤ g.offsets 1 ∨
      g.offsets 1 + 4 * (g.n + 1) ≤ g.offsets 0 := h.separate 0 1 (by decide)
  have sep03 : g.offsets 0 + 4 * g.n ≤ g.offsets 3 ∨
      g.offsets 3 + 4 * (g.n + 1) ≤ g.offsets 0 := h.separate 0 3 (by decide)
  rw [step, WP.seq_iff]
  refine WP.mono (shift_ok h) ?_
  rintro u ⟨qU, rU, ctxU, frameU, restU⟩
  have dU := h.divisor_frame frameU
  rw [WP.seq_iff]
  refine WP.mono (reduce_ok ctxU) ?_
  rintro v ⟨rV, bV, ctxV, frameV, restV⟩
  have qV : g.value v.mem 0 = g.value u.mem 0 := by
    change val32 _ _ _ g.n = val32 _ _ _ g.n
    exact frameV.val32 (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> with_reducible assumption) (by omega)
  have borrow : (v.gpr .r11).toNat ≤ 1 := by rw [bV]; split <;> decide
  refine WP.mono (quotientBit_ok ctxV borrow) ?_
  rintro t ⟨qT, count, zero, ctxT, frameT, restT⟩
  have cV : v.gpr .r6 = s.gpr .r6 :=
    (restV.gpr .r6 (by simp [clobbers])).trans (restU.gpr .r6 (by simp [clobbers]))
  refine ⟨by rw [count, cV], by rw [zero, cV], ctxT,
    frameU.trans ((frameV.mono (by simp [Geometry.ranges])).trans
      (Outs.of_outside frameT (by simp [Geometry.ranges]))),
    (restU.mono (by simp)).trans ((restV.mono (by simp)).trans restT), ?_⟩
  intro remainder divisor
  have rVal := rU (Nat.lt_trans remainder divisor)
  have radix : 2 ^ (32 * g.n) = 2 * 2 ^ (32 * g.n - 1) := by
    rw [← Nat.pow_succ']; congr 1; have := h.positive; omega
  have even : g.value v.mem 0 % 2 = 0 := by
    rw [qV, qU, Nat.mod_mod_of_dvd _ ⟨2 ^ (32 * g.n - 1), radix⟩]
    omega
  have rT : g.value t.mem 1 = g.value v.mem 1 := by
    change val32 _ _ _ (g.n + 1) = val32 _ _ _ (g.n + 1)
    exact frameT.val32 (by omega) (by omega)
  rw [rT, rV, qT even, bV, qV, qU, rVal, dU]
  simp only [VG.Proof.Rsa.divStep]
  split <;> simp only [Nat.add_sub_cancel, Nat.sub_zero]

end VG.Proof.Rsa.Arm.Div
