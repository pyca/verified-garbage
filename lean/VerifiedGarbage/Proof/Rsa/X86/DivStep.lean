module

import VerifiedGarbage.Proof.Rsa.X86.DivShiftArrays
import VerifiedGarbage.Proof.Rsa.X86.DivCount
public import VerifiedGarbage.Proof.Rsa.KeyMath
public import VerifiedGarbage.Impl.Rsa.X86.Div
public import VerifiedGarbage.Proof.Rsa.X86.DivContext
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.DivReduce
import VerifiedGarbage.Proof.Rsa.X86.DivBit

/-! # Native i686 division implements the shared bit-serial step -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Div
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Rsa.X86.Div

theorem step_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa (step g.n (g.offsets 0) (g.offsets 1) (g.offsets 2) (g.offsets 3)) s fun t =>
      t.gpr .esi = s.gpr .esi - 1 ∧ t.zf = some (s.gpr .esi - 1 == 0) ∧ Context g t ∧
      Outs g.base g.ranges s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t ∧
      (g.value s.mem 1 < g.value s.mem 2 → g.value s.mem 2 < 2 ^ (32 * g.n) →
        (g.value t.mem 1, g.value t.mem 0) =
          Rsa.divStep (g.value s.mem 2) (32 * g.n) (g.value s.mem 1, g.value s.mem 0)) := by
  have f0 : g.offsets 0 + 4 * g.n ≤ g.size := h.fits 0
  have f1 : g.offsets 1 + 4 * (g.n + 1) ≤ g.size := h.fits 1
  have f2 : g.offsets 2 + 4 * (g.n + 1) ≤ g.size := h.fits 2
  have f3 : g.offsets 3 + 4 * (g.n + 1) ≤ g.size := h.fits 3
  have sep01 : g.offsets 0 + 4 * g.n ≤ g.offsets 1 ∨
      g.offsets 1 + 4 * (g.n + 1) ≤ g.offsets 0 := h.separate 0 1 (by decide)
  have sep03 : g.offsets 0 + 4 * g.n ≤ g.offsets 3 ∨
      g.offsets 3 + 4 * (g.n + 1) ≤ g.offsets 0 := h.separate 0 3 (by decide)
  have nowrap := h.workspace.nowrap
  unfold step
  refine WP.seq (WP.mono (shiftArrays_ok h) ?_)
  rintro u ⟨qU, rU, hu, frameU, restU⟩
  have dU := h.divisor_frame frameU
  refine WP.seq (WP.mono (reduce_ok hu.workspace f1 f2 f3
    (h.separate 3 1 (by decide)) (h.separate 3 2 (by decide))) ?_)
  rintro v ⟨frameV, rV, bitV, restV⟩
  change g.value v.mem 1 =
    (if g.value u.mem 1 < g.value u.mem 2 then g.value u.mem 1 else g.value u.mem 1 - g.value u.mem 2) at rV
  change v.gpr .ebx = (if g.value u.mem 1 < g.value u.mem 2 then 0 else 1) at bitV
  have hv := hu.after restV
  have qV : g.value v.mem 0 = g.value u.mem 0 := by
    change val32 _ _ _ g.n = val32 _ _ _ g.n
    apply frameV.val32
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> omega
    · omega
  have bit : (v.gpr .ebx).toNat ≤ 1 := by rw [bitV]; split <;> decide
  refine WP.block_append (WP.mono (insertBit_ok hv.workspace h.positive f0 bit) ?_)
  rintro w ⟨frameW, restW, qW⟩
  change g.value v.mem 0 % 2 = 0 → g.value w.mem 0 = g.value v.mem 0 + (v.gpr .ebx).toNat at qW
  refine WP.mono (count_ok w) ?_
  rintro t ⟨count, zero, memT, restT⟩
  have countV : w.gpr .esi = s.gpr .esi :=
    (restW.1 .esi (by decide)).trans ((restV.1 .esi (by decide)).trans (restU.1 .esi (by decide)))
  have frameWV : Outs g.base g.ranges v.mem w.mem := Outs.of_outside frameW (by simp [Geometry.ranges])
  have frameVU : Outs g.base g.ranges u.mem v.mem := frameV.mono (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [Geometry.ranges])
  refine ⟨by rw [count, countV], by rw [zero, countV], (hv.after restW).after restT,
    ?_, (restU.mono (by decide)).trans ((restV.mono (by decide)).trans
      ((restW.mono (by decide)).trans (restT.mono (by decide)))), ?_⟩
  · rw [memT]
    exact frameU.trans (frameVU.trans frameWV)
  intro remBound divBound
  have rValue := rU (Nat.lt_trans remBound divBound)
  have radix : 2 ^ (32 * g.n) = 2 * 2 ^ (32 * g.n - 1) := by
    rw [← Nat.pow_succ']; congr 1; have := h.positive; omega
  have even : g.value v.mem 0 % 2 = 0 := by
    rw [qV, qU, Nat.mod_mod_of_dvd _ ⟨2 ^ (32 * g.n - 1), radix⟩]
    omega
  have remW : g.value w.mem 1 = g.value v.mem 1 := by
    change val32 _ _ _ (g.n + 1) = val32 _ _ _ (g.n + 1)
    exact frameW.val32 (by omega) (by omega)
  rw [memT, remW, rV, qW even, bitV, qV, qU, rValue, dU]
  dsimp only [Rsa.divStep]
  split <;> simp
end VG.Proof.Rsa.X86.Div
