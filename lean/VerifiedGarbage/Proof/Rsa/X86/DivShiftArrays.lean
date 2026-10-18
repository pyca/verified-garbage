module

public import VerifiedGarbage.Proof.Rsa.X86.DivContext

/-! # The quotient's high bit is shifted into the extended remainder -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Div
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Rsa.X86.Div

theorem shiftArrays_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa (shiftArrays g.n (g.offsets 0) (g.offsets 1) (g.offsets 3)) s fun t =>
      g.value t.mem 0 = 2 * g.value s.mem 0 % 2 ^ (32 * g.n) ∧
      (g.value s.mem 1 < 2 ^ (32 * g.n) →
        g.value t.mem 1 = 2 * g.value s.mem 1 + g.value s.mem 0 / 2 ^ (32 * g.n - 1)) ∧
      Context g t ∧ Outs g.base g.ranges s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have f0 : g.offsets 0 + 4 * g.n ≤ g.size := h.fits 0
  have f1 : g.offsets 1 + 4 * (g.n + 1) ≤ g.size := h.fits 1
  have f3 : g.offsets 3 + 4 * (g.n + 1) ≤ g.size := h.fits 3
  have sep01 : g.offsets 0 + 4 * g.n ≤ g.offsets 1 ∨
      g.offsets 1 + 4 * (g.n + 1) ≤ g.offsets 0 := h.separate 0 1 (by decide)
  have sep03 : g.offsets 0 + 4 * g.n ≤ g.offsets 3 ∨
      g.offsets 3 + 4 * (g.n + 1) ≤ g.offsets 0 := h.separate 0 3 (by decide)
  have sep13 : g.offsets 1 + 4 * (g.n + 1) ≤ g.offsets 3 ∨
      g.offsets 3 + 4 * (g.n + 1) ≤ g.offsets 1 := h.separate 1 3 (by decide)
  have nowrap := h.workspace.nowrap
  unfold shiftArrays
  refine WP.seq (WP.mono (shift_ok h.workspace h.positive f0 (by omega) (by omega) true) ?_)
  rintro u ⟨frameU, ⟨c, qVal, bitU⟩, restU⟩
  change g.value u.mem 0 + 2 ^ (32 * g.n) * c.toNat = 2 * g.value s.mem 0 at qVal
  have hu := h.after restU
  have remU : g.value u.mem 1 = g.value s.mem 1 := by
    change val32 _ _ _ (g.n + 1) = val32 _ _ _ (g.n + 1)
    apply frameU.val32
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> omega
    · omega
  refine WP.seq (WP.mono (shift_ok hu.workspace (by omega) f1 f3 (by omega) false) ?_)
  rintro w ⟨frameW, ⟨cr, rVal, bitW⟩, restW⟩
  have hw := hu.after restW
  have bit : (w.gpr .ebx).toNat = c.toNat := by
    rw [bitW, bitU]
    cases c <;> rfl
  have boundedBit : (w.gpr .ebx).toNat ≤ 1 := by rw [bit]; cases c <;> decide
  refine WP.mono (insertBit_ok hw.workspace (by omega) f1 boundedBit) ?_
  rintro t ⟨frameT, restT, remT⟩
  change g.value w.mem 1 % 2 = 0 → g.value t.mem 1 = g.value w.mem 1 + (w.gpr .ebx).toNat at remT
  have quoW : g.value w.mem 0 = g.value u.mem 0 := by
    change val32 _ _ _ g.n = val32 _ _ _ g.n
    apply frameW.val32
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> omega
    · omega
  have quoT : g.value t.mem 0 = g.value w.mem 0 := by
    change val32 _ _ _ g.n = val32 _ _ _ g.n
    exact frameT.val32 (by omega) (by omega)
  have quoBound : g.value u.mem 0 < 2 ^ (32 * g.n) := val32_lt _ _ _ _
  have quoOriginal : g.value s.mem 0 < 2 ^ (32 * g.n) := val32_lt _ _ _ _
  have radix : 2 ^ (32 * g.n) = 2 * 2 ^ (32 * g.n - 1) := by
    rw [← Nat.pow_succ']; congr 1; have := h.positive; omega
  have quotient : g.value u.mem 0 = 2 * g.value s.mem 0 % 2 ^ (32 * g.n) := by
    have eq := congrArg (fun x => x % 2 ^ (32 * g.n)) qVal
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt quoBound] at eq
    exact eq
  have high : c.toNat = g.value s.mem 0 / 2 ^ (32 * g.n - 1) := by
    change g.value u.mem 0 + 2 ^ (32 * g.n) * c.toNat = 2 * g.value s.mem 0 at qVal
    rw [radix] at qVal quoOriginal quoBound
    cases c with
    | false =>
      simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at qVal ⊢
      exact (Nat.div_eq_of_lt (by omega)).symm
    | true =>
      simp only [Bool.toNat_true, Nat.mul_one] at qVal ⊢
      exact (Nat.div_eq_of_lt_le (by omega) (by omega)).symm
  refine ⟨quoT.trans (quoW.trans quotient), ?_, hw.after restT,
    (quotientShift_frame frameU).trans ((frameW.mono (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [Geometry.ranges])).trans
        (Outs.of_outside frameT (by simp [Geometry.ranges]))),
    restU.trans (restW.trans (restT.mono (by decide)))⟩
  intro remBound
  change g.value w.mem 1 + 2 ^ (32 * (g.n + 1)) * cr.toNat = 2 * g.value u.mem 1 at rVal
  have remWidth : g.value w.mem 1 < 2 ^ (32 * (g.n + 1)) := val32_lt _ _ _ _
  rw [remU, pow32_succ] at rVal
  have remDouble : g.value w.mem 1 = 2 * g.value s.mem 1 := by
    cases cr <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at rVal <;> omega
  have even : g.value w.mem 1 % 2 = 0 := by rw [remDouble]; omega
  rw [remT even, bit, remDouble, high]
end VG.Proof.Rsa.X86.Div
