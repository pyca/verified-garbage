module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Key
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Output
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.ExponentShift
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Stages
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Stages

/-! # The checks of the precomputed values

`checks`: ZF clear exactly if one (number 3) and `R² mod M` (number 4) are
below the modulus (number 0), and the modulus is odd (`checks_ok`). Their
outcome is public, as the values are.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrecomputedRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt
open VG.Impl.Bignum.X86.PrecomputedRt VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.PublicRt

theorem and_one_zero (w : BitVec 32) : (w &&& 1 == 0) = !decide (w.toNat % 2 = 1) := by
  have hw : (w &&& 1).toNat = w.toNat % 2 := by
    rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
  by_cases hp : w.toNat % 2 = 1
  · have ne : w &&& 1 ≠ 0 := fun h => by rw [h] at hw; simp at hw; omega
    have e : (w &&& 1 == 0) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact ne
    rw [e]; simp [hp]
  · have eq : w &&& 1 = 0 := BitVec.eq_of_toNat_eq (by rw [hw]; simp; omega)
    have e : (w &&& 1 == 0) = true := by simp only [beq_iff_eq]; exact eq
    rw [e]; simp [hp]

theorem checks_zero (c₁ c₂ : Bool) (w : BitVec 32) :
    (cmask c₂ &&& cmask c₁ &&& (w &&& 1) == 0) = !(c₁ && c₂ && decide (w.toNat % 2 = 1)) := by
  cases c₁ <;> cases c₂
  · simp [cmask]
  · simp [cmask]
  · simp [cmask]
  · show (BitVec.allOnes 32 &&& BitVec.allOnes 32 &&& (w &&& 1) == 0) = !(true && true && decide (w.toNat % 2 = 1))
    rw [BitVec.allOnes_and, BitVec.allOnes_and, Bool.true_and, Bool.true_and]
    exact and_one_zero w

/-- The checks' outcome: one and `R² mod M` below `M`, and `M` odd. -/
def Accepted (M T : Nat) : Bool := decide (1 < M) && decide (T < M) && decide (M % 2 = 1)

theorem checks_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : RtIn base bytes len args s) (one : val32 s.mem base (numAt len 3) (nw len) = 1) :
    WP isa checks s fun u =>
      u.zf = some (!Accepted (val32 s.mem base (numAt len 0) (nw len)) (val32 s.mem base (numAt len 4) (nw len))) ∧
      Outside base checkOffset 4 s.mem u.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .esi] s u := by
  have f0 := (h.fits (j := 0) (by decide)).1
  have nw' := h.scratch.nowrap
  have dims := h.dimensions
  have n0 : numAt len 0 = 256 := by simp [numAt, numOff]
  have wl := wb_ge h.lower
  unfold checks
  refine WP.seq (WP.mono (compareAt_ok h (a := 3) (b := 0) (by decide) (by decide)) fun u₁ ⟨m₁, c₁, K₁⟩ => ?_)
  have h₁ := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine WP.seq (wp_storeS (h₁.scratch.ea (d := 148) (by rw [n0] at f0; omega))
    (h₁.scratch.write (d := 148) (n := 4) (by rw [n0] at f0; omega)) fun u₂ m₂ => WP.block_nil ?_)
  have O₂ : Outside base 148 4 s.mem u₂.mem := by rw [m₂.mem, m₁]; exact writeW32_outside _ _ _ (by omega)
  have h₂ := h₁.keep (m₂.keeps []) (by decide) (by decide) (by rw [m₂.mem]; exact (writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
  have V₀ : ∀ j, j ≤ 4 → val32 u₂.mem base (numAt len j) (nw len) = val32 s.mem base (numAt len j) (nw len) :=
    fun j hj => O₂.val32 (.inr (by simp only [numAt, numOff]; omega)) (by
      have := (h.fits (j := j) (by omega)).1; simp only [nw, wb] at *; omega)
  refine WP.seq (WP.mono (compareAt_ok h₂ (a := 4) (b := 0) (by decide) (by decide)) fun u₃ ⟨m₃, c₃, K₃⟩ => ?_)
  rw [V₀ 4 (by decide), V₀ 0 (by decide)] at c₃
  have h₃ := h₂.keep K₃ (by decide) (by decide) (by rw [m₃]; exact Outside.refl _ _ _ _)
  refine wp_movS (readSrc_sc h₃.scratch (d := 148) (by rw [n0] at f0; omega)) fun u₄ e₄ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun u₅ e₅ => ?_
  refine wp_movS (readSrc_sc ((h₃.scratch.of_keeps e₄.keeps (by decide) (by decide)).of_keeps e₅.keeps
    (by decide) (by decide)) (d := numOff) (by rw [n0] at f0; simp only [numOff]; omega)) fun u₆ e₆ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun u₇ e₇ => ?_
  refine wp_logicS (.inl rfl) rfl fun u₈ e₈ => ?_
  refine wp_cmpS rfl fun t F z => WP.block_nil ⟨?_, ?_, ?_⟩
  · have mem₃ : u₃.mem = u₂.mem := m₃
    have edx₄ : u₄.gpr .edx = cmask (decide (1 < val32 s.mem base (numAt len 0) (nw len))) := by
      rw [e₄.gpr, mem₃, m₂.mem, Mem.readW_writeW_self32, c₁, one]
    have ecx₄ : u₄.gpr .ecx = cmask (decide (val32 s.mem base (numAt len 4) (nw len) <
        val32 s.mem base (numAt len 0) (nw len))) := by rw [e₄.other _ (by decide), c₃]
    have eax₇ : u₇.gpr .eax = u₂.mem.readW (off base numOff) 32 &&& 1 := by
      rw [e₇.gpr]
      show u₆.gpr .eax &&& 1 = _
      rw [e₆.gpr, e₅.mem, e₄.mem, mem₃]
    have ecx₇ : u₇.gpr .ecx = cmask (decide (val32 s.mem base (numAt len 4) (nw len) <
        val32 s.mem base (numAt len 0) (nw len))) &&& cmask (decide (1 < val32 s.mem base (numAt len 0) (nw len))) := by
      rw [e₇.other _ (by decide), e₆.other _ (by decide), e₅.gpr]
      show u₄.gpr .ecx &&& u₄.gpr .edx = _
      rw [ecx₄, edx₄]
    have par : (u₂.mem.readW (off base numOff) 32).toNat % 2 = val32 s.mem base (numAt len 0) (nw len) % 2 := by
      obtain ⟨k, hk⟩ : ∃ k, nw len = k + 1 := ⟨nw len - 1, by simp only [nw]; omega⟩
      have n0' : numAt len 0 = numOff := by simp [numAt]
      rw [← V₀ 0 (by decide), hk, VG.Proof.Mont.X86.Dynamic.val32_parity, n0']
    have e₈' : u₈.gpr .ecx = u₇.gpr .ecx &&& u₇.gpr .eax := e₈.gpr
    rw [z, e₈']
    have sz : ∀ x : BitVec 32, x - 0 = x := fun x => by simp
    rw [sz, ecx₇, eax₇, checks_zero, par]
    rfl
  · show Outside base 148 4 s.mem t.mem
    rw [F.mem, e₈.mem, e₇.mem, e₆.mem, e₅.mem, e₄.mem, m₃]
    exact O₂
  · exact ((((((((K₁.trans ((m₂.keeps []).mono (by decide))).trans K₃).trans (e₄.keeps.mono (by decide))).trans
      (e₅.keeps.mono (by decide))).trans (e₆.keeps.mono (by decide))).trans (e₇.keeps.mono (by decide))).trans
      (e₈.keeps.mono (by decide))).trans (F.keeps _))

end VG.Proof.Bignum.X86.PrecomputedRt
