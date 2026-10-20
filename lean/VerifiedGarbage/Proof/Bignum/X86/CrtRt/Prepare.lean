module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Power
public import VerifiedGarbage.Proof.Mont.X86.Inverse
public import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Framework.Omega

/-! # A context of private CRT at a run-time width

One doubled `16 Bc` times is `R² mod M` (`powerTwo_ok`). `prepare` replaces
the modulus by three unless it is an odd number above one, and sets one, the
inverse and `R² mod M` (`prepare_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (count1_zf countLoop)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The ranges `R² mod M` changes. -/
abbrev powR (len : Nat) (c : Ctx) : List (Nat × Nat) :=
  [(lo len (.slot c 1), bc len c + 4), (lo len (.slot c 4), bc len c)]

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem powerTwo_ok (h : In base bytes len args s) (c : Ctx) (hM : 1 < sv s.mem base len c 0) :
    WP isa (powerTwo c) s fun u =>
      Frame (frameR base (s.gpr .esp) (powR len c)) s.mem u.mem ∧
      sv u.mem base len c 4 = 2 ^ (16 * bc len c) % sv s.mem base len c 0 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have nw' := h.crt.scratch.nowrap
  have f8 := h.slot_fit c (j := 8) (by decide)
  have g := bc_ge h.lower' c
  have hb := bc_le h.upper' c
  have bw := bc_eq_cwc len c
  have s01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 1) := sl_le (len := len) c (by decide)
  have s14 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 4) := sl_le (len := len) c (by decide)
  have s48 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 8) := sl_le (len := len) c (by decide)
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have est : st len c = 2 * bc len c + 32 := rfl
  have cb1 : cb len (one c) = bc len c := by simp [cb, one]
  have cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  have fit : ∀ p ∈ powR len c, p.1 + p.2 ≤ bytes := by
    intro p hp
    simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> dsimp only <;> omega
  unfold powerTwo
  refine WP.seq (WP.mono (setSmall_ok (x := .slot c 4) h (one_ok c) (by rw [cb1]; omega) (v := 1) (by decide))
    fun u₀ ⟨O₀, V₀, K₀⟩ => ?_)
  simp only [cb1, cw1] at O₀ V₀
  have h₀ := h.keep K₀ (by decide) (by decide) (O₀.mono (Nat.zero_le _) (by omega))
  have M₀ : sv u₀.mem base len c 0 = sv s.mem base len c 0 := O₀.val32 (by omega) (by omega)
  refine WP.seq (widthC_ok (k := 0) (c := c) (r := .esi) h₀.width h.upper' fun u₁ K₁ m₁ e₁ => ?_)
  refine wp_addS rfl fun u₂ a₂ _ => wp_addS rfl fun u₃ a₃ _ => wp_addS rfl fun u₄ a₄ _ => ?_
  refine wp_addS rfl fun u₅ a₅ _ => WP.block_nil ?_
  have K₅ : Keeps [.esi] u₀ u₅ := (((K₁.trans a₂.keeps).trans a₃.keeps).trans a₄.keeps).trans a₅.keeps
  have m₅ : u₅.mem = u₀.mem := by rw [a₅.mem, a₄.mem, a₃.mem, a₂.mem, m₁]
  have esi₅ : (u₅.gpr .esi).toNat = 16 * bc len c := by
    rw [a₅.gpr, a₄.gpr, a₃.gpr, a₂.gpr, e₁]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have h₅ := h₀.regs (K₅.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₀ u₅) m₅
  have sp₅ : u₅.gpr .esp = s.gpr .esp := by rw [K₅.1 _ (by decide), K₀.1 _ (by decide)]
  let M := sv s.mem base len c 0
  let I : Nat → State → Prop := fun j t =>
    Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₅ t ∧
      Frame (frameR base (s.gpr .esp) (powR len c)) u₅.mem t.mem ∧
      sv t.mem base len c 4 = 2 ^ j % M ∧ (t.gpr .esi).toNat = 16 * bc len c - j
  have I₀ : I 0 u₅ := ⟨Keeps.refl _ _, Frame.refl _ _,
    by rw [m₅]; simp only [sv] at V₀ ⊢; rw [V₀, Nat.pow_zero, Nat.mod_eq_of_lt hM], by rw [esi₅]; rfl⟩
  refine WP.mono (countLoop (N := 16 * bc len c) (by omega) I ?_ I₀) fun t ⟨Kt, Ft, Vt, _⟩ => ?_
  · rintro j t hj ⟨Kt, Ft, Vt, esit⟩
    have ht := h₅.keepF Kt (by decide) (by decide) (by rw [sp₅]; exact Ft) fit
    have Mt : sv t.mem base len c 0 = M := by
      have := frameR_val32 (d := lo len (.slot c 0)) (k := cwc len c) Ft h.crt.room nw' (by omega) (by
        intro p hp
        simp only [powR, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> dsimp only <;> omega) fit
      simp only [sv]; rw [this, m₅]; exact M₀
    have hM' : 0 < M := by omega
    refine WP.mono (doubleStep_ok ht c (by rw [Vt, Mt]; exact Nat.mod_lt _ hM'))
      fun u ⟨Fu, Vu, esiu, zu, Ku⟩ => ?_
    obtain ⟨c₁, c₂⟩ := count1_zf esit hj
    have spt : t.gpr .esp = s.gpr .esp := by rw [Kt.1 _ (by decide), sp₅]
    refine ⟨⟨Kt.trans Ku, Ft.trans (by rw [← spt]; exact Fu), ?_, by rw [esiu]; exact c₁⟩, by rw [zu, c₂]⟩
    rw [Vu, Vt, Mt, ← Nat.add_mod, ← Nat.two_mul, Nat.mul_comm, ← Nat.pow_succ]
  · have K₅s : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₅ := (K₀.mono (by decide)).trans (K₅.mono (by decide))
    refine ⟨?_, Vt, K₅s.trans Kt⟩
    rw [← m₅] at O₀
    exact (frameR_of_outside O₀ (by omega) (by simp [powR])).trans Ft

end

end VG.Proof.Bignum.X86.CrtRt
