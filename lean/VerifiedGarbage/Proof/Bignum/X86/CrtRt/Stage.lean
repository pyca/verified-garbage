module

import VerifiedGarbage.Proof.Bignum.X86.CrtRt.WindowPower
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Validate
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.MulOk

/-! # What the stages of private CRT share

Frames widened to ranges that contain theirs (`frameR_widen`), the low words
of a number below their range (`val32_low`), a context made from a factor
(`factorCtx_ok`: the factor copied into slot 0 and the context prepared), and
the result of a power saved zero-extended (`saveResult_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

theorem frameR_widen {base : Addr} {sp : BitVec 32} {ws ws' : List (Nat × Nat)} {m m' : Mem}
    (F : Frame (frameR base sp ws) m m') (hw : ∀ p ∈ ws, ∃ q ∈ ws', q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2) :
    Frame (frameR base sp ws') m m' :=
  F.sub fun r hr => by
    simp only [frameR, List.mem_cons, List.mem_map] at hr
    rcases hr with rfl | ⟨p, hp, rfl⟩
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · obtain ⟨q, hq, h1, h2⟩ := hw p hp
      exact ⟨⟨off base q.1, q.2⟩, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q, hq, rfl⟩),
        VG.Offset.sub base h1 h2⟩

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- `2 B` and `B` bytes from wide slot 9 on; half slots within the wide ones. -/
theorem In.wide_fit (h : In base bytes len args s) {j : Nat} (hj : j ≤ 19) :
    lo len (.slot .wide j) + 2 * bc len .wide + 32 ≤ lo len (.slot .wide (j + 1)) ∧
      lo len (.slot .wide (j + 1)) ≤ bytes := by
  have f := h.slot_fit .wide (j := j) (by omega)
  have e : lo len (.slot .wide (j + 1)) = lo len (.slot .wide j) + st len .wide := by
    simp only [lo]; rw [Nat.succ_mul]; omega
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  omega

/-- The half context's slots, its table and the wide context's slots 0 to 8, within the first nine
wide slots and the table. -/
theorem half_in_wide (h : In base bytes len args s) {j : Nat} (hj : j ≤ 8) :
    lo len (.slot .half j) + st len .half ≤ lo len (.slot .wide 9) := by
  have hb := bc_half_le' len
  have g := bc_ge h.lower' .wide
  have e : lo len (.slot .half j) = numBase + j * st len .half := rfl
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have sh : st len .half = 2 * bc len .half + 32 := rfl
  have sw : st len .wide = 2 * bc len .wide + 32 := rfl
  have := Nat.mul_le_mul_right (st len .half) hj
  rw [e, e9]; omega

theorem prepR_fit (h : In base bytes len args s) (c : Ctx) : ∀ p ∈ prepR len c, p.1 + p.2 ≤ bytes := by
  have f8 := h.slot_fit c (j := 8) (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  have e01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 1) := sl_le c (by decide)
  have e1 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have e3 : lo len (.slot c 3) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have e4 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have e7 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have z0 : lo len (.slot c 0) = numBase := sl_zero len c
  have nb : numBase = 3336 := rfl
  intro p hp
  simp only [prepR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [invOff] <;> omega

/-- A prepared context: its modulus the odd number above one that slot 0 held (or three), one in
slot 3 and `R² mod M` in slot 4. -/
theorem prepCtx_ok (h : In base bytes len args s) (c : Ctx) :
    WP isa (prepare c) s fun u =>
      CtxOk base bytes len args c (safeM (sv s.mem base len c 0)) u ∧ sv u.mem base len c 3 = 1 ∧
      sv u.mem base len c 4 = 2 ^ (16 * bc len c) % safeM (sv s.mem base len c 0) ∧
      Frame (frameR base (s.gpr .esp) (prepR len c)) s.mem u.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u :=
  WP.mono (prepare_ok h c) fun _ ⟨F, M, one, R2, I, K⟩ =>
    ⟨⟨h.keepF K (by decide) (by decide) F (prepR_fit h c), M, safeM_gt _, safeM_odd _, I⟩, one, R2, F, K⟩

/-- A power's result (slot 6 of `c`) into the wide slot `o`, zero-extended to `2 B` bytes. -/
theorem saveResult_ok (h : In base bytes len args s) (c : Ctx) {o : Nat} (ho9 : 9 ≤ o) (ho : o ≤ 19) :
    WP isa (saveResult c o) s fun u =>
      Outside base (lo len (.slot .wide o)) (2 * bc len .wide) s.mem u.mem ∧
      val32 u.mem base (lo len (.slot .wide o)) (2 * cwc len .wide) = sv s.mem base len c 6 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have W := h.wide_fit (j := o) ho
  have f8 := h.slot_fit c (j := 8) (by decide)
  have bw := bc_eq_cwc len .wide
  have bc' := bc_eq_cwc len c
  have hb := bc_half_le' len
  have g := bc_ge h.lower' .wide
  have hcw : bc len c ≤ bc len .wide := by cases c <;> omega
  have bl := h.bytes_lt
  have e69 : lo len (.slot c 6) + bc len c ≤ lo len (.slot .wide o) := by
    have e6 : lo len (.slot c 6) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
    have e89 : lo len (.slot c 8) + st len c ≤ lo len (.slot .wide 9) := by
      cases c with
      | half => exact half_in_wide h (j := 8) (by decide)
      | wide => exact sl_le (i := 8) (j := 9) .wide (by decide)
    have : lo len (.slot .wide 9) ≤ lo len (.slot .wide o) := by
      have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
      have eo : lo len (.slot .wide o) = numBase + o * st len .wide := rfl
      have := Nat.mul_le_mul_right (st len .wide) ho9; omega
    have est : st len c = 2 * bc len c + 32 := rfl
    omega
  have cb2 : cb len (two .wide) = 2 * bc len .wide := by simp [cb, two]
  have cw2 : cw len (two .wide) = 2 * cwc len .wide := by
    have := bc_dvd len .wide; simp [cw, cb, two, cwc]; omega
  have cb1 : cb len (one c) = bc len c := by simp [cb, one]
  have cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  unfold saveResult
  refine WP.seq (WP.mono (zero_ok h (x := .slot .wide o) (two_ok .wide) (by rw [cb2]; omega))
    fun u₁ ⟨O₁, Z₁, K₁⟩ => ?_)
  rw [cb2, cw2] at *
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega))
  refine WP.mono (copy_ok h₁ (x := .slot c 6) (d := .slot .wide o) (one_ok c) (by rw [cb1]; omega)
    (by rw [cb1]; omega) (by rw [cb1]; exact .inr e69)) fun u ⟨O₂, V₂, K₂⟩ => ⟨?_, ?_, ?_⟩
  · rw [cb1] at O₂; exact O₁.trans (O₂.mono (Nat.le_refl _) (by omega))
  · rw [cb1] at O₂
    rw [cw1] at V₂
    have hz : val32 u₁.mem base (lo len (.slot .wide o) + 4 * cwc len c) (2 * cwc len .wide - cwc len c) = 0 := by
      have z := Z₁
      rw [show 2 * cwc len .wide = cwc len c + (2 * cwc len .wide - cwc len c) by omega, val32_append] at z
      rcases Nat.eq_zero_of_add_eq_zero z with ⟨_, z2⟩
      exact (Nat.mul_eq_zero.mp z2).resolve_left (Nat.ne_of_gt (Nat.two_pow_pos _))
    rw [show 2 * cwc len .wide = cwc len c + (2 * cwc len .wide - cwc len c) by omega,
      val32_ext (by rw [O₂.val32 (.inr (by omega)) (by omega)]; exact hz), V₂]
    simp only [sv]
    exact O₁.val32 (.inl (by omega)) (by omega)
  · exact (K₁.mono (by decide)).trans K₂

end

end VG.Proof.Bignum.X86.CrtRt
