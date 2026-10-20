module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Coefficient
import VerifiedGarbage.Proof.Framework.Omega

/-! # The recombination

`recombine_ok`: `m = m_q + q h` into the wide slot 19 (`2 B` bytes), from
`q` (wide slot 11), `h` (wide slot 7) and `m_q` (wide slot 17, `2 B` bytes),
when it fits.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- The ranges the recombination changes. -/
abbrev reR (len : Nat) : List (Nat × Nat) :=
  [(multOff, 4), (prodOff, 2 * bc len .wide + 4), (mulAOff, bc len .wide),
    (lo len (.slot .wide 19), 2 * bc len .wide)]

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem recombine_ok (h : In base bytes len args s) {q hc mq : Nat}
    (hq : val32 s.mem base (lo len (.slot .wide 11)) (cwc len .wide) = q)
    (hh : val32 s.mem base (lo len (.slot .wide 7)) (cwc len .wide) = hc)
    (hmq : val32 s.mem base (lo len (.slot .wide 17)) (2 * cwc len .wide) = mq) :
    WP isa recombine s fun u =>
      Frame (frameR base (s.gpr .esp) (reR len)) s.mem u.mem ∧
      (mq + q * hc < 2 ^ (32 * (2 * cwc len .wide)) →
        val32 u.mem base (lo len (.slot .wide 19)) (2 * cwc len .wide) = mq + q * hc) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u := by
  have pf := h.prod_fit
  have bw := bc_eq_cwc len .wide
  have g := bc_ge h.lower' .wide
  have bl := h.bytes_lt
  have nw := h.crt.scratch.nowrap
  have f19 := h.slot_fit .wide (j := 19) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e7 : lo len (.slot .wide 7) = numBase + 7 * st len .wide := rfl
  have e11 : lo len (.slot .wide 11) = numBase + 11 * st len .wide := rfl
  have e17 : lo len (.slot .wide 17) = numBase + 17 * st len .wide := rfl
  have e19 : lo len (.slot .wide 19) = numBase + 19 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  have ma : mulAOff = 2312 := rfl
  have po : prodOff = 256 := rfl
  have mo : multOff = 48 := rfl
  have cb1 : cb len (one .wide) = bc len .wide := by simp [cb, one]
  have cw1 : cw len (one .wide) = cwc len .wide := by simp [cw, cwc, cb, one]
  have cb2 : cb len (two .wide) = 2 * bc len .wide := by simp [cb, two]
  have cw2 : cw len (two .wide) = 2 * cwc len .wide := by
    have := bc_dvd len .wide; simp [cw, cb, two, cwc]; omega
  have fitR : ∀ p ∈ reR len, p.1 + p.2 ≤ bytes := by
    intro p hp; simp only [reR, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> dsimp only <;> omega
  unfold recombine
  -- `q` into the multiplicand, and `q h`.
  refine WP.seq (WP.mono (copy_ok h (x := .slot .wide 11) (d := mulA) (one_ok .wide) (by rw [cb1]; omega)
    (by rw [cb1]; simp only [mulA, lo]; omega) (by rw [cb1]; simp only [mulA, lo]; exact .inl (by omega)))
    fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  simp only [mulA, lo, cb1, cw1] at O₁ V₁
  rw [show numBase + 11 * st len .wide = lo len (.slot .wide 11) from rfl, hq] at V₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega))
  refine WP.seq (WP.mono (wideProduct_ok h₁ (b := .slot .wide 7) (by omega) (by simp only [lo]; omega))
    fun u₂ ⟨F₂, V₂, K₂⟩ => ?_)
  rw [V₁, O₁.val32 (d := lo len (.slot .wide 7)) (k := cwc len .wide) (.inr (by omega)) (by omega), hh] at V₂
  have h₂ := h₁.keepF K₂ (by decide) (by decide) F₂ (prodR_fit h₁)
  have sp₁ : u₁.gpr .esp = s.gpr .esp := K₁.1 _ (by decide)
  rw [sp₁] at F₂
  have M₂ : val32 u₂.mem base (lo len (.slot .wide 17)) (2 * cwc len .wide) = mq := by
    rw [prodR_keep h₁ F₂ (sp₁ ▸ h₁.crt.room) (by omega) (by omega),
      O₁.val32 (.inr (by omega)) (by omega), hmq]
  -- `m_q + q h`.
  refine WP.mono (chainAdd_ok h₂ (o := .slot .wide 19) (a := prod) (b := .slot .wide 17) (two_ok .wide)
    (by rw [cb2]; omega) (by rw [cb2]; simp only [prod, lo]; omega) (by rw [cb2]; omega)
    (by rw [cb2]; simp only [prod, lo]; exact .inr (by omega)) (by rw [cb2]; exact .inr (by omega)))
    fun u ⟨O₃, _, ⟨c, _, V₃⟩, K₃⟩ => ⟨?_, fun fits => ?_, ?_⟩
  · rw [cb2] at O₃
    have F₁ : Frame (frameR base (s.gpr .esp) (reR len)) s.mem u₁.mem := frameR_of_outside O₁ (by omega) (by simp)
    have F₂' : Frame (frameR base (s.gpr .esp) (reR len)) u₁.mem u₂.mem :=
      frameR_mono F₂ fun p hp => by
        simp only [prodR, List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> simp
    exact (F₁.trans F₂').trans (frameR_of_outside O₃ (by omega) (by simp))
  · rw [cw2, show lo len prod = prodOff from rfl] at V₃
    rw [M₂] at V₃
    have pq : val32 u₂.mem base prodOff (2 * cwc len .wide) = q * hc :=
      val32_low (b := 1) V₂ (by omega)
    rw [pq] at V₃
    cases c
    · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at V₃; omega
    · have := val32_lt u.mem base (lo len (.slot .wide 19)) (2 * cwc len .wide)
      simp only [Bool.toNat_true, Nat.mul_one] at V₃; omega
  · exact (((K₁.mono (by decide)).trans K₂).trans (K₃.mono (by decide)))

end

end VG.Proof.Bignum.X86.CrtRt
