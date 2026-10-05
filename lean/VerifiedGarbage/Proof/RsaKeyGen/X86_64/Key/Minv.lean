import VerifiedGarbage.Proof.Bignum.X86_64.Setup

/-!
# An RSA key from its primes on x86-64: the inverse of `e` modulo `2⁶⁴`

`minv` leaves `e⁻¹ mod 2⁶⁴` in `rcx` (`minvC_ok`), as well as its negation
in `r15` (`minv_ok`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Proof.Bignum (emod_pow_weaken odd_sq)

theorem inv_of_emod {a x : Nat} (h : ((a : Int) * x - 1) % (2 ^ 64 : Int) = 0) : a * x % 2 ^ 64 = 1 := by
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h
  have e : ((a * x : Nat) : Int) = 1 + 2 ^ 64 * k := by push_cast; omega
  have : ((a * x : Nat) : Int) % 2 ^ 64 = 1 := by rw [e, Int.add_mul_emod_self_left]; decide
  exact_mod_cast this

/-- `minv`: `rbx⁻¹ mod 2⁶⁴` into `rcx`, for an odd `rbx`. -/
theorem minvC_ok (s : State) (hodd : (s.gpr .rbx).toNat % 2 = 1) :
    WP isa (.block minv) s fun t =>
      (s.gpr .rbx).toNat * (t.gpr .rcx).toNat % 2 ^ 64 = 1 ∧ t.gpr .rbx = s.gpr .rbx ∧
      Keep [.rax, .rcx, .rdx, .rsi, .r15] s t ∧ t.mem = s.mem := by
  unfold minv
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx] (c := .block [.mov .rcx (.reg .rbx)]) (Q := fun t =>
    t.gpr .rcx = s.gpr .rbx ∧ t.mem = s.mem) (by xrun) rfl) fun t₀ ⟨⟨h₀, hm₀⟩, k₀⟩ => ?_
  have hb₀ : t₀.gpr .rbx = s.gpr .rbx := k₀.gpr (by decide)
  have e₀ : (((t₀.gpr .rbx).toNat : Int) * (t₀.gpr .rcx).toNat - 1) % (2 ^ 3 : Int) = 0 := by
    rw [hb₀, h₀]
    have h1 := odd_sq _ hodd
    have h2 : (((s.gpr .rbx).toNat : Int) * (s.gpr .rbx).toNat) % 8 = 1 := by exact_mod_cast h1
    show (((s.gpr .rbx).toNat : Int) * (s.gpr .rbx).toNat - 1) % 8 = 0
    omega
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₀ (j := 3) (by decide) e₀) fun t₁ ⟨e₁, hb₁, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₁ (j := 6) (by decide) e₁) fun t₂ ⟨e₂, hb₂, hm₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₂ (j := 12) (by decide) e₂) fun t₃ ⟨e₃, hb₃, hm₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₃ (j := 24) (by decide) e₃) fun t₄ ⟨e₄, hb₄, hm₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₄ (j := 32) (by decide) (emod_pow_weaken (by decide) e₄))
    fun t₅ ⟨e₅, hb₅, hm₅, k₅⟩ => ?_
  have hb : t₅.gpr .rbx = s.gpr .rbx := hb₅.trans (hb₄.trans (hb₃.trans (hb₂.trans (hb₁.trans hb₀))))
  have kk := ((((k₀.trans k₁).trans k₂).trans k₃).trans k₄).trans k₅
  rw [hb] at e₅
  refine WP.mono (WP.keep [.r15] (Q := fun t => t.mem = t₅.mem) (by xrun) rfl) fun t ⟨hm, k⟩ => ?_
  refine ⟨?_, (k.gpr (by decide)).trans hb, (kk.trans k).mono (by decide), ?_⟩
  · rw [k.gpr (by decide)]; exact inv_of_emod e₅
  · rw [hm, hm₅, hm₄, hm₃, hm₂, hm₁, hm₀]

end VG.Proof.RsaKeyGen.X86_64.Key
