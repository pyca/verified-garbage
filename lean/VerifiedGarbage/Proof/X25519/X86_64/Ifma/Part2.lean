module

public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Part1
import VerifiedGarbage.Proof.X25519.X86_64.Env
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# X25519 on x86-64 with AVX512_IFMA: stages 2 and 3 of an iteration

From `(BB, AA, CB, DA)` in the lanes of `ymm0–ymm4`, stage 2 and its product
leave `(BB, AA + a24 E, x₃', t)` there, and its first operand, with `AA` and
`E`, in `ymm10–ymm14`; stage 3 and its product then leave
`(x₂', z₂', x₃', z₃')`.
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.X25519.X86_64 (Scr Outside Outside.mono)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

theorem fe5_zero : fe5 (fun _ => 0) = 0 := rfl

/-- Stage 2 and its product. -/
theorem part2_ok {s : State} {base : Addr} {x1 : Nat → Nat} (hs : Scr s base) (hk : Consts s.mem base x1)
    (hy : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61) :
    WP isa (.block (stage2 ++ mulG true)) s fun s' => Kept base s s' ∧
      (∀ l < 4, ∀ i < 5, lanes s' 0 l i < 2 ^ 62 ∧ lanes s' 10 l i < 2 ^ 52) ∧
      fe5 (lanes s' 10 0) = fe5 (lanes s 0 1) ∧
      fe5 (lanes s' 10 1) = fe5 (lanes s 0 1) - fe5 (lanes s 0 0) ∧
      fe5 (lanes s' 0 0) = fe5 (lanes s 0 0) ∧
      fe5 (lanes s' 0 1) = fe5 (lanes s 0 1) + (fe5 (lanes s 0 1) - fe5 (lanes s 0 0)) * Spec.X25519.a24 ∧
      fe5 (lanes s' 0 2) = (fe5 (lanes s 0 3) + fe5 (lanes s 0 2)) * (fe5 (lanes s 0 3) + fe5 (lanes s 0 2)) ∧
      fe5 (lanes s' 0 3) = (fe5 (lanes s 0 3) - fe5 (lanes s 0 2)) * (fe5 (lanes s 0 3) - fe5 (lanes s 0 2)) := by
  have hr := hs.rdi
  simp only [stage2, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (s2a_wp hr (scr_ctx hs) hk.c hy) fun s₁ ⟨v₁, m₁, u₁, k₁⟩ => ?_
  have hs₁ := scr_of hs (vm_gpr v₁) (vm_wr v₁)
  have hk₁ : Consts s₁.mem base x1 := by rw [m₁]; exact hk
  rw [WP.block_append_iff]
  refine WP.mono (carryU_wp hs₁.rdi (scr_ctx hs₁) hk₁.c fun l hl i hi => (u₁ l hl i hi).2)
    fun s₂ ⟨v₂, m₂, u₂, k₂⟩ => ?_
  have hs₂ := scr_of hs₁ (vm_gpr v₂) (vm_wr v₂)
  have hk₂ : Consts s₂.mem base x1 := by rw [m₂]; exact hk₁
  rw [WP.block_append_iff]
  refine WP.mono (s2b_wp hs₂.rdi (scr_ctx hs₂) hk₂) fun s₃ ⟨v₃, m₃, u₃, k₃⟩ => ?_
  have hs₃ := scr_of hs₂ (vm_gpr v₃) (vm_wr v₃)
  have e0 : ∀ l < 4, ∀ i < 5, lanes s₃ 0 l i = lanes s 0 l i := fun l hl i hi => by
    rw [lanes_keep (s := s₂) (s' := s₃) (r0 := 0) (fun r hr _ h2 l hl => k₃ r hr (.inl (by omega_using [h2])) l hl)
        (by decide) l hl i hi,
      lanes_keep (s := s₁) (s' := s₂) (r0 := 0) (fun r _ _ h2 l hl => k₂ r (by omega_using [h2]) l hl) (by decide) l hl i hi,
      lanes_keep (s := s) (s' := s₁) (r0 := 0) (fun r _ _ h2 l hl => k₁ r (by omega_using [h2]) l hl) (by decide) l hl i hi]
  have e10 := lanes_keep (s := s₂) (s' := s₃) (r0 := 10) (fun r hr h1 _ l hl => k₃ r hr (.inr h1) l hl) (by decide)
  have bU : ∀ l < 4, ∀ i < 5, lanes s₃ 10 l i < 2 ^ 52 := fun l hl i hi => by
    rw [e10 l hl i hi]; exact (u₂ l hl i hi).2
  have bV : ∀ l < 4, ∀ i < 5, lanes s₃ 5 l i < 2 ^ 52 := fun l hl i hi => by
    rw [u₃ l hl i hi]; split
    · split <;> decide
    · exact (u₂ l hl i hi).2
  refine WP.mono (mulG1_wp hs₃.rdi (scr_ctx hs₃) (fun l hl i hi => by rw [e0 l hl i hi]; exact hy l hl i hi) bU bV)
    fun s₄ ⟨v₄, m₄, u₄, k₄⟩ => ?_
  have K : Kept base s s₄ :=
    (((Kept.vm v₁ m₁).trans (Kept.vm v₂ m₂)).trans (Kept.vm v₃ m₃)).trans (Kept.vm v₄ m₄)
  have e10' := lanes_keep (s := s₃) (s' := s₄) (r0 := 10) (fun r _ h1 h2 l hl => k₄ r (by omega_using [h2]) (by omega_using [h1]) l hl)
    (by decide)
  -- the operands
  have fU : ∀ l < 4, fe5 (lanes s₃ 10 l) = fe5 (fun i => opU (lanes s 0) l i) := fun l hl => by
    rw [fe5_congr (fun i hi => e10 l hl i hi), fe5_congr (fun i hi => (u₂ l hl i hi).1),
      fe5_carry _ (u₁ l hl 4 (by decide)).2]
    exact fe5_congr fun i hi => (u₁ l hl i hi).1
  have hle : ∀ l < 4, ∀ i < 5, lanes s 0 l i ≤ kbv i := fun l hl i hi => le_kbv i (hy l hl i hi)
  have f0 : fe5 (fun i => opU (lanes s 0) 0 i) = fe5 (lanes s 0 1) := fe5_congr fun _ _ => rfl
  have f1 : fe5 (fun i => opU (lanes s 0) 1 i) = fe5 (lanes s 0 1) - fe5 (lanes s 0 0) :=
    fe5_sub (fun _ _ => rfl) (hle 0 (by decide))
  have f2 : fe5 (fun i => opU (lanes s 0) 2 i) = fe5 (lanes s 0 3) + fe5 (lanes s 0 2) := fe5_add fun _ _ => rfl
  have f3 : fe5 (fun i => opU (lanes s 0) 3 i) = fe5 (lanes s 0 3) - fe5 (lanes s 0 2) :=
    fe5_sub (fun _ _ => rfl) (hle 2 (by decide))
  have fP : ∀ l < 4, fe5 (fun i => mulNat (lanes s₃ 10 l) (lanes s₃ 5 l) i) =
      fe5 (fun i => opU (lanes s 0) l i) * fe5 (lanes s₃ 5 l) := fun l hl => by
    rw [fe5_mul (bU l hl) (bV l hl), fU l hl]
  have fV : ∀ l < 4, 2 ≤ l → fe5 (lanes s₃ 5 l) = fe5 (fun i => opU (lanes s 0) l i) := fun l hl h2 => by
    rw [← fU l hl]
    exact fe5_congr fun i hi => by rw [u₃ l hl i hi, ite_eq_right (by omega_using [h2]), e10 l hl i hi]
  have fS : ∀ l < 4, 2 ≤ l → fe5 (lanes s₄ 0 l) =
      fe5 (fun i => opU (lanes s 0) l i) * fe5 (fun i => opU (lanes s 0) l i) := fun l hl h2 => by
    rw [fe5_congr (y := fun i => mulNat (lanes s₃ 10 l) (lanes s₃ 5 l) i) (fun i hi => by
      rw [(u₄ l hl i hi).1, ite_eq_right (by omega_using [h2]), Nat.zero_add]), fP l hl, fV l hl h2]
  have fA : ∀ l < 2, fe5 (lanes s₄ 0 l) = fe5 (lanes s 0 l) +
      fe5 (fun i => opU (lanes s 0) l i) * fe5 (lanes s₃ 5 l) := fun l hl => by
    rw [← fP l (by omega_using [hl])]
    exact fe5_add fun i hi => by
      rw [(u₄ l (by omega_using [hl]) i hi).1, ite_eq_left ⟨rfl, hl⟩, e0 l (by omega_using [hl]) i hi]
  have v0 : fe5 (lanes s₃ 5 0) = 0 := by
    rw [← fe5_zero]; exact fe5_congr fun i hi => by rw [u₃ 0 (by decide) i hi]; simp
  have v1 : fe5 (lanes s₃ 5 1) = Spec.X25519.a24 := by
    rw [← fe5_a24]; exact fe5_congr fun i hi => by rw [u₃ 1 (by decide) i hi]; simp
  refine ⟨K, fun l hl i hi => ⟨(u₄ l hl i hi).2.1, by rw [e10' l hl i hi]; exact bU l hl i hi⟩,
    by rw [fe5_congr (e10' 0 (by decide)), fU 0 (by decide), f0],
    by rw [fe5_congr (e10' 1 (by decide)), fU 1 (by decide), f1],
    by rw [fA 0 (by decide), v0, Fin.mul_zero, Fin.add_zero],
    by rw [fA 1 (by decide), v1, f1],
    by rw [fS 2 (by decide) (by decide), f2], by rw [fS 3 (by decide) (by decide), f3]⟩

/-- Stage 3 and its product, with stage 2's first operand in `ymm10–ymm14`. -/
theorem part3_ok {s : State} {base : Addr} {x1 : Nat → Nat} (hs : Scr s base) (hk : Consts s.mem base x1)
    (hy : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 62 ∧ lanes s 10 l i < 2 ^ 52) :
    WP isa (.block (stage3 ++ mulG false)) s fun s' => Kept base s s' ∧
      (∀ l < 4, ∀ i < 5, lanes s' 0 l i < 2 ^ 61) ∧
      fe5 (lanes s' 0 0) = fe5 (lanes s 10 0) * fe5 (lanes s 0 0) ∧
      fe5 (lanes s' 0 1) = fe5 (lanes s 10 1) * fe5 (lanes s 0 1) ∧
      fe5 (lanes s' 0 2) = fe5 (lanes s 0 2) * 1 ∧
      fe5 (lanes s' 0 3) = fe5 (lanes s 0 3) * fe5 x1 := by
  have hr := hs.rdi
  simp only [stage3, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (carryR_wp hr (scr_ctx hs) hk.c fun l hl i hi => by have := (hy l hl i hi).1; omega_using [this])
    fun s₁ ⟨v₁, m₁, u₁, k₁⟩ => ?_
  have hs₁ := scr_of hs (vm_gpr v₁) (vm_wr v₁)
  have hk₁ : Consts s₁.mem base x1 := by rw [m₁]; exact hk
  have e10 := lanes_keep (s := s) (s' := s₁) (r0 := 10) (fun r _ h1 h2 l hl => k₁ r (by omega_using [h2]) h1 l hl) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (s3b_wp hs₁.rdi (scr_ctx hs₁) hk₁) fun s₂ ⟨v₂, m₂, u₂⟩ => ?_
  have hs₂ := scr_of hs₁ (vm_gpr v₂) (vm_wr v₂)
  have bU : ∀ l < 4, ∀ i < 5, lanes s₂ 10 l i < 2 ^ 52 := fun l hl i hi => by
    rw [(u₂ l hl i hi).1]; split
    · rw [e10 l hl i hi]; exact (hy l hl i hi).2
    · exact (u₁ l hl i hi).2
  have bV : ∀ l < 4, ∀ i < 5, lanes s₂ 5 l i < 2 ^ 52 := fun l hl i hi => by
    rw [(u₂ l hl i hi).2]; split
    · exact (u₁ l hl i hi).2
    · split
      · exact hk.x1 i hi
      · split <;> decide
  refine WP.mono (mulG0_wp hs₂.rdi (scr_ctx hs₂) bU bV) fun s₃ ⟨⟨v₃, m₃, u₃, _⟩, _⟩ => ?_
  have K : Kept base s s₃ := ((Kept.vm v₁ m₁).trans (Kept.vm v₂ m₂)).trans (Kept.vm v₃ m₃)
  have fC : ∀ l < 4, fe5 (lanes s₁ 0 l) = fe5 (lanes s 0 l) := fun l hl => by
    rw [fe5_congr (fun i hi => (u₁ l hl i hi).1), fe5_carry _ (by have := (hy l hl 4 (by decide)).1; omega_using [this])]
  have fM : ∀ l < 4, fe5 (lanes s₃ 0 l) = fe5 (lanes s₂ 10 l) * fe5 (lanes s₂ 5 l) := fun l hl => by
    rw [fe5_congr (y := fun i => mulNat (lanes s₂ 10 l) (lanes s₂ 5 l) i) (fun i hi => by
      rw [(u₃ l hl i hi).1]; simp), fe5_mul (bU l hl) (bV l hl)]
  have fU : ∀ l < 2, fe5 (lanes s₂ 10 l) = fe5 (lanes s 10 l) := fun l hl =>
    fe5_congr fun i hi => by rw [(u₂ l (by omega_using [hl]) i hi).1, ite_eq_left hl, e10 l (by omega_using [hl]) i hi]
  have fU' : ∀ l < 4, 2 ≤ l → fe5 (lanes s₂ 10 l) = fe5 (lanes s 0 l) := fun l hl h2 => by
    rw [← fC l hl]
    exact fe5_congr fun i hi => by rw [(u₂ l hl i hi).1, ite_eq_right (by omega_using [h2])]
  have fV : ∀ l < 2, fe5 (lanes s₂ 5 l) = fe5 (lanes s 0 l) := fun l hl => by
    rw [← fC l (by omega_using [hl])]
    exact fe5_congr fun i hi => by rw [(u₂ l (by omega_using [hl]) i hi).2, ite_eq_left hl]
  have v2 : fe5 (lanes s₂ 5 2) = 1 := by
    rw [← fe5_one]; exact fe5_congr fun i hi => by rw [(u₂ 2 (by decide) i hi).2]; simp
  have v3 : fe5 (lanes s₂ 5 3) = fe5 x1 :=
    fe5_congr fun i hi => by rw [(u₂ 3 (by decide) i hi).2]; simp
  refine ⟨K, fun l hl i hi => (u₃ l hl i hi).2.2 rfl,
    by rw [fM 0 (by decide), fU 0 (by decide), fV 0 (by decide)],
    by rw [fM 1 (by decide), fU 1 (by decide), fV 1 (by decide)],
    by rw [fM 2 (by decide), fU' 2 (by decide) (by decide), v2],
    by rw [fM 3 (by decide), fU' 3 (by decide) (by decide), v3]⟩

end VG.Proof.X25519.X86_64.Ifma
