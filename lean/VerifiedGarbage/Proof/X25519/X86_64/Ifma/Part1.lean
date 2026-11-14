module

public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Lanes
import VerifiedGarbage.Proof.X25519.X86_64.Env
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# X25519 on x86-64 with AVX512_IFMA: stage 1 of an iteration

From `(x₂, z₂, x₃, z₃)` in the lanes of `ymm0–ymm4` and the mask of the swap
in `ymm15`, stage 1 and its product leave `(BB, AA, CB, DA)` there, of the
swapped pairs.
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.X25519.X86_64 (Scr Outside Outside.mono contains_sc)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw sel4)

theorem scr_ctx {s : State} {base : Addr} (hs : Scr s base) : Ctx s := fun d hd => by
  rw [hs.rdi]; exact ⟨_, hs.wr, contains_sc hd⟩

theorem vm_gpr {s s' : State} (h : vm s s' = s') : s'.gpr = s.gpr := by rw [← h]; rfl
theorem vm_rd {s s' : State} (h : vm s s' = s') : s'.rd = s.rd := by rw [← h]; rfl
theorem vm_wr {s s' : State} (h : vm s s' = s') : s'.wr = s.wr := by rw [← h]; rfl

theorem scr_of {s s' : State} {base : Addr} (hs : Scr s base) (hg : s'.gpr = s.gpr)
    (hw : s'.wr = s.wr) : Scr s' base := ⟨by rw [hg]; exact hs.rdi, by rw [hw]; exact hs.wr, hs.nowrap⟩

/-- What a part of an iteration keeps. -/
structure Kept (base : Addr) (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outside base 1024 480 s.mem s'.mem

theorem Kept.trans {base : Addr} {s₁ s₂ s₃ : State} (h₁ : Kept base s₁ s₂) (h₂ : Kept base s₂ s₃) :
    Kept base s₁ s₃ :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₁.mem.trans h₂.mem⟩

theorem Kept.vm {base : Addr} {s s' : State} (h : vm s s' = s') (hm : s'.mem = s.mem) : Kept base s s' :=
  ⟨vm_gpr h, vm_rd h, vm_wr h, by rw [hm]; exact Outside.refl _ _ _ _⟩

theorem lanes_keep {s s' : State} {r0 : Nat} (h : ∀ r < 16, r0 ≤ r → r < r0 + 5 → ∀ l < 4, qw s' (xr r) l = qw s (xr r) l)
    (hr : r0 + 5 ≤ 16) : ∀ l < 4, ∀ i < 5, lanes s' r0 l i = lanes s r0 l i := fun l hl i hi => by
  simp only [lanes]; rw [h (r0 + i) (by omega_using [hr, hi]) (by omega_using []) (by omega_using [hi]) l hl]

theorem le_kbv {x : Nat} (i : Nat) (h : x < 2 ^ 61) : x ≤ kbv i := by simp only [kbv]; split <;> omega_using [h]

theorem pu_lt (b : Bool) {l : Nat} (hl : l < 4) : pu b l < 4 := by
  cases b <;> rcases (by omega_using [hl] : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> decide

theorem pv_lt (b : Bool) {l : Nat} (hl : l < 4) : pv b l < 4 := by
  cases b <;> rcases (by omega_using [hl] : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> decide

/-- The lane of the ladder's state that the swap `b` puts in lane `l`. -/
def swl (b : Bool) (l : Nat) : Nat := if b then l ^^^ 2 else l

/-- Stage 1 and its product, with the mask of the swap `b` in `ymm15`: from
`(x₂, z₂, x₃, z₃)`, swapped if `b`, `(BB, AA, CB, DA)`. -/
theorem part1_ok {s : State} {base : Addr} {x1 : Nat → Nat} (hs : Scr s base) (hk : Consts s.mem base x1)
    (hy : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61) {b : Bool}
    (hm : ∀ l < 4, qw s (xr 15) l = VG.Proof.X25519.X86_64.mask b) :
    WP isa (.block (stage1 ++ mulG false)) s fun s' => Kept base s s' ∧
      (∀ l < 4, ∀ i < 5, lanes s' 0 l i < 2 ^ 61) ∧
      fe5 (lanes s' 0 0) = (fe5 (lanes s 0 (swl b 0)) - fe5 (lanes s 0 (swl b 1))) *
        (fe5 (lanes s 0 (swl b 0)) - fe5 (lanes s 0 (swl b 1))) ∧
      fe5 (lanes s' 0 1) = (fe5 (lanes s 0 (swl b 0)) + fe5 (lanes s 0 (swl b 1))) *
        (fe5 (lanes s 0 (swl b 0)) + fe5 (lanes s 0 (swl b 1))) ∧
      fe5 (lanes s' 0 2) = (fe5 (lanes s 0 (swl b 2)) + fe5 (lanes s 0 (swl b 3))) *
        (fe5 (lanes s 0 (swl b 0)) - fe5 (lanes s 0 (swl b 1))) ∧
      fe5 (lanes s' 0 3) = (fe5 (lanes s 0 (swl b 2)) - fe5 (lanes s 0 (swl b 3))) *
        (fe5 (lanes s 0 (swl b 0)) + fe5 (lanes s 0 (swl b 1))) := by
  have hr := hs.rdi
  simp only [stage1, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (s1a_wp hr (scr_ctx hs) hk.c hy) fun s₁ ⟨v₁, m₁, u₁, k₁⟩ => ?_
  have hs₁ := scr_of hs (vm_gpr v₁) (vm_wr v₁)
  have hk₁ : Consts s₁.mem base x1 := by rw [m₁]; exact hk
  have hm₁ : ∀ l < 4, qw s₁ (xr 15) l = VG.Proof.X25519.X86_64.mask b := fun l hl => by
    rw [k₁ 15 (by decide) (by decide) (by decide) l hl]; exact hm l hl
  rw [WP.block_append_iff]
  refine WP.mono (carryI_wp hs₁.rdi (scr_ctx hs₁) hk₁.c fun l hl i hi => (u₁ l hl i hi).2) fun s₂ ⟨v₂, m₂, u₂, k₂⟩ => ?_
  have hs₂ := scr_of hs₁ (vm_gpr v₂) (vm_wr v₂)
  have hk₂ : Consts s₂.mem base x1 := by rw [m₂]; exact hk₁
  have hm₂ : ∀ l < 4, qw s₂ (xr 15) l = VG.Proof.X25519.X86_64.mask b := fun l hl => by
    rw [k₂ 15 (by decide) (by decide) (by decide) l hl]; exact hm₁ l hl
  rw [WP.block_append_iff]
  refine WP.mono (s1b_wp hs₂.rdi (scr_ctx hs₂) hk₂ hm₂) fun s₃ ⟨v₃, m₃, u₃⟩ => ?_
  have hs₃ := scr_of hs₂ (vm_gpr v₃) (vm_wr v₃)
  have bU : ∀ l < 4, ∀ i < 5, lanes s₃ 10 l i < 2 ^ 52 := fun l hl i hi => by
    rw [(u₃ l hl i hi).1]; exact (u₂ _ (pu_lt b hl) i hi).2
  have bV : ∀ l < 4, ∀ i < 5, lanes s₃ 5 l i < 2 ^ 52 := fun l hl i hi => by
    rw [(u₃ l hl i hi).2]; exact (u₂ _ (pv_lt b hl) i hi).2
  refine WP.mono (mulG0_wp hs₃.rdi (scr_ctx hs₃) bU bV) fun s₄ ⟨⟨v₄, m₄, u₄, _⟩, _⟩ => ?_
  have K : Kept base s s₄ :=
    (((Kept.vm v₁ m₁).trans (Kept.vm v₂ m₂)).trans (Kept.vm v₃ m₃)).trans (Kept.vm v₄ m₄)
  -- the values of the lanes
  have fU : ∀ l < 4, fe5 (lanes s₂ 0 l) = fe5 (fun i => sumDiff (lanes s 0) l i) := fun l hl => by
    rw [fe5_congr (fun i hi => (u₂ l hl i hi).1), fe5_carry _ (by have := (u₁ l hl 4 (by decide)).2; omega_using [this])]
    exact fe5_congr fun i hi => (u₁ l hl i hi).1
  have hle : ∀ l < 4, ∀ i < 5, lanes s 0 l i ≤ kbv i := fun l hl i hi => le_kbv i (hy l hl i hi)
  have f0 : fe5 (fun i => sumDiff (lanes s 0) 0 i) = fe5 (lanes s 0 0) - fe5 (lanes s 0 1) :=
    fe5_sub (fun i _ => rfl) (hle 1 (by decide))
  have f1 : fe5 (fun i => sumDiff (lanes s 0) 1 i) = fe5 (lanes s 0 0) + fe5 (lanes s 0 1) :=
    fe5_add fun i _ => rfl
  have f2 : fe5 (fun i => sumDiff (lanes s 0) 2 i) = fe5 (lanes s 0 2) - fe5 (lanes s 0 3) :=
    fe5_sub (fun i _ => rfl) (hle 3 (by decide))
  have f3 : fe5 (fun i => sumDiff (lanes s 0) 3 i) = fe5 (lanes s 0 2) + fe5 (lanes s 0 3) :=
    fe5_add fun i _ => rfl
  have fM : ∀ l < 4, fe5 (lanes s₄ 0 l) = fe5 (lanes s₂ 0 (pu b l)) * fe5 (lanes s₂ 0 (pv b l)) :=
    fun l hl => by
      have e4 : ∀ i < 5, lanes s₄ 0 l i = mulNat (lanes s₃ 10 l) (lanes s₃ 5 l) i := fun i hi => by
        rw [(u₄ l hl i hi).1]; simp
      rw [fe5_congr e4, fe5_mul (bU l hl) (bV l hl), fe5_congr (fun i hi => (u₃ l hl i hi).1),
        fe5_congr (fun i hi => (u₃ l hl i hi).2)]
  refine ⟨K, fun l hl i hi => (u₄ l hl i hi).2.2 rfl, ?_, ?_, ?_, ?_⟩
  · rw [fM 0 (by decide)]; cases b <;> simp only [pu, pv, swl, Nat.reduceLT, ↓reduceIte, Nat.reduceMod, Nat.reduceXor, Bool.false_eq_true, Nat.xor_zero] <;>
      first | rw [fU 0 (by decide), f0] | rw [fU 2 (by decide), f2]
  · rw [fM 1 (by decide)]; cases b <;> simp only [pu, pv, swl, Nat.reduceLT, ↓reduceIte, Nat.reduceMod, Nat.reduceXor, Bool.false_eq_true, Nat.xor_zero] <;>
      first | rw [fU 1 (by decide), f1] | rw [fU 3 (by decide), f3]
  · rw [fM 2 (by decide)]; cases b <;> simp only [pu, pv, swl, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceMod, Nat.reduceXor, Bool.false_eq_true, Nat.xor_zero] <;>
      first | rw [fU 3 (by decide), fU 0 (by decide), f3, f0] | rw [fU 1 (by decide), fU 2 (by decide), f1, f2]
  · rw [fM 3 (by decide)]; cases b <;> simp only [pu, pv, swl, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceMod, Nat.reduceXor, Bool.false_eq_true, Nat.xor_zero] <;>
      first | rw [fU 2 (by decide), fU 1 (by decide), f2, f1] | rw [fU 0 (by decide), fU 3 (by decide), f0, f3]

end VG.Proof.X25519.X86_64.Ifma
