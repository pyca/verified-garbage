module

public import VerifiedGarbage.Proof.X25519.AArch64.Hybrid.CarryCode
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# X25519 on AArch64: `Neon.prod2`

Untrusted: everything here is checked by Lean. `prod2 o f₁ g₁ f₂ g₂` leaves at
`o + 16 k + 8 e` limb `k` of a radix-2²⁵·⁵ number below 2²⁷ per limb whose value
is `[f_e] · [g_e]` modulo `p` (`prod2_ok`, `prod2_val`), writing only `FBUF` up to
`o + 160` and vector registers.
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Hybrid

open VG VG.AArch64
open VG.Spec.X25519 (P)
open VG.Impl.X25519.AArch64.Neon
open VG.Proof.Ed25519.AArch64 (Scr off word Outside ofs)

/-- The limbs `prod2` leaves for the elements at `a e` and `b e`. -/
def prodLimbs (m : Mem) (base : Addr) (a b : Nat → Nat) (e : Nat) : Nat → Nat :=
  Hybrid.carries (prodCoef (limbOf (feAt m base (a e))) (limbOf (feAt m base (b e))))

/-- The output place: aligned, past `FBUF`'s rows and before the constants. -/
def OutOk (o : Nat) : Prop := o % 16 = 0 ∧ FBUF + 160 ≤ o ∧ o + 160 ≤ CONST

theorem stores_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat} (ho : OutOk o) :
    ∀ n ≤ 10, WP isa (.block ((List.range n).flatMap fun k => [stq (19 + k) (o + 16 * k)])) s fun t =>
      (∀ k < n, ∀ e < 2, word t.mem base (o + 16 * k + 8 * e) = vdword (s.v (V (19 + k))) e) ∧
      Outside base o 160 s.mem t.mem ∧ t.v = s.v ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.flags = s.flags := by
  obtain ⟨a, b, c⟩ := ho
  simp only [CONST, FBUF] at b c
  intro n hn
  refine wp_range_flatMap (M := isa) (N := 10)
    (fun n (x : State) => (∀ k < n, ∀ e < 2, word x.mem base (o + 16 * k + 8 * e) = vdword (s.v (V (19 + k))) e) ∧
      Outside base o 160 s.mem x.mem ∧ x.v = s.v ∧ x.gpr = s.gpr ∧ x.rd = s.rd ∧ x.wr = s.wr ∧ x.sp = s.sp ∧
      x.flags = s.flags)
    (fun n x hn ⟨xw, xo, xv, xg, xr, xww, xsp, xf⟩ => ?_) n hn s
    ⟨fun _ h => absurd h (by omega), Outside.refl _ _ _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hx : Scratch x base := scratch_of hs xg xww
  have hd : (o + 16 * n) % 16 = 0 := by omega
  have hd' : o + 16 * n + 16 ≤ 4096 := by omega
  refine WP.block_cons_iff.mpr ⟨_, exec_stq hx _ hd hd', WP.block_nil_iff.mpr ?_⟩
  simp only [VG.Proof.Curve448.AArch64.Neon.setMem_mem, VG.Proof.Curve448.AArch64.Neon.setMem_gpr,
    VG.Proof.Curve448.AArch64.Neon.setMem_rd, VG.Proof.Curve448.AArch64.Neon.setMem_wr,
    VG.Proof.Curve448.AArch64.Neon.setMem_sp, VG.Proof.Curve448.AArch64.Neon.setMem_v, flags_setMem]
  refine ⟨fun k hk e he => ?_, xo.trans ((st_outside _ _ _ hd').mono (by omega) (by omega)), xv, xg, xr, xww, xsp, xf⟩
  rcases (show k < n ∨ k = n by omega) with h | rfl
  · rw [Outside.word' (st_outside _ _ _ hd') (by omega) (by omega)]; exact xw k h e he
  · rw [word_st _ _ _ hd' he, xv]

/-- `prod2`: the limbs of `[f_e] · [g_e]` at `o`. -/
theorem prod2_ok {s : State} {base : Addr} (hs : Scratch s base) (hc : Consts s.mem base) {o f₁ g₁ f₂ g₂ : Nat}
    (ho : OutOk o) (hf₁ : Below f₁) (hg₁ : Below g₁) (hf₂ : Below f₂) (hg₂ : Below g₂) :
    WP isa (.block (prod2 o f₁ g₁ f₂ g₂)) s fun t =>
      (∀ k < 10, ∀ e < 2, (word t.mem base (o + 16 * k + 8 * e)).toNat =
        prodLimbs s.mem base (fun e => if e = 0 then f₁ else f₂) (fun e => if e = 0 then g₁ else g₂) e k) ∧
      Outside base FBUF (o + 160 - FBUF) s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ t.flags = s.flags := by
  have ho' := ho
  obtain ⟨oa, ob, oc⟩ := ho'
  simp only [CONST, FBUF] at ob oc
  rw [prod2, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (convertF_ok hs hc hf₁ hf₂) fun t ⟨tf, to, tg, tr, tw, tsp, tfl⟩ => ?_
  have ht : Scratch t base := scratch_of hs tg tw
  have hct : Consts t.mem base := by
    obtain ⟨c1, c2, c3⟩ := hc
    refine ⟨fun e he => ?_, fun e he => ?_, fun c hc' => ?_⟩
    · rw [Outside.word' to (by simp only [M26, CONST, FBUF]; omega) (by simp only [M26, CONST]; omega)]; exact c1 e he
    · rw [Outside.word' to (by simp only [M25, CONST, FBUF]; omega) (by simp only [M25, CONST]; omega)]; exact c2 e he
    · rw [Outside.nw to (by simp only [C19, CONST, FBUF]; omega) (by simp only [C19, CONST]; omega)]; exact c3 c hc'
  have below : ∀ x, Below x → feAt t.mem base x = feAt s.mem base x := fun x ⟨_, hx⟩ =>
    to.fe (by simp only [FBUF] at hx ⊢; omega) (by simp only [FBUF] at hx; omega)
  rw [WP.block_append_iff]
  refine WP.mono (convertG_ok ht hct hg₁ hg₂) fun u ⟨ug, um, ugg, ur, uw, usp, ufl⟩ => ?_
  have hu : Scratch u base := scratch_of ht ugg uw
  rw [WP.block_append_iff]
  have hfr : FRows u.mem base (fun e => limbOf (feAt s.mem base (if e = 0 then f₁ else f₂))) 10 := by
    rw [um]; exact tf
  have hgu : GRegs u (fun e => limbOf (feAt s.mem base (if e = 0 then g₁ else g₂))) 9 := by
    have e1 : (fun e => limbOf (feAt t.mem base (if e = 0 then g₁ else g₂))) =
        fun e => limbOf (feAt s.mem base (if e = 0 then g₁ else g₂)) := funext fun e => by
      split
      · rw [below g₁ hg₁]
      · rw [below g₂ hg₂]
    rw [← e1]; exact ug
  refine WP.mono (products_ok hu hfr hgu (fun e i => Nat.le_sub_one_of_lt (limbOf_lt _ _))
    (fun e i => Nat.le_sub_one_of_lt (limbOf_lt _ _))) fun x ⟨xc, xm, xg, xr, xw, xsp, xfl⟩ => ?_
  have hx : Scratch x base := scratch_of hu xg xw
  rw [WP.block_append_iff]
  have hcx : Consts x.mem base := by rw [xm, um]; exact hct
  refine WP.mono (carries_ok hx hcx xc (fun e he k hk => prodCoef_le (fun i _ => Nat.le_sub_one_of_lt (limbOf_lt _ _))
    (fun i _ => Nat.le_sub_one_of_lt (limbOf_lt _ _)) k)) fun y ⟨yc, yb, ym, yg, yr, yw, ysp, yfl⟩ => ?_
  have hy : Scratch y base := scratch_of hx yg yw
  refine WP.mono (stores_ok hy ho 10 (Nat.le_refl _)) fun z ⟨zw, zo, zv, zg, zr, zww, zsp, zfl⟩ => ?_
  refine ⟨fun k hk e he => ?_, ?_, zg.trans (yg.trans (xg.trans (ugg.trans tg))),
    zr.trans (yr.trans (xr.trans (ur.trans tr))), zww.trans (yw.trans (xw.trans (uw.trans tw))),
    zsp.trans (ysp.trans (xsp.trans (usp.trans tsp))), zfl.trans (yfl.trans (xfl.trans (ufl.trans tfl)))⟩
  · rw [zw k hk e he, yc k hk e he]
    rfl
  · have h1 : Outside base FBUF (o + 160 - FBUF) s.mem t.mem := to.mono (Nat.le_refl _) (by simp only [FBUF]; omega)
    have h2 : Outside base FBUF (o + 160 - FBUF) y.mem z.mem := zo.mono (by simp only [FBUF]; omega) (by simp only [FBUF]; omega)
    rw [ym, xm, um] at h2
    exact h1.trans h2

theorem prodLimbs_val (m : Mem) (base : Addr) (a b : Nat → Nat) (e : Nat) :
    val (prodLimbs m base a b e) % P = feAt m base (a e) * feAt m base (b e) % P := by
  rw [prodLimbs, val_carries, val_prodCoef, val_limbOf (VG.Proof.Ed25519.Word64.val4_lt _ _ _ _),
    val_limbOf (VG.Proof.Ed25519.Word64.val4_lt _ _ _ _)]

theorem prodLimbs_lt (m : Mem) (base : Addr) (a b : Nat → Nat) (e : Nat) : ∀ k < 10, prodLimbs m base a b e k < 2 ^ 27 :=
  carries_prod_lt (fun _ _ => Nat.le_sub_one_of_lt (limbOf_lt _ _)) (fun _ _ => Nat.le_sub_one_of_lt (limbOf_lt _ _))

theorem prodLimbs_le (m : Mem) (base : Addr) (a b : Nat → Nat) (e : Nat) : ∀ k < 10, prodLimbs m base a b e k ≤ limbB k :=
  carries_prod_le (fun _ _ => Nat.le_sub_one_of_lt (limbOf_lt _ _)) (fun _ _ => Nat.le_sub_one_of_lt (limbOf_lt _ _))

end VG.Proof.X25519.AArch64.Hybrid
