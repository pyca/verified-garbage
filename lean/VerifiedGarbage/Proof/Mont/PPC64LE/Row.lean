module

import VerifiedGarbage.Proof.Mont.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Mont.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words

/-!
# Montgomery arithmetic on PPC64LE: a row of the multiplication

`mulRow rs src D` adds `r9 · [rs + src]` (its `D` digits) to the window of
the accumulator at `[r7]`, `w` bytes into the working space: the `D` steps
leave the carry in `r10` (`steps_ok`), which `carryUp` adds to digits `D`
and `D + 1` (`carryUp_ok`), so that the window's `D + 2` digits hold the sum
when it fits them (`mulRow_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont.PPC64LE VG.Proof.Mont

/-- The first `k` steps of a row. -/
def steps (rs : Reg) (src k : Nat) : List Instr := (List.range k).flatMap (mulStep rs src)

theorem steps_succ (rs : Reg) (src k : Nat) :
    steps rs src (k + 1) = steps rs src k ++ mulStep rs src k := by
  simp only [steps, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem wp_append {l₁ l₂ : List Instr} {s : State} {Q : State → Prop}
    (h : WP isa (.block l₁) s (fun s₁ => WP isa (.block l₂) s₁ Q)) : WP isa (.block (l₁ ++ l₂)) s Q :=
  WP.block_append h

/-- The window's low `k` digits `+= r9 · [rs + src] + r10`, the carry to
`r10` (`[rs + src]`, `K + src` bytes into the working space, apart from the
window). -/
theorem steps_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {rs : Reg} {K src w : Nat}
    (hb : At s base rs K) (h7 : At s base .r7 w) (hrs : rs ∉ [.r0, .r10, .r11, .r12, .r7])
    (hu : (s.gpr .r9).toNat < 2 ^ 32) (hc : (s.gpr .r10).toNat < 2 ^ 32) :
    ∀ {k : Nat}, K + src + 4 * k ≤ size → w + 4 * k ≤ size →
    (K + src + 4 * k ≤ w ∨ w + 4 * k ≤ K + src) →
    WP isa (.block (steps rs src k)) s fun u =>
      Outside base w (4 * k) s.mem u.mem ∧
      val32 u.mem base w k + 2 ^ (32 * k) * (u.gpr .r10).toNat =
        val32 s.mem base w k + (s.gpr .r9).toNat * val32 s.mem base (K + src) k + (s.gpr .r10).toNat ∧
      (u.gpr .r10).toNat < 2 ^ 32 ∧ Kp [.r10, .r11, .r12] s u
  | 0, _, _, _ => WP.block_nil ⟨Outside.refl _ _ _ _, by simp [val32], hc, Kp.refl _ _⟩
  | k + 1, hbk, hwk, hsep => by
    have hn := hs.nowrap
    rw [steps_succ]
    refine wp_append (WP.mono (steps_ok hs hb h7 hrs hu hc (k := k) (by omega) (by omega) (by omega))
      fun s₁ ⟨O₁, V₁, C₁, K₁⟩ => ?_)
    have hs₁ := K₁.ws hs
    have hb₁ : At s₁ base rs K := K₁.at hb (not_mem_sub hrs)
    have h7₁ : At s₁ base .r7 w := K₁.at h7
    have hu₁ : (s₁.gpr .r9).toNat < 2 ^ 32 := by rw [K₁.g]; exact hu
    refine WP.mono (mulStep_ok hs₁ hb₁ h7₁ hrs (j := k) (by omega) (by omega) hu₁ C₁) fun u ⟨m₂, c₂, K₂⟩ => ?_
    rw [K₁.g (r := .r9)] at m₂ c₂
    have tk : w32 s₁.mem base (w + 4 * k) = w32 s.mem base (w + 4 * k) := O₁.w32 (by omega) (by omega)
    have bk : w32 s₁.mem base (K + (src + 4 * k)) = w32 s.mem base (K + src + 4 * k) := by
      rw [← Nat.add_assoc]; exact O₁.w32 (by omega) (by omega)
    rw [tk, bk] at m₂ c₂
    have W := writeW32_outside s₁.mem base (d := w + 4 * k)
      (BitVec.ofNat 32 ((s.gpr .r9).toNat * w32 s.mem base (K + src + 4 * k) + w32 s.mem base (w + 4 * k) +
        (s₁.gpr .r10).toNat)) (by omega)
    rw [← m₂] at W
    have hlow : val32 u.mem base w k = val32 s₁.mem base w k := W.val32 (by omega) (by omega)
    have htop : w32 u.mem base (w + 4 * k) = ((s.gpr .r9).toNat * w32 s.mem base (K + src + 4 * k) +
        w32 s.mem base (w + 4 * k) + (s₁.gpr .r10).toNat) % 2 ^ 32 := by
      rw [m₂, w32_write_self, BitVec.toNat_ofNat]
    have hx := step_lt hu (w32_lt s.mem base (K + src + 4 * k)) (w32_lt s.mem base (w + 4 * k)) C₁
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (W.mono (by omega) (by omega)), ?_, ?_, K₁.trans K₂⟩
    · rw [val32_succ, val32_succ, val32_succ, hlow, htop, c₂, pow32_succ]
      generalize hxd : (s.gpr .r9).toNat * w32 s.mem base (K + src + 4 * k) + w32 s.mem base (w + 4 * k) +
        (s₁.gpr .r10).toNat = x at *
      have hx' := Nat.div_add_mod x (2 ^ 32)
      generalize 2 ^ (32 * k) = P at *
      grind
    · rw [c₂]; omega

/-- The carry `r10` added to the window's digits `D` and `D + 1`, when the
sum fits them. -/
theorem carryUp_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {w D : Nat}
    (h7 : At s base .r7 w) (hD : w + 4 * D + 8 ≤ size)
    (hlt : val32 s.mem base (w + 4 * D) 2 + (s.gpr .r10).toNat < 2 ^ 64) :
    WP isa (.block (carryUp D)) s fun u =>
      Outside base (w + 4 * D) 8 s.mem u.mem ∧
      val32 u.mem base (w + 4 * D) 2 = val32 s.mem base (w + 4 * D) 2 + (s.gpr .r10).toNat ∧
      Kp [.r11, .r12] s u := by
  have hn := hs.nowrap
  have hs15 := hs.small
  simp only [val32, Nat.mul_zero, Nat.add_zero] at hlt ⊢
  have t0 := w32_lt s.mem base (w + 4 * D)
  have t1 := w32_lt s.mem base (w + 4 * D + 4)
  simp only [carryUp]
  refine wp_step (lwz_ok hs h7 (by decide) (d := 4 * D) (by omega)) ?_
  refine wp_step exec_add ?_
  refine wp_step (stw_ok ((hs.write _ _).write _ _) ((h7.write _).write _) (by decide) (d := 4 * D) (by omega)) ?_
  refine wp_step (exec_lsr_d (by decide)) ?_
  refine wp_step (lwz_ok (((hs.write _ _).write _ _).store _ |>.write _ _)
    ((((h7.write _).write _).store _).write _) (by decide) (d := 4 * D + 4) (by omega)) ?_
  refine wp_step exec_add ?_
  refine wp_step (stw_ok ((((((hs.write _ _).write _ _).store _).write _ _).write _ _).write _ _)
    (((((((h7.write _).write _).store _).write _).write _).write _)) (by decide) (d := 4 * D + 4) (by omega))
    (WP.block_nil ?_)
  simp only [write_gpr, write_mem, reduceCtorEq, ite_false, ite_true]
  rw [show w + (4 * D + 4) = w + 4 * D + 4 by omega]
  have e1 : (BitVec.ofNat 64 (w32 s.mem base (w + 4 * D)) + s.gpr .r10).toNat =
      w32 s.mem base (w + 4 * D) + (s.gpr .r10).toNat := by
    rw [BitVec.toNat_add, toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hw1 : w32 (s.mem.writeW (off base (w + 4 * D)) (BitVec.ofNat 32
      (BitVec.ofNat 64 (w32 s.mem base (w + 4 * D)) + s.gpr .r10).toNat)) base (w + 4 * D + 4) =
      w32 s.mem base (w + 4 * D + 4) := w32_write_ne hn (by omega) (by omega) (by omega) _
  rw [hw1]
  have e2 : (BitVec.ofNat 64 (w32 s.mem base (w + 4 * D + 4)) + (BitVec.ofNat 64 (w32 s.mem base (w + 4 * D)) +
      s.gpr .r10) >>> 32).toNat = w32 s.mem base (w + 4 * D + 4) +
        (w32 s.mem base (w + 4 * D) + (s.gpr .r10).toNat) / 2 ^ 32 := by
    rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, e1, Nat.shiftRight_eq_div_pow, toNat_ofNat_lt (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [e2]
  rw [e1]
  have W₀ := writeW32_outside s.mem base (d := w + 4 * D) (BitVec.ofNat 32 (w32 s.mem base (w + 4 * D) +
    (s.gpr .r10).toNat)) (by omega)
  have W₁ := writeW32_outside (s.mem.writeW (off base (w + 4 * D)) (BitVec.ofNat 32 (w32 s.mem base (w + 4 * D) +
    (s.gpr .r10).toNat))) base (d := w + 4 * D + 4) (BitVec.ofNat 32 (w32 s.mem base (w + 4 * D + 4) +
    (w32 s.mem base (w + 4 * D) + (s.gpr .r10).toNat) / 2 ^ 32)) (by omega)
  refine ⟨(W₀.mono (Nat.le_refl _) (by omega)).trans (W₁.mono (by omega) (by omega)), ?_, ?_⟩
  · rw [w32_write_ne hn (by omega) (by omega) (by omega), w32_write_self, w32_write_self,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [write_gpr, hr.1, hr.2, ite_false], rfl, rfl, rfl, rfl⟩

/-- The window `+= r9 · [rs + src]` (`D` digits, `K + src` bytes into the
working space, apart from the window), when the sum fits the window's
`D + 2` digits. -/
theorem mulRow_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {rs : Reg} {K src w D : Nat}
    (hb : At s base rs K) (h7 : At s base .r7 w) (hrs : rs ∉ [.r0, .r10, .r11, .r12, .r7])
    (hsrc : K + src + 4 * D ≤ size) (hwD : w + 4 * D + 8 ≤ size)
    (hsep : K + src + 4 * D ≤ w ∨ w + 4 * D + 8 ≤ K + src) (hu : (s.gpr .r9).toNat < 2 ^ 32)
    (hlt : val32 s.mem base w (D + 2) + (s.gpr .r9).toNat * val32 s.mem base (K + src) D < 2 ^ (32 * (D + 2))) :
    WP isa (.block (mulRow rs src D)) s fun u =>
      Outside base w (4 * D + 8) s.mem u.mem ∧
      val32 u.mem base w (D + 2) = val32 s.mem base w (D + 2) + (s.gpr .r9).toNat * val32 s.mem base (K + src) D ∧
      Kp [.r10, .r11, .r12] s u := by
  have hn := hs.nowrap
  simp only [mulRow, List.cons_append]
  refine wp_step (exec_li (by decide)) ?_
  refine wp_append (WP.mono (steps_ok (hs.write _ _) (hb.write _ (ne_of_not_mem hrs)) (h7.write _) hrs
    (by simp only [write_gpr, reduceCtorEq, ite_false]; exact hu) (by simp only [write_gpr, ite_true]; decide) (k := D)
    (by omega) (by omega) (by omega)) fun s₁ ⟨O₁, V₁, C₁, K₁⟩ => ?_)
  simp only [write_mem, write_gpr, ite_true, reduceCtorEq, ite_false] at O₁ V₁ C₁
  have K₀₁ : Kp [.r10, .r11, .r12] s s₁ := (Kp.write s _ (by decide)).trans K₁
  have hs₁ := K₀₁.ws hs
  have h7₁ : At s₁ base .r7 w := K₀₁.at h7
  have z : (BitVec.ofNat 64 0 : BitVec 64).toNat = 0 := rfl
  rw [z, Nat.add_zero] at V₁
  have hhi : val32 s₁.mem base (w + 4 * D) 2 = val32 s.mem base (w + 4 * D) 2 := O₁.val32 (by omega) (by omega)
  have hsplit : val32 s.mem base w (D + 2) = val32 s.mem base w D + 2 ^ (32 * D) * val32 s.mem base (w + 4 * D) 2 :=
    val32_append _ _ _ _ _
  have hP : 0 < 2 ^ (32 * D) := Nat.two_pow_pos _
  have hlt₁ : val32 s₁.mem base (w + 4 * D) 2 + (s₁.gpr .r10).toNat < 2 ^ 64 := by
    rw [hhi]
    rw [hsplit, show 32 * (D + 2) = 32 * D + 64 by omega, Nat.pow_add] at hlt
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (32 * D)) ?_
    rw [Nat.mul_add]
    have := val32_lt s.mem base w D
    have := val32_lt s₁.mem base w D
    omega
  refine WP.mono (carryUp_ok hs₁ h7₁ (by omega) hlt₁) fun u ⟨O₂, V₂, K₂⟩ =>
    ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega)), ?_,
      K₀₁.trans (K₂.mono (by decide))⟩
  rw [val32_append, V₂, O₂.val32 (d := w) (k := D) (by omega) (by omega), hhi, hsplit, Nat.mul_add]
  omega

end VG.Proof.Mont.PPC64LE
