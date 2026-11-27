module

import VerifiedGarbage.Proof.Mont.Arm.Step
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Mont.Arm
public import VerifiedGarbage.Proof.Mont.Arm.Words

/-! ### `Mont.Arm.Loop`, which this module and modules that import it used -/

section

/-! ### `Mont.Arm.Row`, which only this module used -/

section

/-!
# Montgomery arithmetic on 32-bit ARM: a row of the multiplication

`mulRow acc src D` adds `r2 · [src]` (its `D` digits) to the window of the
accumulator at `[r0 + acc]`, `r0 = r12 + 4i` (`w = 4i + acc` from the base),
which holds digits: the `D` steps leave the carry in `r3` (`steps_ok`), which
`carryUp` adds to digits `D` and `D + 1` (`carryUp_ok`), so that the window's
`D + 2` digits hold the sum when it fits them (`mulRow_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr wp_str wp_dp wp_mov wp_mul op2_reg op2_lsr op2_lsl
  op2_imm dpVal toNat_add_lt toNat_shr)

/-- The first `k` steps of a row. -/
def steps (acc : Nat) (rb : Reg) (d k : Nat) : List Instr := (List.range k).flatMap (mulStep acc rb d)

theorem steps_succ (acc : Nat) (rb : Reg) (d k : Nat) :
    steps acc rb d (k + 1) = steps acc rb d k ++ mulStep acc rb d k := by
  simp only [steps, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- The window's low `k` digits `+= r2 · [src] + r3`, the carry to `r3`
(`[src]` read at `[rb + d]`, `rb = r12 + K`). -/
theorem steps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc src i w W : Nat}
    {rb : Reg} {K d : Nat} (hb : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 K) (hK : K + d = src)
    (hrb : rb ∉ [.r3, .r5, .r7])
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hp : s.gpr .r0 = s.gpr .r12 + BitVec.ofNat 32 (4 * i))
    (hw : 4 * i + acc = w) (hsrc : src + 4 * W ≤ size)
    (hu : (s.gpr .r2).toNat < 2 ^ 16) (hc : (s.gpr .r3).toNat < 2 ^ 16) :
    ∀ {k : Nat}, k ≤ 2 * W → w + 4 * k ≤ size → (src + 4 * W ≤ w ∨ w + 4 * k ≤ src) → Digs s.mem base w k →
    WP isa (.block (steps acc rb d k)) s fun u =>
      Outside base w (4 * k) s.mem u.mem ∧
      dval u.mem base w k + 2 ^ (16 * k) * (u.gpr .r3).toNat =
        dval s.mem base w k + (s.gpr .r2).toNat * pval s.mem base src k + (s.gpr .r3).toNat ∧
      (u.gpr .r3).toNat < 2 ^ 16 ∧ Digs u.mem base w k ∧ Rest [.r3, .r5, .r7] s u
  | 0, _, _, _, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, by simp only [dval, pval, Nat.mul_zero,
      Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero], hc, fun _ h => absurd h (Nat.not_lt_zero _),
      Rest.refl _ _⟩
  | k + 1, hk, hwk, hsep, hd => by
    have hn := hs.nowrap
    rw [steps_succ]
    refine VG.Proof.X25519.Arm.WP.append (steps_ok hs hb hK hrb h6 hp hw hsrc hu hc (k := k) (by omega_arith)
      (by omega_arith) (by omega_arith) (hd.mono (by omega_arith))) fun s₁ ⟨O₁, V₁, C₁, D₁, K₁⟩ => ?_
    obtain hb₁ : s₁.gpr rb = s₁.gpr .r12 + BitVec.ofNat 32 K := by
      rw [K₁.gpr _ hrb, K₁.gpr _ (by decide)]; exact hb
    obtain hs₁ := hs.of_rest K₁ (by decide)
    obtain h6₁ : s₁.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₁.gpr _ (by decide)]; exact h6
    obtain hp₁ : s₁.gpr .r0 = s₁.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
      rw [K₁.gpr _ (by decide), K₁.gpr _ (by decide)]; exact hp
    obtain e : 4 * i + (acc + 4 * k) = w + 4 * k := by omega_arith
    obtain tk : w32 s₁.mem base (w + 4 * k) = w32 s.mem base (w + 4 * k) := O₁.w32 (by omega_arith) (by omega_arith)
    obtain tkd : w32 s₁.mem base (4 * i + (acc + 4 * k)) < 2 ^ 16 := by rw [e, tk]; exact hd k (by omega_arith)
    refine WP.mono (mulStep_ok hs₁ hb₁ hK h6₁ hp₁ (j := k) (by omega_arith) (by omega_arith)
      (by rw [K₁.gpr _ (by decide)]; exact hu) C₁ tkd) fun u ⟨m₂, b₂, K₂⟩ => ?_
    rw [e] at m₂ b₂
    obtain r2₁ : s₁.gpr .r2 = s.gpr .r2 := K₁.gpr _ (by decide)
    obtain dk : pdig s₁.mem base src k = pdig s.mem base src k := O₁.pdig (by omega_arith) (by omega_arith)
    rw [r2₁, dk, tk] at m₂ b₂
    obtain W := writeW32_outside s₁.mem base (d := w + 4 * k)
      (BitVec.ofNat 32 (((s.gpr .r2).toNat * pdig s.mem base src k + w32 s.mem base (w + 4 * k) +
        (s₁.gpr .r3).toNat) % 2 ^ 16)) (by omega_arith)
    rw [← m₂] at W
    obtain hlow : dval u.mem base w k = dval s₁.mem base w k := W.dval (by omega_arith) (by omega_arith)
    obtain htop : w32 u.mem base (w + 4 * k) = ((s.gpr .r2).toNat * pdig s.mem base src k +
        w32 s.mem base (w + 4 * k) + (s₁.gpr .r3).toNat) % 2 ^ 16 := by
      rw [m₂, w32_write_self, BitVec.toNat_ofNat]; omega_arith
    obtain hdk := hdig_lt (w32 s.mem base (src + 4 * (k / 2))) (k % 2)
    obtain hx := step_lt (d := pdig s.mem base src k) hu hdk (hd k (by omega_arith)) C₁
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega_arith)).trans (W.mono (by omega_arith) (by omega_arith)), ?_, ?_, ?_,
      K₁.trans K₂⟩
    · rw [dval, dval, pval, hlow, htop, b₂, pow16_succ]
      generalize hxd : (s.gpr .r2).toNat * pdig s.mem base src k + w32 s.mem base (w + 4 * k) +
        (s₁.gpr .r3).toNat = x at *
      obtain hx' := Nat.div_add_mod x (2 ^ 16)
      generalize 2 ^ (16 * k) = P at *
      grind
    · rw [b₂]; omega_arith
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [W.w32 (by omega_arith) (by omega_arith)]; exact D₁ j hj
      · rw [htop]; exact Nat.mod_lt _ (by decide)

/-- The carry `r3` added to the window's digits `D` and `D + 1`, when the
sum fits them. -/
theorem carryUp_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc i w D : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hp : s.gpr .r0 = s.gpr .r12 + BitVec.ofNat 32 (4 * i))
    (hw : 4 * i + acc = w) (hD : w + 4 * D + 8 ≤ size) (hd : Digs s.mem base (w + 4 * D) 2)
    (hlt : dval s.mem base (w + 4 * D) 2 + (s.gpr .r3).toNat < 2 ^ 32) :
    WP isa (.block (carryUp acc D)) s fun u =>
      Outside base (w + 4 * D) 8 s.mem u.mem ∧
      dval u.mem base (w + 4 * D) 2 = dval s.mem base (w + 4 * D) 2 + (s.gpr .r3).toNat ∧
      Digs u.mem base (w + 4 * D) 2 ∧ Rest [.r5, .r7] s u := by
  have hn := hs.nowrap
  obtain e₀ : 4 * i + (acc + 4 * D) = w + 4 * D := by omega_arith
  obtain e₁ : 4 * i + (acc + 4 * D + 4) = w + 4 * D + 4 := by omega_arith
  obtain d0 := hd 0 (by omega_arith)
  obtain d1 := hd 1 (by omega_arith)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at d0 d1
  simp only [dval, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add, Nat.pow_zero] at hlt ⊢
  simp only [carryUp]
  refine wp_ldr (hs.off_lt (by omega_arith)) (hs.ea_at hp (d := acc + 4 * D) (by omega_arith)) (hs.read (by omega_arith))
    fun s₁ u₁ => ?_
  refine wp_dp (op2_reg _ _) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  obtain K₃ : Rest [.r5, .r7] s s₃ := (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans (u₃.rest (by simp)))
  obtain hs₃ := hs.of_rest K₃ (by decide)
  obtain hp₃ : s₃.gpr .r0 = s₃.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₃.gpr _ (by decide), K₃.gpr _ (by decide)]; exact hp
  refine wp_str (hs.off_lt (by omega_arith)) (hs₃.ea_at hp₃ (d := acc + 4 * D) (by omega_arith)) (hs₃.write (by omega_arith))
    fun s₄ m₄ => ?_
  obtain K₄ : Rest [.r5, .r7] s s₄ := K₃.trans (m₄.rest _)
  obtain hs₄ := hs.of_rest K₄ (by decide)
  obtain hp₄ : s₄.gpr .r0 = s₄.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₄.gpr _ (by decide), K₄.gpr _ (by decide)]; exact hp
  refine wp_ldr (hs.off_lt (by omega_arith)) (hs₄.ea_at hp₄ (d := acc + 4 * D + 4) (by omega_arith)) (hs₄.read (by omega_arith))
    fun s₅ u₅ => ?_
  refine wp_dp (op2_lsr (by decide)) fun s₆ u₆ => ?_
  obtain K₆ : Rest [.r5, .r7] s s₆ := K₄.trans ((u₅.rest (by simp)).trans (u₆.rest (by simp)))
  obtain hs₆ := hs.of_rest K₆ (by decide)
  obtain hp₆ : s₆.gpr .r0 = s₆.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₆.gpr _ (by decide), K₆.gpr _ (by decide)]; exact hp
  refine wp_str (hs.off_lt (by omega_arith)) (hs₆.ea_at hp₆ (d := acc + 4 * D + 4) (by omega_arith)) (hs₆.write (by omega_arith))
    fun s₇ m₇ => WP.block_nil ?_
  rw [e₀] at m₄
  rw [e₁] at u₅ m₇
  -- The values.
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  obtain a1 : (s₁.gpr .r5).toNat = w32 s.mem base (w + 4 * D) := by rw [u₁.gpr, e₀]
  obtain b1 : s₁.gpr .r3 = s.gpr .r3 := u₁.other _ (by decide)
  obtain r5₂ : (s₂.gpr .r5).toNat = w32 s.mem base (w + 4 * D) + (s.gpr .r3).toNat := by
    rw [u₂.gpr, dpVal, toNat_add_lt (by rw [a1, b1]; omega_arith), a1, b1]
  obtain h6₂ : s₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact h6
  obtain r7₃ : (s₃.gpr .r7).toNat = (w32 s.mem base (w + 4 * D) + (s.gpr .r3).toNat) % 2 ^ 16 := by
    rw [u₃.gpr, dpVal, toNat_and_r6 h6₂, r5₂]
  obtain hhi : w32 s₄.mem base (w + 4 * D + 4) = w32 s.mem base (w + 4 * D + 4) := by
    rw [m₄.mem, m₃]; exact w32_write_ne hn (by omega_arith) (by omega_arith) (by omega_arith) _
  obtain a5 : (s₅.gpr .r7).toNat = w32 s.mem base (w + 4 * D + 4) := by rw [u₅.gpr]; exact hhi
  obtain b5 : s₅.gpr .r5 = s₂.gpr .r5 := by rw [u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide)]
  obtain r7₆ : (s₆.gpr .r7).toNat = w32 s.mem base (w + 4 * D + 4) +
      (w32 s.mem base (w + 4 * D) + (s.gpr .r3).toNat) / 2 ^ 16 := by
    rw [u₆.gpr, dpVal, toNat_add_lt (by rw [a5, toNat_shr, b5, r5₂]; omega_arith), a5, toNat_shr, b5, r5₂]
  obtain W₀ := writeW32_outside s.mem base (d := w + 4 * D) (s₃.gpr .r7) (by omega_arith)
  obtain W₁ := writeW32_outside (s.mem.writeW (off base (w + 4 * D)) (s₃.gpr .r7)) base
    (d := w + 4 * D + 4) (s₆.gpr .r7) (by omega_arith)
  rw [m₆, m₄.mem, m₃] at m₇
  rw [← m₇.mem] at W₁
  obtain v0 : w32 s₇.mem base (w + 4 * D) = (w32 s.mem base (w + 4 * D) + (s.gpr .r3).toNat) % 2 ^ 16 := by
    rw [m₇.mem, w32_write_ne hn (by omega_arith) (by omega_arith) (by omega_arith), w32_write_self, r7₃]
  obtain v1 : w32 s₇.mem base (w + 4 * D + 4) = w32 s.mem base (w + 4 * D + 4) +
      (w32 s.mem base (w + 4 * D) + (s.gpr .r3).toNat) / 2 ^ 16 := by
    rw [m₇.mem, w32_write_self, r7₆]
  refine ⟨(W₀.mono (Nat.le_refl _) (by omega_arith)).trans (W₁.mono (by omega_arith) (by omega_arith)), ?_, ?_,
    K₆.trans (m₇.rest _)⟩
  · rw [v0, v1]; omega_arith
  · intro j hj
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega_arith
    · simp only [Nat.mul_zero, Nat.add_zero]; rw [v0]; exact Nat.mod_lt _ (by decide)
    · simp only [Nat.mul_one]; rw [v1]; omega_arith

/-- The window `+= r2 · [src]` (`D ≤ 2W` digits of its `W` words, read at
`[rb + d]`, `rb = r12 + K`), when the sum fits the window's `D + 2` digits. -/
theorem mulRow_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc src i w W D : Nat}
    {rb : Reg} {K d : Nat} (hb : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 K) (hK : K + d = src)
    (hrb : rb ∉ [.r3, .r5, .r7])
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hp : s.gpr .r0 = s.gpr .r12 + BitVec.ofNat 32 (4 * i))
    (hw : 4 * i + acc = w) (hsrc : src + 4 * W ≤ size) (hDW : D ≤ 2 * W) (hwD : w + 4 * D + 8 ≤ size)
    (hsep : src + 4 * W ≤ w ∨ w + 4 * D + 8 ≤ src) (hu : (s.gpr .r2).toNat < 2 ^ 16)
    (hd : Digs s.mem base w (D + 2))
    (hlt : dval s.mem base w (D + 2) + (s.gpr .r2).toNat * pval s.mem base src D < 2 ^ (16 * (D + 2))) :
    WP isa (.block (mulRow acc rb d D)) s fun u =>
      Outside base w (4 * D + 8) s.mem u.mem ∧
      dval u.mem base w (D + 2) = dval s.mem base w (D + 2) + (s.gpr .r2).toNat * pval s.mem base src D ∧
      Digs u.mem base w (D + 2) ∧ Rest [.r3, .r5, .r7] s u := by
  have hn := hs.nowrap
  simp only [mulRow, List.cons_append]
  refine wp_mov (op2_imm (by decide)) fun s₀ u₀ => ?_
  obtain K₀ : Rest [.r3, .r5, .r7] s s₀ := u₀.rest (by simp)
  obtain hs₀ := hs.of_rest K₀ (by decide)
  obtain h6₀ : s₀.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₀.gpr _ (by decide)]; exact h6
  obtain hp₀ : s₀.gpr .r0 = s₀.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₀.gpr _ (by decide), K₀.gpr _ (by decide)]; exact hp
  obtain z : (s₀.gpr .r3).toNat = 0 := by rw [u₀.gpr]; rfl
  obtain hu₀ : (s₀.gpr .r2).toNat < 2 ^ 16 := by rw [K₀.gpr _ (by decide)]; exact hu
  rw [← u₀.mem] at hd hlt
  obtain hb₀ : s₀.gpr rb = s₀.gpr .r12 + BitVec.ofNat 32 K := by
    rw [K₀.gpr _ hrb, K₀.gpr _ (by decide)]; exact hb
  refine VG.Proof.X25519.Arm.WP.append (steps_ok hs₀ hb₀ hK hrb h6₀ hp₀ hw hsrc hu₀ (by rw [z]; decide) (k := D) hDW
    (by omega_arith) (by omega_arith) (hd.mono (by omega_arith))) fun s₁ ⟨O₁, V₁, C₁, D₁, K₁⟩ => ?_
  obtain K₀₁ := K₀.trans K₁
  obtain hs₁ := hs.of_rest K₀₁ (by decide)
  obtain h6₁ : s₁.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₀₁.gpr _ (by decide)]; exact h6
  obtain hp₁ : s₁.gpr .r0 = s₁.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₀₁.gpr _ (by decide), K₀₁.gpr _ (by decide)]; exact hp
  rw [z, Nat.add_zero, u₀.other _ (by decide)] at V₁
  obtain hhi : dval s₁.mem base (w + 4 * D) 2 = dval s₀.mem base (w + 4 * D) 2 := O₁.dval (by omega_arith) (by omega_arith)
  obtain hsplit : dval s₀.mem base w (D + 2) = dval s₀.mem base w D + 2 ^ (16 * D) * dval s₀.mem base (w + 4 * D) 2 :=
    dval_append _ _ _ _ _
  obtain hP : 0 < 2 ^ (16 * D) := Nat.two_pow_pos _
  obtain hlt₁ : dval s₁.mem base (w + 4 * D) 2 + (s₁.gpr .r3).toNat < 2 ^ 32 := by
    rw [hhi]
    rw [hsplit, show 16 * (D + 2) = 16 * D + 32 by omega_arith, Nat.pow_add] at hlt
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (16 * D)) ?_
    rw [Nat.mul_add]
    have := dval_lt D₁
    omega_arith
  obtain hd₁ : Digs s₁.mem base (w + 4 * D) 2 := O₁.digs (by omega_arith) (by omega_arith) hd.shift
  refine WP.mono (carryUp_ok hs₁ h6₁ hp₁ hw (by omega_arith) hd₁ hlt₁) fun u ⟨O₂, V₂, D₂, K₂⟩ =>
    ⟨?_, ?_, ?_, K₀₁.trans (K₂.mono (by simp))⟩
  · rw [u₀.mem] at O₁; exact (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))
  · rw [dval_append, V₂, O₂.dval (d := w) (k := D) (by omega_arith) (by omega_arith), hhi, ← u₀.mem, hsplit, Nat.mul_add]
    omega_arith
  · intro j hj
    by_cases hjD : j < D
    · rw [O₂.w32 (by omega_arith) (by omega_arith)]; exact D₁ j hjD
    · have := D₂ (j - D) (by omega_arith)
      rwa [show w + 4 * D + 4 * (j - D) = w + 4 * j by omega_arith] at this

end VG.Proof.Mont.Arm

end

end


/-!
# Montgomery arithmetic on 32-bit ARM: the loop of the multiplication

A digit's row (`digitRow`), at `r0 = r12 + 4i`, adds `u [b]` and then `q m`
to the window of `D + 2` digits at `acc + 4i`, which holds `T < 2m` (the
digit above it being zero): `q = t₀ m' mod 2¹⁶` makes the sum's low digit
zero, so the window one digit up holds `(T + u B + q m) / 2¹⁶`, below `2m`
again (`digitRow_ok`). An iteration of the loop (`row`) does the rows of
the two digits of a word of `[a]` (`row_ok`); `Z` is whether it was the last.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr wp_str wp_dp wp_mov wp_mul wp_movw wp_subs op2_reg op2_lsr
  op2_lsl op2_imm dpVal toNat_add_lt toNat_shr)

/-- The registers the arithmetic changes. -/
def clob : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9]

/-- The registers the multiplication's rows write: `clob` but `r4`, which
the rows leave for a pointer. -/
def rowClob : List Reg := [.r0, .r1, .r2, .r3, .r5, .r6, .r7, .r8, .r9]

/-- A register outside `rowClob` is outside any list of its registers. -/
theorem not_mem_of_rowClob {r : Reg} (h : r ∉ rowClob) {l : List Reg} (hl : ∀ x ∈ l, x ∈ rowClob := by decide) :
    r ∉ l := fun hr => h (hl r hr)

/-- A register outside `clob` is outside `rowClob`. -/
theorem not_mem_rowClob {r : Reg} (h : r ∉ clob) : r ∉ rowClob :=
  fun hr => h ((by decide : ∀ x ∈ rowClob, x ∈ clob) r hr)

/-- A register outside `clob` is outside any list of its registers. -/
theorem not_mem_of_clob {r : Reg} (h : r ∉ clob) {l : List Reg} (hl : ∀ x ∈ l, x ∈ clob := by decide) :
    r ∉ l := fun hr => h (hl r hr)

/-- `t₀ + (t₀ m' mod 2¹⁶) m ≡ 0 (mod 2¹⁶)` when `m m' ≡ -1`. -/
theorem mont_low16 (t0 minv m : Nat) (h : (m * minv + 1) % 2 ^ 16 = 0) :
    (t0 + t0 * minv % 2 ^ 16 * m) % 2 ^ 16 = 0 := by
  rw [Nat.add_mod, Nat.mul_mod (t0 * minv % 2 ^ 16), Nat.mod_mod, ← Nat.mul_mod,
    ← Nat.add_mod, show t0 + t0 * minv * m = t0 * (m * minv + 1) by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm minv m]; omega_using [],
    Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

/-- `-m⁻¹ mod 2⁶⁴` gives `-m⁻¹ mod 2¹⁶`. -/
theorem minv16_inv {M : Mod} {m : Nat} (h : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) :
    (m * (minv16 M).toNat + 1) % 2 ^ 16 = 0 := by
  rw [minv16, BitVec.toNat_setWidth, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod,
    ← Nat.mod_mod_of_dvd (m * M.minv.toNat + 1) (show 2 ^ 16 ∣ 2 ^ 64 from ⟨2 ^ 48, by decide⟩), h]

/-- A row's sum stays below `2m` once divided. -/
theorem row_lt {T u B q m : Nat} (hT : T < 2 * m) (hu : u < 2 ^ 16) (hB : B < m) (hq : q < 2 ^ 16) :
    T + u * B + q * m < 2 ^ 16 * (2 * m) := by
  obtain h1 : u * B ≤ (2 ^ 16 - 1) * B := Nat.mul_le_mul_right _ (by omega_arith)
  obtain h2 : q * m ≤ (2 ^ 16 - 1) * m := Nat.mul_le_mul_right _ (by omega_using [hq])
  omega_using [hT, hB, h1, h2]

/-- The low digit of a window of digits. -/
theorem dval_low {m : Mem} {base : Addr} {d k : Nat} (h : Digs m base d (k + 1)) :
    dval m base d (k + 1) % 2 ^ 16 = w32 m base d := by
  rw [show k + 1 = 1 + k by omega_using [], dval_append, show dval m base d 1 = w32 m base d by
    simp [dval], Nat.mul_comm, show 16 * 1 = 16 by rfl, Nat.add_mul_mod_self_right]
  have := h 0 (by omega_using [])
  simp only [Nat.mul_zero, Nat.add_zero] at this
  exact Nat.mod_eq_of_lt this

/-- The window one digit up, when the low digit is zero and the digit above
the window is zero. -/
theorem dval_shift {m : Mem} {base : Addr} {d k : Nat} (h0 : w32 m base d = 0) (htop : w32 m base (d + 4 * (k + 1)) = 0) :
    2 ^ 16 * dval m base (d + 4) (k + 1) = dval m base d (k + 1) := by
  rw [show k + 1 = 1 + k by omega_using [], dval_append m base d 1 k, show dval m base d 1 = w32 m base d by simp [dval], h0,
    Nat.zero_add, show 1 + k = k + 1 by omega_using [], dval, show d + 4 + 4 * k = d + 4 * (k + 1) by omega_using [], htop,
    show 16 * 1 = 16 by rfl]
  simp

/-- A pointer moved up 4 bytes. -/
theorem ptr_add4 (e : BitVec 32) (x : Nat) :
    e + BitVec.ofNat 32 x + 4 = e + BitVec.ofNat 32 (x + 4) := by
  rw [BitVec.add_assoc]
  refine congrArg (e + ·) ?_
  apply BitVec.eq_of_toNat_eq
  have : (4 : BitVec 32).toNat = 4 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, this]
  omega_using []

/-- A pointer moved up a word. -/
theorem ptr_succ (e : BitVec 32) (i : Nat) :
    e + BitVec.ofNat 32 (4 * i) + 4 = e + BitVec.ofNat 32 (4 * (i + 1)) := by
  rw [BitVec.add_assoc]
  refine congrArg (e + ·) ?_
  apply BitVec.eq_of_toNat_eq
  have : (4 : BitVec 32).toNat = 4 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, this]
  omega_using []

/-- What a digit's row needs of the layout: `[b]` and the modulus (`W`
words, `D = 2W` digits) apart from the window and the digit above it. -/
structure RowLay (W size w b mo : Nat) : Prop where
  b_le : b + 4 * W ≤ size
  mo_le : mo + 4 * W ≤ size
  w_le : w + 4 * (2 * W + 3) ≤ size
  sb : b + 4 * W ≤ w ∨ w + 4 * (2 * W + 3) ≤ b
  smo : mo + 4 * W ≤ w ∨ w + 4 * (2 * W + 3) ≤ mo

/-- A digit's row: from the window `T < 2m` at `w = acc + 4i` (the digit
above it zero), the window one digit up holds `(T + u B + q m) / 2¹⁶`
(`[b]` read at `[rb + d]`, `rb = r12 + K`). -/
theorem digitRow_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {W D acc b h i w m : Nat}
    {rb : Reg} {K d : Nat} (hb : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 K) (hK : K + d = b) (hrb : rb ∉ rowClob)
    (_hW : words M = W) (hD : digits M = D) (hDW : D = 2 * W) (hL : RowLay W size w b M.mo)
    (hh : h < 2) (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16)
    (hp : s.gpr .r0 = s.gpr .r12 + BitVec.ofNat 32 (4 * i)) (hw : 4 * i + acc = w)
    (hm : val32 s.mem base M.mo W = m) (hinv : (m * (minv16 M).toNat + 1) % 2 ^ 16 = 0)
    (hB : val32 s.mem base b W < m) (hd : Digs s.mem base w (D + 2))
    (hT : dval s.mem base w (D + 2) < 2 * m) (htop : w32 s.mem base (w + 4 * (D + 2)) = 0) :
    WP isa (.block (digitRow M acc rb d h)) s fun u =>
      u.gpr .r0 = u.gpr .r12 + BitVec.ofNat 32 (4 * (i + 1)) ∧
      Outside base w (4 * (D + 2)) s.mem u.mem ∧ Digs u.mem base (w + 4) (D + 2) ∧
      (∃ q, q < 2 ^ 16 ∧ 2 ^ 16 * dval u.mem base (w + 4) (D + 2) =
        dval s.mem base w (D + 2) + hdig (s.gpr .r8).toNat h * val32 s.mem base b W + q * m) ∧
      Rest [.r0, .r2, .r3, .r5, .r7] s u := by
  have hn := hs.nowrap
  obtain ⟨hb_le, hmo_le, hw_le, hsb, hsmo⟩ := hL
  subst hDW
  obtain hm0 : m < 2 ^ (16 * (2 * W)) := by
    rw [← hm, show 16 * (2 * W) = 32 * W by omega_using []]; exact val32_lt _ _ _ _
  simp only [digitRow, hD, List.cons_append, List.nil_append, List.append_assoc]
  refine wp_half hh h6 fun s₁ u₁ => ?_
  obtain K₁ : Rest [.r2, .r3, .r5, .r7] s s₁ := u₁.rest (by simp)
  obtain hs₁ := hs.of_rest K₁ (by decide)
  obtain h6₁ : s₁.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₁.gpr _ (by decide)]; exact h6
  obtain hp₁ : s₁.gpr .r0 = s₁.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [u₁.other _ (by decide), u₁.other _ (by decide)]; exact hp
  obtain hU := hdig_lt (s.gpr .r8).toNat h
  obtain hu₁ : (s₁.gpr .r2).toNat = hdig (s.gpr .r8).toNat h := by
    rw [u₁.gpr, BitVec.toNat_ofNat]; omega_using [hU]
  rw [← u₁.mem] at hm hB hd hT htop
  obtain hBp : pval s₁.mem base b (2 * W) = val32 s₁.mem base b W := pval_words _ _ _ _
  obtain hlt₁ : dval s₁.mem base w (2 * W + 2) + (s₁.gpr .r2).toNat * pval s₁.mem base b (2 * W) <
      2 ^ (16 * (2 * W + 2)) := by
    rw [hBp, hu₁, show 16 * (2 * W + 2) = 16 * (2 * W) + 32 by omega_using [], Nat.pow_add]
    have : hdig (s.gpr .r8).toNat h * val32 s₁.mem base b W ≤ (2 ^ 16 - 1) * m :=
      Nat.mul_le_mul (by omega_using [hU]) (by omega_using [hB])
    have : (2 ^ 16 - 1) * m + 2 * m < 2 ^ (16 * (2 * W)) * 2 ^ 32 := by
      have : (2 ^ 16 + 1) * m < (2 ^ 16 + 1) * 2 ^ (16 * (2 * W)) := Nat.mul_lt_mul_of_pos_left hm0 (by omega_using [])
      omega_using [this]
    omega_arith
  obtain hrb' : rb ∉ [.r3, .r5, .r7] := not_mem_of_rowClob hrb
  obtain hb₁ : s₁.gpr rb = s₁.gpr .r12 + BitVec.ofNat 32 K := by
    rw [K₁.gpr _ (not_mem_of_rowClob hrb), K₁.gpr _ (by decide)]; exact hb
  refine VG.Proof.X25519.Arm.WP.append (mulRow_ok hs₁ hb₁ hK hrb' h6₁ hp₁ hw hb_le (D := 2 * W) (Nat.le_refl _) (by omega_using [hw_le])
    (by omega_using [hsb]) (by rw [hu₁]; exact hU) hd hlt₁) fun s₂ ⟨O₂, V₂, D₂, K₂⟩ => ?_
  obtain K₁₂ := K₁.trans (K₂.mono (by simp))
  obtain hs₂ := hs.of_rest K₁₂ (by decide)
  obtain h6₂ : s₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₁₂.gpr _ (by decide)]; exact h6
  obtain hp₂ : s₂.gpr .r0 = s₂.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₁₂.gpr _ (by decide), K₁₂.gpr _ (by decide)]; exact hp
  rw [hBp, hu₁] at V₂
  -- q
  refine wp_ldr (hs.off_lt (by omega_using [hw, hw_le])) (hs₂.ea_at hp₂ (d := acc) (by omega_using [hw, hw_le]))
      (hs₂.read (by omega_using [hw, hw_le]))
    fun s₃ u₃ => ?_
  refine wp_movw fun s₄ u₄ => ?_
  refine wp_mul fun s₅ u₅ => ?_
  refine wp_dp (op2_reg _ _) fun s₆ u₆ => ?_
  obtain K₆ : Rest [.r2, .r3, .r5, .r7] s₂ s₆ :=
    ((u₃.rest (by simp)).trans (u₄.rest (by simp))).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp)))
  obtain K₁₆ := K₁₂.trans K₆
  obtain hs₆ := hs.of_rest K₁₆ (by decide)
  obtain h6₆ : s₆.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₁₆.gpr _ (by decide)]; exact h6
  obtain hp₆ : s₆.gpr .r0 = s₆.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₆.gpr _ (by decide), K₆.gpr _ (by decide)]; exact hp₂
  obtain m₆ : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  obtain ht0 : w32 s₂.mem base w = (dval s₁.mem base w (2 * W + 2) + hdig (s.gpr .r8).toNat h *
      val32 s₁.mem base b W) % 2 ^ 16 := by
    rw [← V₂, dval_low D₂]
  obtain hq : (s₆.gpr .r2).toNat = w32 s₂.mem base w * (minv16 M).toNat % 2 ^ 16 := by
    obtain h6₅ : s₅.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]; exact h6₂
    obtain hmv : (minv16 M).toNat % 2 ^ 32 = (minv16 M).toNat :=
      Nat.mod_eq_of_lt (Nat.lt_trans (minv16 M).isLt (by decide))
    rw [u₆.gpr, dpVal, toNat_and_r6 h6₅, u₅.gpr, BitVec.toNat_mul, u₄.gpr, u₄.other _ (by decide), u₃.gpr,
      BitVec.toNat_setWidth, hmv, Nat.mod_mod_of_dvd _ (show 2 ^ 16 ∣ 2 ^ 32 from ⟨2 ^ 16, by decide⟩), ← hw]
  obtain hq16 : (s₆.gpr .r2).toNat < 2 ^ 16 := by rw [hq]; exact Nat.mod_lt _ (by decide)
  rw [← m₆] at D₂ V₂ O₂
  obtain hmo₆ : val32 s₆.mem base M.mo W = m := by
    rw [O₂.val32 (by omega_using [hsmo]) (by omega_using [hn, hmo_le])]; exact hm
  obtain hMp : pval s₆.mem base M.mo (2 * W) = m := by rw [pval_words, hmo₆]
  obtain hlt₂ : dval s₆.mem base w (2 * W + 2) + (s₆.gpr .r2).toNat * pval s₆.mem base M.mo (2 * W) <
      2 ^ (16 * (2 * W + 2)) := by
    rw [hMp, V₂, show 16 * (2 * W + 2) = 16 * (2 * W) + 32 by omega_using [], Nat.pow_add]
    have hb1 : val32 s₁.mem base b W < m := hB
    have := row_lt hT hU hb1 hq16
    have : 2 ^ 16 * (2 * m) < 2 ^ (16 * (2 * W)) * 2 ^ 32 := by
      have : 2 * 2 ^ 16 * m < 2 * 2 ^ 16 * 2 ^ (16 * (2 * W)) := Nat.mul_lt_mul_of_pos_left hm0 (by omega_using [])
      omega_using [this]
    omega_arith
  refine VG.Proof.X25519.Arm.WP.append (mulRow_ok hs₆ (rb := .r12) (K := 0) (by simp) (Nat.zero_add _) (by decide)
    h6₆ hp₆ hw hmo_le (D := 2 * W) (Nat.le_refl _) (by omega_using [hw_le])
    (by omega_using [hsmo]) hq16 D₂ hlt₂) fun s₇ ⟨O₇, V₇, D₇, K₇⟩ => ?_
  obtain K₁₇ := K₁₆.trans (K₇.mono (by simp))
  refine wp_dp (op2_imm (by decide)) fun s₈ u₈ => WP.block_nil ?_
  rw [hMp, V₂] at V₇
  have m₈ : s₈.mem = s₇.mem := u₈.mem
  -- The window's low digit is zero, and the one above it too.
  generalize hT1 : dval s₁.mem base w (2 * W + 2) + hdig (s.gpr .r8).toNat h * val32 s₁.mem base b W = T1 at *
  generalize hqv : (s₆.gpr .r2).toNat = q at *
  obtain hz : w32 s₇.mem base w = 0 := by
    rw [← dval_low D₇, V₇, show (T1 + q * m) % 2 ^ 16 = (T1 % 2 ^ 16 + q * m) % 2 ^ 16 by omega_using [], hq, ← ht0]
    exact mont_low16 _ _ _ hinv
  obtain htop' : w32 s₇.mem base (w + 4 * (2 * W + 2)) = 0 := by
    rw [O₇.w32 (by omega_using []) (by omega_using [hn, hw_le]), O₂.w32 (by omega_using []) (by omega_using [hn, hw_le])]; exact htop
  obtain hsh := dval_shift hz htop'
  refine ⟨?_, ?_, ?_, ⟨q, hq16, ?_⟩, ?_⟩
  · rw [u₈.gpr, dpVal, u₈.other _ (by decide), K₇.gpr _ (by decide), K₇.gpr _ (by decide), hp₆]
    exact ptr_succ _ _
  · rw [m₈, ← u₁.mem]
    exact (O₂.mono (Nat.le_refl _) (by omega_using [])).trans (O₇.mono (Nat.le_refl _) (by omega_using []))
  · intro j hj
    rw [m₈]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [show w + 4 + 4 * j = w + 4 * (j + 1) by omega_using []]; exact D₇ (j + 1) (by omega_using [hj])
    · rw [show w + 4 + 4 * (2 * W + 1) = w + 4 * (2 * W + 2) by omega_using [], htop']; decide
  · rw [m₈, hsh, V₇, ← hT1, ← u₁.mem]
  · exact ((((K₁.trans (K₂.mono (by simp))).trans K₆).trans (K₇.mono (by simp))).mono
      (ws' := [.r0, .r2, .r3, .r5, .r7]) (by simp)).trans (u₈.rest (by simp))

/-! ## The loop -/

/-- The offsets of a multiplication: `[a]`, `[b]` and the modulus (`W`
words) in the working space and apart from the accumulator (`2D + 2 = 4W + 2`
digits at `acc`). -/
structure MulLay (W size acc a b mo : Nat) : Prop where
  acc_le : acc + 4 * (4 * W + 2) ≤ size
  a_le : a + 4 * W ≤ size
  b_le : b + 4 * W ≤ size
  mo_le : mo + 4 * W ≤ size
  sa : a + 4 * W ≤ acc ∨ acc + 4 * (4 * W + 2) ≤ a
  sb : b + 4 * W ≤ acc ∨ acc + 4 * (4 * W + 2) ≤ b
  smo : mo + 4 * W ≤ acc ∨ acc + 4 * (4 * W + 2) ≤ mo

/-- The invariant of the loop, before the iteration for word `k` of `[a]`:
the window of `D + 2` digits at `acc + 8k` holds `T < 2m` with
`2^(32 k) T ≡ A B`, for the low `2k` digits `A` of `[a]`; the digits above
it are zero; `r0` points to the window and `r1` to word `k`, from `ka` bytes
into the working space, and `r9` counts the words left. -/
structure LoopInv (base : Addr) (W acc ka a b m k : Nat) (s t : State) : Prop where
  r0 : t.gpr .r0 = t.gpr .r12 + BitVec.ofNat 32 (4 * (2 * k))
  r1 : t.gpr .r1 = t.gpr .r12 + BitVec.ofNat 32 (ka + 4 * k)
  r9 : t.gpr .r9 = BitVec.ofNat 32 (W - k)
  r6 : t.gpr .r6 = VG.Proof.X25519.Arm.mask16
  out : Outside base acc (4 * (4 * W + 2)) s.mem t.mem
  rest : Rest rowClob s t
  digs : Digs t.mem base (acc + 4 * (2 * k)) (2 * W + 2)
  zeros : ∀ l, 2 * k + 2 * W + 2 ≤ l → l < 4 * W + 2 → w32 t.mem base (acc + 4 * l) = 0
  lt : dval t.mem base (acc + 4 * (2 * k)) (2 * W + 2) < 2 * m
  cong : ∃ U, 2 ^ (32 * k) * dval t.mem base (acc + 4 * (2 * k)) (2 * W + 2) =
    pval s.mem base a (2 * k) * val32 s.mem base b W + U * m

/-- The count of the loop, one less. -/
theorem cnt_dec {W k : Nat} (hk : k < W) (hW : W < 2 ^ 32) :
    BitVec.ofNat 32 (W - k) - 1 = BitVec.ofNat 32 (W - (k + 1)) := by
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1, BitVec.toNat_ofNat]; omega_using [hk, hW]), h1, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  omega_using [hW]

/-- The congruence of the loop, two digits on. -/
theorem cong_step {P T T' T'' A B m U u0 u1 q0 q1 : Nat} (h0 : P * T = A * B + U * m)
    (h1 : 2 ^ 16 * T' = T + u0 * B + q0 * m) (h2 : 2 ^ 16 * T'' = T' + u1 * B + q1 * m) :
    P * 2 ^ 32 * T'' = (A + u0 * P + u1 * (P * 2 ^ 16)) * B + (U + q0 * P + q1 * (P * 2 ^ 16)) * m := by
  obtain e1 : P * 2 ^ 32 * T'' = P * (2 ^ 16 * T') + P * 2 ^ 16 * (u1 * B + q1 * m) := by
    rw [show P * 2 ^ 32 * T'' = P * 2 ^ 16 * (2 ^ 16 * T'') by grind, h2]; grind
  obtain e2 : P * (2 ^ 16 * T') = A * B + U * m + P * u0 * B + P * q0 * m := by
    rw [h1, Nat.mul_add, Nat.mul_add, h0]; grind
  rw [e1, e2]; grind

/-- An iteration of the loop: the rows of the two digits of word `k` (of
`[a]`, read at `[r1 + da]`, and `[b]`, at `[rb + db]`, `rb = r12 + kb`). -/
theorem row_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {W acc a b m k : Nat}
    {ka da : Nat} (hka : ka + da = a) {rb : Reg} {kb db : Nat}
    (hb : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 kb) (hkb : kb + db = b) (hrb : rb ∉ rowClob)
    (hW : words M = W) (hD : digits M = 2 * W) (hL : MulLay W size acc a b M.mo) (hk : k < W)
    (_hW32 : W < 2 ^ 31)
    (hm : val32 s.mem base M.mo W = m) (hinv : (m * (minv16 M).toNat + 1) % 2 ^ 16 = 0)
    (hB : val32 s.mem base b W < m) {t : State} (I : LoopInv base W acc ka a b m k s t) :
    WP isa (.block (row M acc da rb db)) t fun u =>
      LoopInv base W acc ka a b m (k + 1) s u ∧ u.z = decide (k + 1 = W) := by
  have hn := hs.nowrap
  obtain ⟨acc_le, a_le, b_le, mo_le, sa, sb, smo⟩ := hL
  obtain ht := hs.of_rest I.rest (by decide)
  obtain hmt : val32 t.mem base M.mo W = m := by rw [I.out.val32 (by omega_using [smo]) (by omega_using [hn, mo_le]), hm]
  obtain hbt : val32 t.mem base b W = val32 s.mem base b W := I.out.val32 (by omega_using [sb]) (by omega_using [hn, b_le])
  obtain hat : w32 t.mem base (a + 4 * k) = w32 s.mem base (a + 4 * k) := I.out.w32 (by omega_using [hk, sa]) (by omega_using [hk, hn, a_le])
  simp only [row, List.cons_append, List.nil_append, List.append_assoc]
  obtain ea : State.addr (t.gpr .r1 + BitVec.ofNat 32 da) = off base (4 * k + a) := by
    rw [show 4 * k + a = ka + 4 * k + da by omega_using [hka]]; exact ht.ea_off I.r1 (by omega_using [hka, hk, a_le])
  refine wp_ldr (hs.off_lt (d := da) (by omega_using [hka, hk, a_le])) ea (ht.read (by omega_using [hk, a_le])) fun t₁ u₁ => ?_
  obtain K₁ : Rest rowClob t t₁ := u₁.rest (by simp [rowClob])
  obtain hbR : ∀ t', Rest rowClob s t' → t'.gpr rb = t'.gpr .r12 + BitVec.ofNat 32 kb := fun t' K => by
    rw [K.gpr _ hrb, K.gpr _ (by decide)]; exact hb
  obtain ht₁ := ht.of_rest K₁ (by decide)
  obtain r8₁ : (t₁.gpr .r8).toNat = w32 s.mem base (a + 4 * k) := by
    rw [u₁.gpr, ← hat, show 4 * k + a = a + 4 * k by omega_using []]
  have m₁ : t₁.mem = t.mem := u₁.mem
  obtain L₀ : RowLay W size (acc + 4 * (2 * k)) b M.mo := ⟨b_le, mo_le,
      by omega_using [hk, acc_le], by omega_using [hk, sb], by omega_using [hk, smo]⟩
  refine VG.Proof.X25519.Arm.WP.append (digitRow_ok ht₁ (hbR _ (I.rest.trans K₁)) hkb hrb hW hD rfl L₀ (h := 0)
    (i := 2 * k) (by decide)
    (by rw [u₁.other _ (by decide)]; exact I.r6) (by rw [u₁.other _ (by decide), u₁.other _ (by decide)]; exact I.r0)
    (by omega_using []) (by rw [m₁, hmt]) hinv (by rw [m₁, hbt]; exact hB) (by rw [m₁]; exact I.digs) (by rw [m₁]; exact I.lt)
    (by rw [m₁, show acc + 4 * (2 * k) + 4 * (2 * W + 2) = acc + 4 * (2 * k + 2 * W + 2) by omega_using []];
        exact I.zeros _ (Nat.le_refl _) (by omega_using [hk]))) fun t₂ ⟨p₂, O₂, D₂, ⟨q₀, hq₀, V₂⟩, K₂⟩ => ?_
  obtain K₁₂ : Rest rowClob t t₂ := K₁.trans (K₂.mono (by simp [rowClob]))
  obtain ht₂ := ht.of_rest K₁₂ (by decide)
  rw [m₁] at O₂ V₂
  obtain hmt₂ : val32 t₂.mem base M.mo W = m := by rw [O₂.val32 (by omega_using [hk, smo]) (by omega_using [hn, mo_le]), hmt]
  obtain hbt₂ : val32 t₂.mem base b W = val32 s.mem base b W := by rw [O₂.val32 (by omega_using [hk, sb]) (by omega_using [hn, b_le]), hbt]
  rw [r8₁, hbt] at V₂
  obtain hU0 := hdig_lt (w32 s.mem base (a + 4 * k)) 0
  obtain hT' : dval t₂.mem base (acc + 4 * (2 * k) + 4) (2 * W + 2) < 2 * m := by
    have := row_lt I.lt hU0 hB hq₀
    omega_using [V₂, this]
  obtain L₁ : RowLay W size (acc + 4 * (2 * k) + 4) b M.mo := ⟨b_le, mo_le,
      by omega_using [hk, acc_le], by omega_using [hk, sb], by omega_using [hk, smo]⟩
  obtain r8₂ : t₂.gpr .r8 = t₁.gpr .r8 := K₂.gpr _ (by decide)
  refine VG.Proof.X25519.Arm.WP.append (digitRow_ok ht₂ (hbR _ (I.rest.trans K₁₂)) hkb hrb hW hD rfl L₁ (h := 1)
    (i := 2 * k + 1) (by decide)
    (by rw [K₂.gpr _ (by decide), u₁.other _ (by decide)]; exact I.r6) p₂ (by omega_using []) hmt₂ hinv
    (by rw [hbt₂]; exact hB) D₂ hT'
    (by rw [O₂.w32 (by omega_using []) (by omega_using [hk, hn, acc_le]), show acc + 4 * (2 * k) + 4 + 4 * (2 * W + 2) =
        acc + 4 * (2 * k + 2 * W + 3) by omega_using []]; exact I.zeros _ (by omega_using []) (by omega_using [hk])))
    fun t₃ ⟨p₃, O₃, D₃, ⟨q₁, hq₁, V₃⟩, K₃⟩ => ?_
  rw [r8₂, r8₁, hbt₂] at V₃
  refine wp_dp (op2_imm (by decide)) fun t₄ u₄ => ?_
  refine wp_subs (op2_imm (by decide)) fun t₅ u₅ z₅ => WP.block_nil ?_
  obtain m₅ : t₅.mem = t₃.mem := by rw [u₅.mem, u₄.mem]
  obtain r9₄ : t₄.gpr .r9 = BitVec.ofNat 32 (W - k) := by
    rw [u₄.other _ (by decide), K₃.gpr _ (by decide), K₂.gpr _ (by decide), u₁.other _ (by decide)]; exact I.r9
  obtain hU1 := hdig_lt (w32 s.mem base (a + 4 * k)) 1
  obtain hT'' : dval t₃.mem base (acc + 4 * (2 * k) + 4 + 4) (2 * W + 2) < 2 * m := by
    have := row_lt hT' hU1 hB hq₁
    omega_using [V₃, this]
  obtain e8 : acc + 4 * (2 * (k + 1)) = acc + 4 * (2 * k) + 4 + 4 := by omega_using []
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), p₃]
    congr 2
  · rw [u₅.other _ (by decide), u₄.gpr, dpVal, u₅.other _ (by decide), u₄.other _ (by decide),
      K₃.gpr _ (by decide), K₃.gpr _ (by decide), K₂.gpr _ (by decide), K₂.gpr _ (by decide), u₁.other _ (by decide),
      u₁.other _ (by decide), I.r1, ptr_add4]
    congr 2
  · rw [u₅.gpr, r9₄]; exact cnt_dec hk (by omega_using [hn, mo_le])
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), K₃.gpr _ (by decide), K₂.gpr _ (by decide),
      u₁.other _ (by decide)]; exact I.r6
  · rw [m₅]
    exact I.out.trans ((O₂.mono (by omega_using []) (by omega_using [hk])).trans (O₃.mono (by omega_using []) (by omega_using [hk])))
  · exact (I.rest.trans K₁₂).trans ((K₃.mono (by simp [rowClob])).trans
      ((u₄.rest (by simp [rowClob])).trans (u₅.rest (by simp [rowClob]))))
  · rw [m₅, e8]; exact D₃
  · intro l hl1 hl2
    rw [m₅, O₃.w32 (by omega_using [hl1]) (by omega_using [hn, acc_le, hl2]),
        O₂.w32 (by omega_using [hl1]) (by omega_using [hn, acc_le, hl2])]
    exact I.zeros l (by omega_using [hl1]) hl2
  · rw [m₅, e8]; exact hT''
  · obtain ⟨U, hU⟩ := I.cong
    refine ⟨U + q₀ * 2 ^ (32 * k) + q₁ * (2 ^ (32 * k) * 2 ^ 16), ?_⟩
    obtain hc := cong_step hU V₂ V₃
    rw [m₅, e8, show 32 * (k + 1) = 32 * k + 32 by omega_using [], Nat.pow_add,
      show 2 * (k + 1) = 2 * k + 1 + 1 by omega_using [], pval, pval, hc]
    simp only [pdig, show (2 * k + 1) / 2 = k by omega_using [], show (2 * k) / 2 = k by omega_using [],
      show (2 * k + 1) % 2 = 1 by omega_using [], show (2 * k) % 2 = 0 by omega_using [],
      show 16 * (2 * k + 1) = 32 * k + 16 by omega_using [], show 16 * (2 * k) = 32 * k by omega_using [], Nat.pow_add]
  · rw [z₅, r9₄, cnt_dec hk (by omega_using [hn, mo_le]), VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_using [hn, mo_le])]
    simp only [decide_eq_decide]
    omega_using [hk]

/-- The loop of `mulR`: from the invariant at word 0 to the invariant at `W`. -/
theorem loop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {W acc a b m : Nat}
    {ka da : Nat} (hka : ka + da = a) {rb : Reg} {kb db : Nat}
    (hb : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 kb) (hkb : kb + db = b) (hrb : rb ∉ rowClob)
    (hW : words M = W) (hD : digits M = 2 * W) (hL : MulLay W size acc a b M.mo) (hW0 : 0 < W) (hW32 : W < 2 ^ 31)
    (hm : val32 s.mem base M.mo W = m) (hinv : (m * (minv16 M).toNat + 1) % 2 ^ 16 = 0)
    (hB : val32 s.mem base b W < m) {t : State} (h0 : LoopInv base W acc ka a b m 0 s t) :
    WP isa (.loop (.block (row M acc da rb db)) .ne) t fun u => LoopInv base W acc ka a b m W s u := by
  refine WP.loop (M := isa)
    (fun n t' => ∃ k, n = W - k ∧ k < W ∧ LoopInv base W acc ka a b m k s t') ?_ W t ⟨0, rfl, hW0, h0⟩
  rintro n t' ⟨k, rfl, hk, I⟩
  refine WP.mono (row_ok hs hka hb hkb hrb hW hD hL hk hW32 hm hinv hB I) fun u ⟨I', hz⟩ => ?_
  by_cases hk1 : k + 1 = W
  · exact .inl ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_true hk1]; rfl, hk1 ▸ I'⟩
  · exact .inr ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_false hk1]; rfl, W - (k + 1), by omega_using [hk],
      k + 1, rfl, by omega_using [hk, hk1], I'⟩

end VG.Proof.Mont.Arm

end

end

/-!
# Montgomery arithmetic on 32-bit ARM: the conditional subtraction

`csub M src o` reduces the number `V < 2m` at `[src]` (`D` digits and a top
digit, 0 or 1) modulo `m` into `[o]` (`csub_ok`): the digits of `X - m`, for
the low `D` digits `X`, each `x_j + (2¹⁶ - 1 - m_j)` plus the carry from 1,
are packed into `[tmp]` with the carry out (`diffs_ok`), which plus the top
digit is 1 exactly when `V ≥ m`; its negation is the mask that selects
`V - m` or `V`, packed, into `[o]` (`sels_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr wp_str wp_dp wp_mov wp_mul wp_movw wp_subs op2_reg op2_lsr
  op2_lsl op2_imm dpVal toNat_add_lt toNat_shr toNat_shl)

/-- Two digits packed into a word. -/
theorem pack_toNat (x y : BitVec 32) (hx : x.toNat < 2 ^ 16) :
    (x ||| y <<< 16).toNat = x.toNat + y.toNat % 2 ^ 16 * 2 ^ 16 := by
  rw [BitVec.toNat_or, toNat_shl]
  obtain e : y.toNat * 2 ^ 16 % 2 ^ 32 = (y.toNat % 2 ^ 16) <<< 16 := by rw [Nat.shiftLeft_eq]; omega_arith
  rw [e, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  omega_using []

theorem toNat_mask16 : (VG.Proof.X25519.Arm.mask16).toNat = 2 ^ 16 - 1 := rfl

/-- Digit `j` of `[src] - m`: `r5 = x_j + (2¹⁶ - 1 - m_j) + c`, its carry to
`r3`, with `r7` the word of `m`. -/
theorem diffDigit_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {src j : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hj : src + 4 * j + 4 ≤ size)
    (hx : w32 s.mem base (src + 4 * j) < 2 ^ 16) (hc : (s.gpr .r3).toNat ≤ 1)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, (u.gpr .r5).toNat = w32 s.mem base (src + 4 * j) + (2 ^ 16 - 1 - hdig (s.gpr .r7).toNat (j % 2)) +
        (s.gpr .r3).toNat →
      (u.gpr .r3).toNat = (u.gpr .r5).toNat / 2 ^ 16 → u.mem = s.mem → Rest [.r3, .r4, .r5] s u →
      WP isa (.block is) u Q) :
    WP isa (.block (diffDigit src j ++ is)) s Q := by
  simp only [diffDigit, List.cons_append, List.nil_append]
  refine wp_ldr (hs.off_lt (by omega_using [hj])) (hs.ea (by omega_using [hj])) (hs.read hj) fun s₁ u₁ => ?_
  refine wp_half (Nat.mod_lt _ (by decide)) (by rw [u₁.other _ (by decide)]; exact h6) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₆ u₆ => ?_
  obtain hd : hdig (s.gpr .r7).toNat (j % 2) < 2 ^ 16 := hdig_lt _ _
  obtain a1 : (s₁.gpr .r5).toNat = w32 s.mem base (src + 4 * j) := by rw [u₁.gpr]
  obtain a2r5 : s₂.gpr .r5 = s₁.gpr .r5 := u₂.other _ (by decide)
  obtain a2r4 : (s₂.gpr .r4).toNat = hdig (s.gpr .r7).toNat (j % 2) := by
    rw [u₂.gpr, u₁.other _ (by decide), BitVec.toNat_ofNat]; omega_using [hd]
  obtain a2r6 : s₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact h6
  obtain a3 : (s₃.gpr .r5).toNat = w32 s.mem base (src + 4 * j) + (2 ^ 16 - 1) := by
    rw [u₃.gpr, dpVal, toNat_add_lt (by rw [a2r5, a1, a2r6, toNat_mask16]; omega_using [hx]), a2r5, a1, a2r6, toNat_mask16]
  obtain a3r4 : s₃.gpr .r4 = s₂.gpr .r4 := u₃.other _ (by decide)
  obtain a4 : (s₄.gpr .r5).toNat = w32 s.mem base (src + 4 * j) + (2 ^ 16 - 1 - hdig (s.gpr .r7).toNat (j % 2)) := by
    rw [u₄.gpr, dpVal, VG.Proof.X25519.Arm.toNat_sub_le (by rw [a3, a3r4, a2r4]; omega_using [hd]), a3, a3r4, a2r4]
    omega_using [hd]
  obtain a4r3 : s₄.gpr .r3 = s.gpr .r3 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain a5 : (s₅.gpr .r5).toNat = w32 s.mem base (src + 4 * j) + (2 ^ 16 - 1 - hdig (s.gpr .r7).toNat (j % 2)) +
      (s.gpr .r3).toNat := by
    rw [u₅.gpr, dpVal, toNat_add_lt (by rw [a4, a4r3]; omega_using [hx, hc]), a4, a4r3]
  refine k s₆ (by rw [u₆.other _ (by decide), a5]) (by rw [u₆.gpr, toNat_shr, u₆.other _ (by decide)])
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]) ?_
  exact (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans
    ((u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp))))))

/-- Word `k` of `[src] - m`, packed into `[tmp]`: with `c` the carry in and
`x₀`, `x₁` the digits, `[tmp + 4k] + 2³² c' + m_k = x₀ + 2¹⁶ x₁ + 2³² - 1 + c`. -/
theorem diffWord_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {src k : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hsrc : src + 4 * (2 * k + 1) + 4 ≤ size)
    (hmo : M.mo + 4 * k + 4 ≤ size) (htmp : M.tmp + 4 * k + 4 ≤ size)
    (hx0 : w32 s.mem base (src + 4 * (2 * k)) < 2 ^ 16) (hx1 : w32 s.mem base (src + 4 * (2 * k + 1)) < 2 ^ 16)
    (hc : (s.gpr .r3).toNat ≤ 1) :
    WP isa (.block (diffWord M src k)) s fun u =>
      Outside base (M.tmp + 4 * k) 4 s.mem u.mem ∧ (u.gpr .r3).toNat ≤ 1 ∧
      w32 u.mem base (M.tmp + 4 * k) + 2 ^ 32 * (u.gpr .r3).toNat + w32 s.mem base (M.mo + 4 * k) =
        w32 s.mem base (src + 4 * (2 * k)) + 2 ^ 16 * w32 s.mem base (src + 4 * (2 * k + 1)) + (2 ^ 32 - 1) +
          (s.gpr .r3).toNat ∧
      Rest [.r3, .r4, .r5, .r7, .r8] s u := by
  have hn := hs.nowrap
  simp only [diffWord, List.cons_append, List.append_assoc]
  refine wp_ldr (hs.off_lt (by omega_using [hmo])) (hs.ea (by omega_using [hmo])) (hs.read hmo) fun s₁ u₁ => ?_
  obtain hs₁ := hs.of_rest (u₁.rest (ws := [.r7]) (by simp)) (by decide)
  refine diffDigit_ok hs₁ (j := 2 * k) (by rw [u₁.other _ (by decide)]; exact h6) (by omega_using [hsrc])
    (by rw [u₁.mem]; exact hx0) (by rw [u₁.other _ (by decide)]; exact hc) fun s₂ v₂ c₂ m₂ K₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  obtain K₃ : Rest [.r3, .r4, .r5, .r7, .r8] s s₃ :=
    ((u₁.rest (by simp)).trans (K₂.mono (by simp))).trans (u₃.rest (by simp))
  obtain hs₃ := hs.of_rest K₃ (by decide)
  obtain hv0 : (s₂.gpr .r5).toNat < 2 ^ 17 := by
    obtain h1 : w32 s₁.mem base (src + 4 * (2 * k)) < 2 ^ 16 := by rw [u₁.mem]; exact hx0
    obtain h2 : (s₁.gpr .r3).toNat ≤ 1 := by rw [u₁.other _ (by decide)]; exact hc
    rw [v₂]; omega_using [h1, h2]
  refine diffDigit_ok hs₃ (j := 2 * k + 1) (by rw [K₃.gpr _ (by decide)]; exact h6) (by omega_using [hsrc])
    (by rw [u₃.mem, m₂, u₁.mem]; exact hx1) (by rw [u₃.other _ (by decide), c₂]; omega_using [hv0])
    fun s₄ v₄ c₄ m₄ K₄ => ?_
  refine wp_dp (op2_lsl (by decide)) fun s₅ u₅ => ?_
  obtain K₅ : Rest [.r3, .r4, .r5, .r7, .r8] s s₅ := (K₃.trans (K₄.mono (by simp))).trans (u₅.rest (by simp))
  obtain hs₅ := hs.of_rest K₅ (by decide)
  refine wp_str (hs.off_lt (by omega_using [htmp])) (hs₅.ea (by omega_using [htmp])) (hs₅.write htmp) fun s₆ m₆ => WP.block_nil ?_
  obtain m₅ : s₅.mem = s.mem := by rw [u₅.mem, m₄, u₃.mem, m₂, u₁.mem]
  obtain r7₃ : s₃.gpr .r7 = s₁.gpr .r7 := by rw [u₃.other _ (by decide), K₂.gpr _ (by decide)]
  obtain hr7 : (s₁.gpr .r7).toNat = w32 s.mem base (M.mo + 4 * k) := by rw [u₁.gpr]
  obtain hm := word_digits (w32 s.mem base (M.mo + 4 * k)) (BitVec.isLt _)
  obtain hd0 := hdig_lt (w32 s.mem base (M.mo + 4 * k)) 0
  obtain hd1 := hdig_lt (w32 s.mem base (M.mo + 4 * k)) 1
  obtain e0 : (s₂.gpr .r5).toNat = w32 s.mem base (src + 4 * (2 * k)) +
      (2 ^ 16 - 1 - hdig (w32 s.mem base (M.mo + 4 * k)) 0) + (s.gpr .r3).toNat := by
    rw [v₂, hr7, u₁.mem, u₁.other _ (by decide), show 2 * k % 2 = 0 by omega_using []]
  obtain e1 : (s₄.gpr .r5).toNat = w32 s.mem base (src + 4 * (2 * k + 1)) +
      (2 ^ 16 - 1 - hdig (w32 s.mem base (M.mo + 4 * k)) 1) + (s₂.gpr .r5).toNat / 2 ^ 16 := by
    rw [v₄, r7₃, hr7, u₃.mem, m₂, u₁.mem, u₃.other _ (by decide), c₂, show (2 * k + 1) % 2 = 1 by omega_using []]
  obtain h6₂ : s₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [K₂.gpr _ (by decide), u₁.other _ (by decide)]; exact h6
  obtain r8₄ : (s₄.gpr .r8).toNat = (s₂.gpr .r5).toNat % 2 ^ 16 := by
    rw [K₄.gpr _ (by decide), u₃.gpr, dpVal, toNat_and_r6 h6₂]
  obtain hw : (s₅.gpr .r8).toNat = (s₂.gpr .r5).toNat % 2 ^ 16 + (s₄.gpr .r5).toNat % 2 ^ 16 * 2 ^ 16 := by
    rw [u₅.gpr, dpVal, pack_toNat _ _ (by rw [r8₄]; omega_using []), r8₄]
  obtain r3₆ : (s₆.gpr .r3).toNat = (s₄.gpr .r5).toNat / 2 ^ 16 := by rw [m₆.gpr, u₅.other _ (by decide), c₄]
  refine ⟨?_, ?_, ?_, K₅.trans (m₆.rest _)⟩
  · rw [m₆.mem, m₅]; exact writeW32_outside _ _ _ (by omega_arith)
  · rw [r3₆, e1]; omega_using [hx1, hv0]
  · rw [m₆.mem, m₅, w32_write_self, hw, r3₆, e0, e1]
    rw [e0] at e1
    omega_using [hm, hd0, hd1, e0]

/-- The first `k` words of `[src] - m`. -/
def diffK (M : Mod) (src k : Nat) : List Instr := (List.range k).flatMap (diffWord M src)

theorem diffK_succ (M : Mod) (src k : Nat) : diffK M src (k + 1) = diffK M src k ++ diffWord M src k := by
  simp only [diffK, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The first `k` words of `[src] - m` into `[tmp]`, from the carry `c`:
`[tmp] + 2^(32k) c' + m_k + 1 = X_k + 2^(32k) + c`, for the low `2k` digits
`X_k` and words `m_k`. -/
theorem diffK_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {src : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hc : (s.gpr .r3).toNat ≤ 1) :
    ∀ {k : Nat}, src + 4 * (2 * k) ≤ size → M.mo + 4 * k ≤ size → M.tmp + 4 * k ≤ size →
    (M.tmp + 4 * k ≤ src ∨ src + 4 * (2 * k) ≤ M.tmp) → (M.tmp + 4 * k ≤ M.mo ∨ M.mo + 4 * k ≤ M.tmp) →
    Digs s.mem base src (2 * k) →
    WP isa (.block (diffK M src k)) s fun u =>
      Outside base M.tmp (4 * k) s.mem u.mem ∧ (u.gpr .r3).toNat ≤ 1 ∧
      val32 u.mem base M.tmp k + 2 ^ (32 * k) * (u.gpr .r3).toNat + val32 s.mem base M.mo k + 1 =
        dval s.mem base src (2 * k) + 2 ^ (32 * k) + (s.gpr .r3).toNat ∧
      Rest [.r3, .r4, .r5, .r7, .r8] s u
  | 0, _, _, _, _, _, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, hc,
      by simp only [val32, dval, Nat.mul_zero, Nat.pow_zero]; omega_using [], Rest.refl _ _⟩
  | k + 1, hsrc, hmo, htmp, hts, htm, hd => by
    have hn := hs.nowrap
    rw [diffK_succ]
    refine VG.Proof.X25519.Arm.WP.append (diffK_ok hs h6 hc (k := k) (by omega_using [hsrc]) (by omega_using [hmo])
        (by omega_using [htmp]) (by omega_using [hts])
      (by omega_using [htm]) (hd.mono (by omega_using []))) fun s₁ ⟨O₁, C₁, V₁, K₁⟩ => ?_
    obtain hs₁ := hs.of_rest K₁ (by decide)
    obtain x0 : w32 s₁.mem base (src + 4 * (2 * k)) = w32 s.mem base (src + 4 * (2 * k)) := O₁.w32 (by omega_using [hts])
        (by omega_using [hsrc, hn])
    obtain x1 : w32 s₁.mem base (src + 4 * (2 * k + 1)) = w32 s.mem base (src + 4 * (2 * k + 1)) :=
      O₁.w32 (by omega_using [hts]) (by omega_using [hsrc, hn])
    obtain mk : w32 s₁.mem base (M.mo + 4 * k) = w32 s.mem base (M.mo + 4 * k) := O₁.w32 (by omega_using [htm]) (by omega_using [hmo, hn])
    refine WP.mono (diffWord_ok hs₁ (k := k) (by rw [K₁.gpr _ (by decide)]; exact h6) (by omega_using [hsrc]) (by omega_using [hmo])
      (by omega_using [htmp]) (by rw [x0]; exact hd _ (by omega_using [])) (by rw [x1]; exact hd _ (by omega_using [])) C₁)
      fun u ⟨O₂, C₂, V₂, K₂⟩ => ⟨(O₁.mono (Nat.le_refl _) (by omega_using [])).trans (O₂.mono (by omega_using [])
          (by omega_using [])), C₂, ?_,
        K₁.trans K₂⟩
    rw [x0, x1, mk] at V₂
    obtain hlow : val32 u.mem base M.tmp k = val32 s₁.mem base M.tmp k := O₂.val32 (by omega_using []) (by omega_using [htmp, hn])
    rw [val32_append _ _ _ k 1, val32_append _ _ _ k 1, show 2 * (k + 1) = 2 * k + 1 + 1 by omega_using [], dval, dval,
      hlow, show 32 * (k + 1) = 32 * k + 32 by omega_using [], Nat.pow_add, show 16 * (2 * k + 1) = 32 * k + 16 by omega_using [],
      show 16 * (2 * k) = 32 * k by omega_using [], Nat.pow_add]
    simp only [val32, Nat.mul_zero, Nat.add_zero]
    generalize 2 ^ (32 * k) = P at *
    grind

/-- `x ^ ((t ^ x) & mask)`: `t` under the mask of all ones, `x` under 0. -/
theorem select_val (x t : BitVec 32) (b : Bool) :
    x ^^^ ((t ^^^ x) &&& (if b then BitVec.allOnes 32 else 0)) = if b then t else x := by
  cases b
  · simp
  · ext i hi
    simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_allOnes, ite_true, Bool.and_true]
    cases x[i] <;> cases t[i] <;> rfl

/-- Word `k` of `[o]` (written at `[ro + d]`, `ro = r12 + K`): of `[tmp]`
under the mask, else the packed digits. -/
theorem selWord_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {src o k : Nat}
    {ro : Reg} {K d : Nat} (hro : s.gpr ro = s.gpr .r12 + BitVec.ofNat 32 K) (hK : K + d = o) (hrc : ro ∉ clob)
    (b : Bool) (h3 : s.gpr .r3 = if b then BitVec.allOnes 32 else 0)
    (hsrc : src + 8 * k + 8 ≤ size) (htmp : M.tmp + 4 * k + 4 ≤ size) (ho : o + 4 * k + 4 ≤ size)
    (hx0 : w32 s.mem base (src + 8 * k) < 2 ^ 16) (hx1 : w32 s.mem base (src + 8 * k + 4) < 2 ^ 16) :
    WP isa (.block (selWord M src ro d k)) s fun u =>
      Outside base (o + 4 * k) 4 s.mem u.mem ∧
      w32 u.mem base (o + 4 * k) = (if b then w32 s.mem base (M.tmp + 4 * k) else
        w32 s.mem base (src + 8 * k) + 2 ^ 16 * w32 s.mem base (src + 8 * k + 4)) ∧
      Rest [.r5, .r7] s u := by
  have hn := hs.nowrap
  simp only [selWord]
  refine wp_ldr (hs.off_lt (by omega_using [hsrc])) (hs.ea (by omega_using [hsrc])) (hs.read (by omega_using [hsrc])) fun s₁ u₁ => ?_
  obtain hs₁ := hs.of_rest (u₁.rest (ws := [.r5, .r7]) (by simp)) (by decide)
  refine wp_ldr (hs.off_lt (by omega_using [hsrc])) (hs₁.ea (by omega_using [hsrc])) (hs₁.read (by omega_using [hsrc])) fun s₂ u₂ => ?_
  refine wp_dp (op2_lsl (by decide)) fun s₃ u₃ => ?_
  obtain K₃ : Rest [.r5, .r7] s s₃ := ((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans (u₃.rest (by simp))
  obtain hs₃ := hs.of_rest K₃ (by decide)
  refine wp_ldr (hs.off_lt (by omega_using [htmp])) (hs₃.ea (by omega_using [htmp])) (hs₃.read (by omega_using [htmp])) fun s₄ u₄ => ?_
  refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_dp (op2_reg _ _) fun s₆ u₆ => ?_
  refine wp_dp (op2_reg _ _) fun s₇ u₇ => ?_
  obtain K₇ : Rest [.r5, .r7] s s₇ := K₃.trans (((u₄.rest (by simp)).trans (u₅.rest (by simp))).trans
    ((u₆.rest (by simp)).trans (u₇.rest (by simp))))
  obtain hs₇ := hs.of_rest K₇ (by decide)
  obtain hro₇ : s₇.gpr ro = s₇.gpr .r12 + BitVec.ofNat 32 K := by
    rw [K₇.gpr _ (not_mem_of_clob hrc), K₇.gpr _ (by decide)]; exact hro
  obtain ea : State.addr (s₇.gpr ro + BitVec.ofNat 32 (d + 4 * k)) = off base (o + 4 * k) := by
    rw [← hK, Nat.add_assoc]; exact hs₇.ea_off hro₇ (by omega_using [hK, ho])
  refine wp_str (hs.off_lt (d := d + 4 * k) (by omega_using [hK, ho])) ea (hs₇.write (by omega_using [ho])) fun s₈ m₈ => WP.block_nil ?_
  obtain m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  -- r5 = x₀ | x₁ << 16
  obtain r5₃ : s₃.gpr .r5 = s.mem.readW (off base (src + 8 * k)) 32 |||
      s.mem.readW (off base (src + 8 * k + 4)) 32 <<< 16 := by
    rw [u₃.gpr, dpVal, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem]
  obtain r7₄ : s₄.gpr .r7 = s.mem.readW (off base (M.tmp + 4 * k)) 32 := by rw [u₄.gpr, m₃]
  obtain r5₆ : s₆.gpr .r5 = s₃.gpr .r5 := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide)]
  obtain r3₅ : s₅.gpr .r3 = s.gpr .r3 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), K₃.gpr _ (by decide)]
  obtain r7₆ : s₆.gpr .r7 = (s₄.gpr .r7 ^^^ s₃.gpr .r5) &&& s.gpr .r3 := by
    rw [u₆.gpr, dpVal, u₅.gpr, dpVal, u₄.other .r5 (by decide), r3₅]
  obtain r5₇ : s₇.gpr .r5 = s₃.gpr .r5 ^^^ ((s₄.gpr .r7 ^^^ s₃.gpr .r5) &&& s.gpr .r3) := by
    rw [u₇.gpr, dpVal, r5₆, r7₆]
  refine ⟨?_, ?_, K₇.trans (m₈.rest _)⟩
  · rw [m₈.mem, m₇]; exact writeW32_outside _ _ _ (by omega_using [ho, hn])
  · rw [m₈.mem, m₇, w32_write_self, r5₇, h3, select_val]
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      have e0 : w32 s.mem base (src + 8 * k) = (s.mem.readW (off base (src + 8 * k)) 32).toNat := rfl
      have e1 : w32 s.mem base (src + 8 * k + 4) = (s.mem.readW (off base (src + 8 * k + 4)) 32).toNat := rfl
      rw [e0] at hx0; rw [e1] at hx1
      rw [r5₃, pack_toNat _ _ hx0, e0, e1, Nat.mod_eq_of_lt hx1]; omega_using []
    · simp only [ite_true]; rw [r7₄]

/-- The first `k` words of the selection. -/
def selK (M : Mod) (src : Nat) (ro : Reg) (o k : Nat) : List Instr := (List.range k).flatMap (selWord M src ro o)

theorem selK_succ (M : Mod) (src : Nat) (ro : Reg) (o k : Nat) :
    selK M src ro o (k + 1) = selK M src ro o k ++ selWord M src ro o k := by
  simp only [selK, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The first `k` words of `[o]`: of `[tmp]` under the mask, else the digits
of `[src]`, packed. -/
theorem selK_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {src o : Nat}
    {ro : Reg} {K d : Nat} (hro : s.gpr ro = s.gpr .r12 + BitVec.ofNat 32 K) (hK : K + d = o) (hrc : ro ∉ clob)
    (b : Bool) (h3 : s.gpr .r3 = if b then BitVec.allOnes 32 else 0) :
    ∀ {k : Nat}, src + 8 * k ≤ size → M.tmp + 4 * k ≤ size → o + 4 * k ≤ size →
    (o + 4 * k ≤ src ∨ src + 8 * k ≤ o) → (o + 4 * k ≤ M.tmp ∨ M.tmp + 4 * k ≤ o) →
    Digs s.mem base src (2 * k) →
    WP isa (.block (selK M src ro d k)) s fun u =>
      Outside base o (4 * k) s.mem u.mem ∧
      val32 u.mem base o k = (if b then val32 s.mem base M.tmp k else dval s.mem base src (2 * k)) ∧
      Rest [.r5, .r7] s u
  | 0, _, _, _, _, _, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, by cases b <;> rfl, Rest.refl _ _⟩
  | k + 1, hsrc, htmp, ho, hos, hot, hd => by
    have hn := hs.nowrap
    rw [selK_succ]
    refine VG.Proof.X25519.Arm.WP.append (selK_ok hs hro hK hrc b h3 (k := k) (by omega_using [hsrc])
        (by omega_using [htmp]) (by omega_using [ho]) (by omega_using [hos])
      (by omega_using [hot]) (hd.mono (by omega_using []))) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_
    obtain hs₁ := hs.of_rest K₁ (by decide)
    obtain x0 : w32 s₁.mem base (src + 8 * k) = w32 s.mem base (src + 4 * (2 * k)) := by
      rw [O₁.w32 (by omega_using [hos]) (by omega_using [hsrc, hn])]; congr 1; omega_using []
    obtain x1 : w32 s₁.mem base (src + 8 * k + 4) = w32 s.mem base (src + 4 * (2 * k + 1)) := by
      rw [O₁.w32 (by omega_using [hos]) (by omega_using [hsrc, hn])]; congr 1; omega_using []
    obtain tk : w32 s₁.mem base (M.tmp + 4 * k) = w32 s.mem base (M.tmp + 4 * k) := O₁.w32 (by omega_using [hot]) (by omega_using [htmp, hn])
    obtain hro₁ : s₁.gpr ro = s₁.gpr .r12 + BitVec.ofNat 32 K := by
      rw [K₁.gpr _ (not_mem_of_clob hrc), K₁.gpr _ (by decide)]; exact hro
    refine WP.mono (selWord_ok hs₁ hro₁ hK hrc (k := k) b (by rw [K₁.gpr _ (by decide)]; exact h3)
        (by omega_using [hsrc]) (by omega_using [htmp])
      (by omega_using [ho]) (by rw [x0]; exact hd _ (by omega_using [])) (by rw [x1]; exact hd _ (by omega_using [])))
      fun u ⟨O₂, V₂, K₂⟩ => ⟨(O₁.mono (Nat.le_refl _) (by omega_using [])).trans (O₂.mono (by omega_using []) (by omega_using [])), ?_,
        K₁.trans K₂⟩
    rw [x0, x1, tk] at V₂
    obtain hlow : val32 u.mem base o k = val32 s₁.mem base o k := O₂.val32 (by omega_using []) (by omega_using [ho, hn])
    rw [val32_append _ _ _ k 1, hlow, V₁, val32_append _ _ _ k 1, show 2 * (k + 1) = 2 * k + 1 + 1 by omega_using [],
      dval, dval, show 16 * (2 * k + 1) = 32 * k + 16 by omega_arith, show 16 * (2 * k) = 32 * k by omega_using [], Nat.pow_add]
    simp only [val32, Nat.mul_zero, Nat.add_zero]
    rw [V₂]
    cases b
    · simp only [Bool.false_eq_true, ite_false]; grind
    · simp only [ite_true]

/-- The result of the conditional subtraction, from the difference's carry
`c` and the top digit `t`. -/
theorem csub_arith {X t T c m P : Nat} (hP : m < P) (_hm : 0 < m) (hV : X + P * t < 2 * m) (ht : t ≤ 1)
    (hc : c ≤ 1) (hT : T < P) (hdiff : T + P * c + m = X + P) :
    c + t ≤ 1 ∧ (if c + t = 1 then T else X) = (X + P * t) % m := by
  obtain rfl | rfl : c = 0 ∨ c = 1 := by omega_using [hc]
  all_goals obtain rfl | rfl : t = 0 ∨ t = 1 := by omega_using [ht]
  all_goals simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add] at hV hdiff ⊢
  · exact ⟨by omega_using [], by rw [Nat.mod_eq_of_lt (by omega_using [hT, hdiff])]; rfl⟩
  · refine ⟨by omega_using [], ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega_using [hdiff]), Nat.mod_eq_of_lt (by omega_using [hV])]
    simp only [ite_true]; omega_using [hdiff]
  · refine ⟨by omega_using [], ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega_using [hdiff]), Nat.mod_eq_of_lt (by omega_using [hV])]
    simp only [ite_true]; omega_using [hdiff]
  · omega_using [hP, hV, hdiff]

/-- `[o] = V mod m` for the number `V < 2m` at `[src]` (`D = 2W` digits and
the top digit), through `[tmp]`. -/
theorem csub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {W src o m : Nat}
    {ro : Reg} {K d : Nat} (hro : s.gpr ro = s.gpr .r12 + BitVec.ofNat 32 K) (hK : K + d = o) (hrc : ro ∉ clob)
    (hW : words M = W) (hD : digits M = 2 * W) (hsrc : src + 4 * (2 * W + 1) ≤ size) (ho : o + 4 * W ≤ size)
    (htmp : M.tmp + 4 * W ≤ size) (hmo : M.mo + 4 * W ≤ size)
    (hts : M.tmp + 4 * W ≤ src ∨ src + 4 * (2 * W + 1) ≤ M.tmp) (htm : M.tmp + 4 * W ≤ M.mo ∨ M.mo + 4 * W ≤ M.tmp)
    (hos : o + 4 * W ≤ src ∨ src + 4 * (2 * W + 1) ≤ o) (hot : o + 4 * W ≤ M.tmp ∨ M.tmp + 4 * W ≤ o)
    (hm : val32 s.mem base M.mo W = m) (hm0 : 0 < m) (hd : Digs s.mem base src (2 * W + 1))
    (hV : dval s.mem base src (2 * W + 1) < 2 * m) :
    WP isa (.block (csub M src ro d)) s fun u =>
      Outs base [(M.tmp, 4 * W), (o, 4 * W)] s.mem u.mem ∧
      val32 u.mem base o W = dval s.mem base src (2 * W + 1) % m ∧
      Rest [.r3, .r4, .r5, .r6, .r7, .r8] s u := by
  have hn := hs.nowrap
  simp only [csub, hW, hD, List.cons_append, List.nil_append, List.append_assoc]
  rw [show (List.range W).flatMap (diffWord M src) = diffK M src W from rfl,
    show (List.range W).flatMap (selWord M src ro d) = selK M src ro d W from rfl]
  refine wp_movw fun s₁ u₁ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  obtain K₂ : Rest [.r3, .r4, .r5, .r6, .r7, .r8] s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
  obtain hs₂ := hs.of_rest K₂ (by decide)
  obtain h6₂ : s₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [u₂.other _ (by decide), u₁.gpr]
  obtain m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  obtain c₂ : (s₂.gpr .r3).toNat = 1 := by rw [u₂.gpr]; rfl
  refine VG.Proof.X25519.Arm.WP.append (diffK_ok hs₂ h6₂ (by omega_using [c₂]) (k := W) (by omega_using [hsrc]) hmo htmp
      (by omega_using [hts]) htm
    (by rw [m₂]; exact hd.mono (by omega_using []))) fun s₃ ⟨O₃, C₃, V₃, K₃⟩ => ?_
  rw [c₂, m₂] at V₃
  rw [m₂] at O₃
  obtain K₂₃ := K₂.trans (K₃.mono (by simp))
  obtain hs₃ := hs.of_rest K₂₃ (by decide)
  refine wp_ldr (hs.off_lt (by omega_using [hsrc])) (hs₃.ea (by omega_using [hsrc])) (hs₃.read (by omega_using [hsrc])) fun s₄ u₄ => ?_
  refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₆ u₆ => ?_
  refine wp_dp (op2_reg _ _) fun s₇ u₇ => ?_
  -- The digits, the top digit, the carry.
  obtain hX : dval s.mem base src (2 * W) < 2 ^ (32 * W) := by
    rw [show 32 * W = 16 * (2 * W) by omega_using []]; exact dval_lt (hd.mono (by omega_using []))
  obtain hsplit : dval s.mem base src (2 * W + 1) = dval s.mem base src (2 * W) +
      w32 s.mem base (src + 4 * (2 * W)) * 2 ^ (32 * W) := by
    rw [dval, show 16 * (2 * W) = 32 * W by omega_using []]
  obtain htop : w32 s₃.mem base (src + 4 * (2 * W)) = w32 s.mem base (src + 4 * (2 * W)) := O₃.w32 (by omega_using [hts])
      (by omega_using [hsrc, hn])
  obtain hmP : m < 2 ^ (32 * W) := by rw [← hm]; exact val32_lt _ _ _ _
  obtain hT : val32 s₃.mem base M.tmp W < 2 ^ (32 * W) := val32_lt _ _ _ _
  obtain ht1 : w32 s.mem base (src + 4 * (2 * W)) ≤ 1 := by
    rcases Nat.lt_or_ge (w32 s.mem base (src + 4 * (2 * W))) 2 with h | h
    · omega_using [h]
    · have := Nat.mul_le_mul_right (2 ^ (32 * W)) h; omega_using [hV, hsplit, hmP, this]
  obtain ⟨hct, hres⟩ := csub_arith (X := dval s.mem base src (2 * W)) (t := w32 s.mem base (src + 4 * (2 * W)))
    (T := val32 s₃.mem base M.tmp W) (c := (s₃.gpr .r3).toNat) hmP hm0
    (by rw [hsplit, Nat.mul_comm (w32 _ _ _)] at hV; exact hV) ht1 C₃ hT (by rw [hm] at V₃; omega_using [V₃])
  -- The mask.
  obtain r5₄ : (s₄.gpr .r5).toNat = w32 s.mem base (src + 4 * (2 * W)) := by rw [u₄.gpr, ← htop]
  obtain r3₄ : s₄.gpr .r3 = s₃.gpr .r3 := u₄.other _ (by decide)
  obtain r3₅ : (s₅.gpr .r3).toNat = (s₃.gpr .r3).toNat + w32 s.mem base (src + 4 * (2 * W)) := by
    rw [u₅.gpr, dpVal, toNat_add_lt (by rw [r3₄, r5₄]; omega_using [hct]), r3₄, r5₄]
  obtain b3 : s₇.gpr .r3 = if (s₃.gpr .r3).toNat + w32 s.mem base (src + 4 * (2 * W)) = 1 then BitVec.allOnes 32
      else 0 := by
    rw [u₇.gpr, dpVal, u₆.gpr, u₆.other _ (by decide)]
    apply BitVec.eq_of_toNat_eq
    have h0 : (0 : BitVec 32).toNat = 0 := rfl
    rcases (by omega_using [hct] : (s₃.gpr .r3).toNat + w32 s.mem base (src + 4 * (2 * W)) = 0 ∨
        (s₃.gpr .r3).toNat + w32 s.mem base (src + 4 * (2 * W)) = 1) with h | h
    · rw [ite_eq_right (by omega_using [h]), h0]
      have : s₅.gpr .r3 = 0 := BitVec.eq_of_toNat_eq (by rw [r3₅, h0]; omega_using [h])
      rw [this]; rfl
    · rw [ite_eq_left h]
      have : s₅.gpr .r3 = 1 := BitVec.eq_of_toNat_eq (by rw [r3₅]; exact h)
      rw [this]; rfl
  obtain K₇ : Rest [.r3, .r4, .r5, .r6, .r7, .r8] s s₇ := K₂₃.trans (((u₄.rest (by simp)).trans (u₅.rest (by simp))).trans
    ((u₆.rest (by simp)).trans (u₇.rest (by simp))))
  obtain hs₇ := hs.of_rest K₇ (by decide)
  obtain m₇ : s₇.mem = s₃.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  obtain b3' : s₇.gpr .r3 = if decide ((s₃.gpr .r3).toNat + w32 s.mem base (src + 4 * (2 * W)) = 1) = true then
      BitVec.allOnes 32 else 0 := by simp only [decide_eq_true_eq]; exact b3
  obtain hro₇ : s₇.gpr ro = s₇.gpr .r12 + BitVec.ofNat 32 K := by
    rw [K₇.gpr _ (not_mem_of_clob hrc), K₇.gpr _ (by decide)]; exact hro
  refine WP.mono (selK_ok hs₇ hro₇ hK hrc (k := W) _ b3' (by omega_using [hsrc]) htmp ho (by omega_using [hos]) hot
    (by rw [m₇]; exact (O₃.digs (by omega_using [hts]) (by omega_using [hsrc, hn]) hd).mono (by omega_using []))) fun u ⟨O₈, V₈, K₈⟩ => ⟨?_, ?_, ?_⟩
  · rw [m₇] at O₈
    exact (Outs.of_outside O₃ (by simp)).trans (Outs.of_outside O₈ (by simp))
  · rw [V₈, m₇, O₃.dval (by omega_using [hts]) (by omega_arith), hsplit, Nat.mul_comm (w32 _ _ _), ← hres]
    by_cases h : (s₃.gpr .r3).toNat + w32 s.mem base (src + 4 * (2 * W)) = 1
    · simp only [h, ite_true, decide_true]
    · simp only [h, decide_false, Bool.false_eq_true, ite_false]
  · exact K₇.trans (K₈.mono (by simp))

end VG.Proof.Mont.Arm
