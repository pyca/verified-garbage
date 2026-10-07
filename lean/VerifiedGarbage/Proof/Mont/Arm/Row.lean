import VerifiedGarbage.Proof.Mont.Arm.Step

/-!
# Montgomery arithmetic on 32-bit ARM: a row of the multiplication

`mulRow acc src D` adds `r2 · [src]` (its `D` digits) to the window of the
accumulator at `[r0 + acc]`, `r0 = r12 + 4i` (`w = 4i + acc` from the base),
which holds digits: the `D` steps leave the carry in `r3` (`steps_ok`), which
`carryUp` adds to digits `D` and `D + 1` (`carryUp_ok`), so that the window's
`D + 2` digits hold the sum when it fits them (`mulRow_ok`).
-/

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
    have hb₁ : s₁.gpr rb = s₁.gpr .r12 + BitVec.ofNat 32 K := by
      rw [K₁.gpr _ hrb, K₁.gpr _ (by decide)]; exact hb
    have hs₁ := hs.of_rest K₁ (by decide)
    have h6₁ : s₁.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₁.gpr _ (by decide)]; exact h6
    have hp₁ : s₁.gpr .r0 = s₁.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
      rw [K₁.gpr _ (by decide), K₁.gpr _ (by decide)]; exact hp
    have e : 4 * i + (acc + 4 * k) = w + 4 * k := by omega_arith
    have tk : w32 s₁.mem base (w + 4 * k) = w32 s.mem base (w + 4 * k) := O₁.w32 (by omega_arith) (by omega_arith)
    have tkd : w32 s₁.mem base (4 * i + (acc + 4 * k)) < 2 ^ 16 := by rw [e, tk]; exact hd k (by omega_arith)
    refine WP.mono (mulStep_ok hs₁ hb₁ hK h6₁ hp₁ (j := k) (by omega_arith) (by omega_arith)
      (by rw [K₁.gpr _ (by decide)]; exact hu) C₁ tkd) fun u ⟨m₂, b₂, K₂⟩ => ?_
    rw [e] at m₂ b₂
    have r2₁ : s₁.gpr .r2 = s.gpr .r2 := K₁.gpr _ (by decide)
    have dk : pdig s₁.mem base src k = pdig s.mem base src k := O₁.pdig (by omega_arith) (by omega_arith)
    rw [r2₁, dk, tk] at m₂ b₂
    have W := writeW32_outside s₁.mem base (d := w + 4 * k)
      (BitVec.ofNat 32 (((s.gpr .r2).toNat * pdig s.mem base src k + w32 s.mem base (w + 4 * k) +
        (s₁.gpr .r3).toNat) % 2 ^ 16)) (by omega_arith)
    rw [← m₂] at W
    have hlow : dval u.mem base w k = dval s₁.mem base w k := W.dval (by omega_arith) (by omega_arith)
    have htop : w32 u.mem base (w + 4 * k) = ((s.gpr .r2).toNat * pdig s.mem base src k +
        w32 s.mem base (w + 4 * k) + (s₁.gpr .r3).toNat) % 2 ^ 16 := by
      rw [m₂, w32_write_self, BitVec.toNat_ofNat]; omega_arith
    have hdk := hdig_lt (w32 s.mem base (src + 4 * (k / 2))) (k % 2)
    have hx := step_lt (d := pdig s.mem base src k) hu hdk (hd k (by omega_arith)) C₁
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega_arith)).trans (W.mono (by omega_arith) (by omega_arith)), ?_, ?_, ?_,
      K₁.trans K₂⟩
    · rw [dval, dval, pval, hlow, htop, b₂, pow16_succ]
      generalize hxd : (s.gpr .r2).toNat * pdig s.mem base src k + w32 s.mem base (w + 4 * k) +
        (s₁.gpr .r3).toNat = x at *
      have hx' := Nat.div_add_mod x (2 ^ 16)
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
  have e₀ : 4 * i + (acc + 4 * D) = w + 4 * D := by omega_arith
  have e₁ : 4 * i + (acc + 4 * D + 4) = w + 4 * D + 4 := by omega_arith
  have d0 := hd 0 (by omega_arith)
  have d1 := hd 1 (by omega_arith)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at d0 d1
  simp only [dval, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add, Nat.pow_zero] at hlt ⊢
  simp only [carryUp]
  refine wp_ldr (hs.off_lt (by omega_arith)) (hs.ea_at hp (d := acc + 4 * D) (by omega_arith)) (hs.read (by omega_arith))
    fun s₁ u₁ => ?_
  refine wp_dp (op2_reg _ _) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  have K₃ : Rest [.r5, .r7] s s₃ := (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans (u₃.rest (by simp)))
  have hs₃ := hs.of_rest K₃ (by decide)
  have hp₃ : s₃.gpr .r0 = s₃.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₃.gpr _ (by decide), K₃.gpr _ (by decide)]; exact hp
  refine wp_str (hs.off_lt (by omega_arith)) (hs₃.ea_at hp₃ (d := acc + 4 * D) (by omega_arith)) (hs₃.write (by omega_arith))
    fun s₄ m₄ => ?_
  have K₄ : Rest [.r5, .r7] s s₄ := K₃.trans (m₄.rest _)
  have hs₄ := hs.of_rest K₄ (by decide)
  have hp₄ : s₄.gpr .r0 = s₄.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₄.gpr _ (by decide), K₄.gpr _ (by decide)]; exact hp
  refine wp_ldr (hs.off_lt (by omega_arith)) (hs₄.ea_at hp₄ (d := acc + 4 * D + 4) (by omega_arith)) (hs₄.read (by omega_arith))
    fun s₅ u₅ => ?_
  refine wp_dp (op2_lsr (by decide)) fun s₆ u₆ => ?_
  have K₆ : Rest [.r5, .r7] s s₆ := K₄.trans ((u₅.rest (by simp)).trans (u₆.rest (by simp)))
  have hs₆ := hs.of_rest K₆ (by decide)
  have hp₆ : s₆.gpr .r0 = s₆.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₆.gpr _ (by decide), K₆.gpr _ (by decide)]; exact hp
  refine wp_str (hs.off_lt (by omega_arith)) (hs₆.ea_at hp₆ (d := acc + 4 * D + 4) (by omega_arith)) (hs₆.write (by omega_arith))
    fun s₇ m₇ => WP.block_nil ?_
  rw [e₀] at m₄
  rw [e₁] at u₅ m₇
  -- The values.
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  have a1 : (s₁.gpr .r5).toNat = w32 s.mem base (w + 4 * D) := by rw [u₁.gpr, e₀]
  have b1 : s₁.gpr .r3 = s.gpr .r3 := u₁.other _ (by decide)
  have r5₂ : (s₂.gpr .r5).toNat = w32 s.mem base (w + 4 * D) + (s.gpr .r3).toNat := by
    rw [u₂.gpr, dpVal, toNat_add_lt (by rw [a1, b1]; omega_arith), a1, b1]
  have h6₂ : s₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact h6
  have r7₃ : (s₃.gpr .r7).toNat = (w32 s.mem base (w + 4 * D) + (s.gpr .r3).toNat) % 2 ^ 16 := by
    rw [u₃.gpr, dpVal, toNat_and_r6 h6₂, r5₂]
  have hhi : w32 s₄.mem base (w + 4 * D + 4) = w32 s.mem base (w + 4 * D + 4) := by
    rw [m₄.mem, m₃]; exact w32_write_ne hn (by omega_arith) (by omega_arith) (by omega_arith) _
  have a5 : (s₅.gpr .r7).toNat = w32 s.mem base (w + 4 * D + 4) := by rw [u₅.gpr]; exact hhi
  have b5 : s₅.gpr .r5 = s₂.gpr .r5 := by rw [u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide)]
  have r7₆ : (s₆.gpr .r7).toNat = w32 s.mem base (w + 4 * D + 4) +
      (w32 s.mem base (w + 4 * D) + (s.gpr .r3).toNat) / 2 ^ 16 := by
    rw [u₆.gpr, dpVal, toNat_add_lt (by rw [a5, toNat_shr, b5, r5₂]; omega_arith), a5, toNat_shr, b5, r5₂]
  have W₀ := writeW32_outside s.mem base (d := w + 4 * D) (s₃.gpr .r7) (by omega_arith)
  have W₁ := writeW32_outside (s.mem.writeW (off base (w + 4 * D)) (s₃.gpr .r7)) base
    (d := w + 4 * D + 4) (s₆.gpr .r7) (by omega_arith)
  rw [m₆, m₄.mem, m₃] at m₇
  rw [← m₇.mem] at W₁
  have v0 : w32 s₇.mem base (w + 4 * D) = (w32 s.mem base (w + 4 * D) + (s.gpr .r3).toNat) % 2 ^ 16 := by
    rw [m₇.mem, w32_write_ne hn (by omega_arith) (by omega_arith) (by omega_arith), w32_write_self, r7₃]
  have v1 : w32 s₇.mem base (w + 4 * D + 4) = w32 s.mem base (w + 4 * D + 4) +
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
  have K₀ : Rest [.r3, .r5, .r7] s s₀ := u₀.rest (by simp)
  have hs₀ := hs.of_rest K₀ (by decide)
  have h6₀ : s₀.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₀.gpr _ (by decide)]; exact h6
  have hp₀ : s₀.gpr .r0 = s₀.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₀.gpr _ (by decide), K₀.gpr _ (by decide)]; exact hp
  have z : (s₀.gpr .r3).toNat = 0 := by rw [u₀.gpr]; rfl
  have hu₀ : (s₀.gpr .r2).toNat < 2 ^ 16 := by rw [K₀.gpr _ (by decide)]; exact hu
  rw [← u₀.mem] at hd hlt
  have hb₀ : s₀.gpr rb = s₀.gpr .r12 + BitVec.ofNat 32 K := by
    rw [K₀.gpr _ hrb, K₀.gpr _ (by decide)]; exact hb
  refine VG.Proof.X25519.Arm.WP.append (steps_ok hs₀ hb₀ hK hrb h6₀ hp₀ hw hsrc hu₀ (by rw [z]; decide) (k := D) hDW
    (by omega_arith) (by omega_arith) (hd.mono (by omega_arith))) fun s₁ ⟨O₁, V₁, C₁, D₁, K₁⟩ => ?_
  have K₀₁ := K₀.trans K₁
  have hs₁ := hs.of_rest K₀₁ (by decide)
  have h6₁ : s₁.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [K₀₁.gpr _ (by decide)]; exact h6
  have hp₁ : s₁.gpr .r0 = s₁.gpr .r12 + BitVec.ofNat 32 (4 * i) := by
    rw [K₀₁.gpr _ (by decide), K₀₁.gpr _ (by decide)]; exact hp
  rw [z, Nat.add_zero, u₀.other _ (by decide)] at V₁
  have hhi : dval s₁.mem base (w + 4 * D) 2 = dval s₀.mem base (w + 4 * D) 2 := O₁.dval (by omega_arith) (by omega_arith)
  have hsplit : dval s₀.mem base w (D + 2) = dval s₀.mem base w D + 2 ^ (16 * D) * dval s₀.mem base (w + 4 * D) 2 :=
    dval_append _ _ _ _ _
  have hP : 0 < 2 ^ (16 * D) := Nat.two_pow_pos _
  have hlt₁ : dval s₁.mem base (w + 4 * D) 2 + (s₁.gpr .r3).toNat < 2 ^ 32 := by
    rw [hhi]
    rw [hsplit, show 16 * (D + 2) = 16 * D + 32 by omega_arith, Nat.pow_add] at hlt
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (16 * D)) ?_
    rw [Nat.mul_add]
    have := dval_lt D₁
    omega_arith
  have hd₁ : Digs s₁.mem base (w + 4 * D) 2 := O₁.digs (by omega_arith) (by omega_arith) hd.shift
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
