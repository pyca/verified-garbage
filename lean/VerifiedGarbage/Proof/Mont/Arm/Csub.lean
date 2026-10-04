import VerifiedGarbage.Proof.Mont.Arm.Loop

/-!
# Montgomery arithmetic on 32-bit ARM: the conditional subtraction

`csub M src o` reduces the number `V < 2m` at `[src]` (`D` digits and a top
digit, 0 or 1) modulo `m` into `[o]` (`csub_ok`): the digits of `X - m`, for
the low `D` digits `X`, each `x_j + (2¹⁶ - 1 - m_j)` plus the carry from 1,
are packed into `[tmp]` with the carry out (`diffs_ok`), which plus the top
digit is 1 exactly when `V ≥ m`; its negation is the mask that selects
`V - m` or `V`, packed, into `[o]` (`sels_ok`).
-/

namespace VG.Proof.Mont.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr wp_str wp_dp wp_mov wp_mul wp_movw wp_subs op2_reg op2_lsr
  op2_lsl op2_imm dpVal toNat_add_lt toNat_shr toNat_shl)

/-- Two digits packed into a word. -/
theorem pack_toNat (x y : BitVec 32) (hx : x.toNat < 2 ^ 16) :
    (x ||| y <<< 16).toNat = x.toNat + y.toNat % 2 ^ 16 * 2 ^ 16 := by
  rw [BitVec.toNat_or, toNat_shl]
  have e : y.toNat * 2 ^ 16 % 2 ^ 32 = (y.toNat % 2 ^ 16) <<< 16 := by rw [Nat.shiftLeft_eq]; omega
  rw [e, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  omega

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
  refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read hj) fun s₁ u₁ => ?_
  refine wp_half (Nat.mod_lt _ (by decide)) (by rw [u₁.other _ (by decide)]; exact h6) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₆ u₆ => ?_
  have hd : hdig (s.gpr .r7).toNat (j % 2) < 2 ^ 16 := hdig_lt _ _
  have a1 : (s₁.gpr .r5).toNat = w32 s.mem base (src + 4 * j) := by rw [u₁.gpr]
  have a2r5 : s₂.gpr .r5 = s₁.gpr .r5 := u₂.other _ (by decide)
  have a2r4 : (s₂.gpr .r4).toNat = hdig (s.gpr .r7).toNat (j % 2) := by
    rw [u₂.gpr, u₁.other _ (by decide), BitVec.toNat_ofNat]; omega
  have a2r6 : s₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact h6
  have a3 : (s₃.gpr .r5).toNat = w32 s.mem base (src + 4 * j) + (2 ^ 16 - 1) := by
    rw [u₃.gpr, dpVal, toNat_add_lt (by rw [a2r5, a1, a2r6, toNat_mask16]; omega), a2r5, a1, a2r6, toNat_mask16]
  have a3r4 : s₃.gpr .r4 = s₂.gpr .r4 := u₃.other _ (by decide)
  have a4 : (s₄.gpr .r5).toNat = w32 s.mem base (src + 4 * j) + (2 ^ 16 - 1 - hdig (s.gpr .r7).toNat (j % 2)) := by
    rw [u₄.gpr, dpVal, VG.Proof.X25519.Arm.toNat_sub_le (by rw [a3, a3r4, a2r4]; omega), a3, a3r4, a2r4]
    omega
  have a4r3 : s₄.gpr .r3 = s.gpr .r3 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have a5 : (s₅.gpr .r5).toNat = w32 s.mem base (src + 4 * j) + (2 ^ 16 - 1 - hdig (s.gpr .r7).toNat (j % 2)) +
      (s.gpr .r3).toNat := by
    rw [u₅.gpr, dpVal, toNat_add_lt (by rw [a4, a4r3]; omega), a4, a4r3]
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
  refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read hmo) fun s₁ u₁ => ?_
  have hs₁ := hs.of_rest (u₁.rest (ws := [.r7]) (by simp)) (by decide)
  refine diffDigit_ok hs₁ (j := 2 * k) (by rw [u₁.other _ (by decide)]; exact h6) (by omega)
    (by rw [u₁.mem]; exact hx0) (by rw [u₁.other _ (by decide)]; exact hc) fun s₂ v₂ c₂ m₂ K₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  have K₃ : Rest [.r3, .r4, .r5, .r7, .r8] s s₃ :=
    ((u₁.rest (by simp)).trans (K₂.mono (by simp))).trans (u₃.rest (by simp))
  have hs₃ := hs.of_rest K₃ (by decide)
  have hv0 : (s₂.gpr .r5).toNat < 2 ^ 17 := by
    have h1 : w32 s₁.mem base (src + 4 * (2 * k)) < 2 ^ 16 := by rw [u₁.mem]; exact hx0
    have h2 : (s₁.gpr .r3).toNat ≤ 1 := by rw [u₁.other _ (by decide)]; exact hc
    rw [v₂]; omega
  refine diffDigit_ok hs₃ (j := 2 * k + 1) (by rw [K₃.gpr _ (by decide)]; exact h6) (by omega)
    (by rw [u₃.mem, m₂, u₁.mem]; exact hx1) (by rw [u₃.other _ (by decide), c₂]; omega)
    fun s₄ v₄ c₄ m₄ K₄ => ?_
  refine wp_dp (op2_lsl (by decide)) fun s₅ u₅ => ?_
  have K₅ : Rest [.r3, .r4, .r5, .r7, .r8] s s₅ := (K₃.trans (K₄.mono (by simp))).trans (u₅.rest (by simp))
  have hs₅ := hs.of_rest K₅ (by decide)
  refine wp_str (hs.off_lt (by omega)) (hs₅.ea (by omega)) (hs₅.write htmp) fun s₆ m₆ => WP.block_nil ?_
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, m₄, u₃.mem, m₂, u₁.mem]
  have r7₃ : s₃.gpr .r7 = s₁.gpr .r7 := by rw [u₃.other _ (by decide), K₂.gpr _ (by decide)]
  have hr7 : (s₁.gpr .r7).toNat = w32 s.mem base (M.mo + 4 * k) := by rw [u₁.gpr]
  have hm := word_digits (w32 s.mem base (M.mo + 4 * k)) (BitVec.isLt _)
  have hd0 := hdig_lt (w32 s.mem base (M.mo + 4 * k)) 0
  have hd1 := hdig_lt (w32 s.mem base (M.mo + 4 * k)) 1
  have e0 : (s₂.gpr .r5).toNat = w32 s.mem base (src + 4 * (2 * k)) +
      (2 ^ 16 - 1 - hdig (w32 s.mem base (M.mo + 4 * k)) 0) + (s.gpr .r3).toNat := by
    rw [v₂, hr7, u₁.mem, u₁.other _ (by decide), show 2 * k % 2 = 0 by omega]
  have e1 : (s₄.gpr .r5).toNat = w32 s.mem base (src + 4 * (2 * k + 1)) +
      (2 ^ 16 - 1 - hdig (w32 s.mem base (M.mo + 4 * k)) 1) + (s₂.gpr .r5).toNat / 2 ^ 16 := by
    rw [v₄, r7₃, hr7, u₃.mem, m₂, u₁.mem, u₃.other _ (by decide), c₂, show (2 * k + 1) % 2 = 1 by omega]
  have h6₂ : s₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [K₂.gpr _ (by decide), u₁.other _ (by decide)]; exact h6
  have r8₄ : (s₄.gpr .r8).toNat = (s₂.gpr .r5).toNat % 2 ^ 16 := by
    rw [K₄.gpr _ (by decide), u₃.gpr, dpVal, toNat_and_r6 h6₂]
  have hw : (s₅.gpr .r8).toNat = (s₂.gpr .r5).toNat % 2 ^ 16 + (s₄.gpr .r5).toNat % 2 ^ 16 * 2 ^ 16 := by
    rw [u₅.gpr, dpVal, pack_toNat _ _ (by rw [r8₄]; omega), r8₄]
  have r3₆ : (s₆.gpr .r3).toNat = (s₄.gpr .r5).toNat / 2 ^ 16 := by rw [m₆.gpr, u₅.other _ (by decide), c₄]
  refine ⟨?_, ?_, ?_, K₅.trans (m₆.rest _)⟩
  · rw [m₆.mem, m₅]; exact writeW32_outside _ _ _ (by omega)
  · rw [r3₆, e1]; omega
  · rw [m₆.mem, m₅, w32_write_self, hw, r3₆, e0, e1]
    rw [e0] at e1
    omega

end VG.Proof.Mont.Arm
