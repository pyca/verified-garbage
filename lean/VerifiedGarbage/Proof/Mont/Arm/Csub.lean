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
      by simp only [val32, dval, Nat.mul_zero, Nat.pow_zero]; omega, Rest.refl _ _⟩
  | k + 1, hsrc, hmo, htmp, hts, htm, hd => by
    have hn := hs.nowrap
    rw [diffK_succ]
    refine VG.Proof.X25519.Arm.WP.append (diffK_ok hs h6 hc (k := k) (by omega) (by omega) (by omega) (by omega)
      (by omega) (hd.mono (by omega))) fun s₁ ⟨O₁, C₁, V₁, K₁⟩ => ?_
    have hs₁ := hs.of_rest K₁ (by decide)
    have x0 : w32 s₁.mem base (src + 4 * (2 * k)) = w32 s.mem base (src + 4 * (2 * k)) := O₁.w32 (by omega) (by omega)
    have x1 : w32 s₁.mem base (src + 4 * (2 * k + 1)) = w32 s.mem base (src + 4 * (2 * k + 1)) :=
      O₁.w32 (by omega) (by omega)
    have mk : w32 s₁.mem base (M.mo + 4 * k) = w32 s.mem base (M.mo + 4 * k) := O₁.w32 (by omega) (by omega)
    refine WP.mono (diffWord_ok hs₁ (k := k) (by rw [K₁.gpr _ (by decide)]; exact h6) (by omega) (by omega)
      (by omega) (by rw [x0]; exact hd _ (by omega)) (by rw [x1]; exact hd _ (by omega)) C₁)
      fun u ⟨O₂, C₂, V₂, K₂⟩ => ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega)), C₂, ?_,
        K₁.trans K₂⟩
    rw [x0, x1, mk] at V₂
    have hlow : val32 u.mem base M.tmp k = val32 s₁.mem base M.tmp k := O₂.val32 (by omega) (by omega)
    rw [val32_append _ _ _ k 1, val32_append _ _ _ k 1, show 2 * (k + 1) = 2 * k + 1 + 1 by omega, dval, dval,
      hlow, show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add, show 16 * (2 * k + 1) = 32 * k + 16 by omega,
      show 16 * (2 * k) = 32 * k by omega, Nat.pow_add]
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

/-- Word `k` of `[o]`: of `[tmp]` under the mask, else the packed digits. -/
theorem selWord_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {src o k : Nat}
    (b : Bool) (h3 : s.gpr .r3 = if b then BitVec.allOnes 32 else 0)
    (hsrc : src + 8 * k + 8 ≤ size) (htmp : M.tmp + 4 * k + 4 ≤ size) (ho : o + 4 * k + 4 ≤ size)
    (hx0 : w32 s.mem base (src + 8 * k) < 2 ^ 16) (hx1 : w32 s.mem base (src + 8 * k + 4) < 2 ^ 16) :
    WP isa (.block (selWord M src o k)) s fun u =>
      Outside base (o + 4 * k) 4 s.mem u.mem ∧
      w32 u.mem base (o + 4 * k) = (if b then w32 s.mem base (M.tmp + 4 * k) else
        w32 s.mem base (src + 8 * k) + 2 ^ 16 * w32 s.mem base (src + 8 * k + 4)) ∧
      Rest [.r5, .r7] s u := by
  have hn := hs.nowrap
  simp only [selWord]
  refine wp_ldr (hs.off_lt (by omega)) (hs.ea (by omega)) (hs.read (by omega)) fun s₁ u₁ => ?_
  have hs₁ := hs.of_rest (u₁.rest (ws := [.r5, .r7]) (by simp)) (by decide)
  refine wp_ldr (hs.off_lt (by omega)) (hs₁.ea (by omega)) (hs₁.read (by omega)) fun s₂ u₂ => ?_
  refine wp_dp (op2_lsl (by decide)) fun s₃ u₃ => ?_
  have K₃ : Rest [.r5, .r7] s s₃ := ((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans (u₃.rest (by simp))
  have hs₃ := hs.of_rest K₃ (by decide)
  refine wp_ldr (hs.off_lt (by omega)) (hs₃.ea (by omega)) (hs₃.read (by omega)) fun s₄ u₄ => ?_
  refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_dp (op2_reg _ _) fun s₆ u₆ => ?_
  refine wp_dp (op2_reg _ _) fun s₇ u₇ => ?_
  have K₇ : Rest [.r5, .r7] s s₇ := K₃.trans (((u₄.rest (by simp)).trans (u₅.rest (by simp))).trans
    ((u₆.rest (by simp)).trans (u₇.rest (by simp))))
  have hs₇ := hs.of_rest K₇ (by decide)
  refine wp_str (hs.off_lt (by omega)) (hs₇.ea (by omega)) (hs₇.write (by omega)) fun s₈ m₈ => WP.block_nil ?_
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  -- r5 = x₀ | x₁ << 16
  have r5₃ : s₃.gpr .r5 = s.mem.readW (off base (src + 8 * k)) 32 |||
      s.mem.readW (off base (src + 8 * k + 4)) 32 <<< 16 := by
    rw [u₃.gpr, dpVal, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem]
  have r7₄ : s₄.gpr .r7 = s.mem.readW (off base (M.tmp + 4 * k)) 32 := by rw [u₄.gpr, m₃]
  have r5₆ : s₆.gpr .r5 = s₃.gpr .r5 := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide)]
  have r3₅ : s₅.gpr .r3 = s.gpr .r3 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), K₃.gpr _ (by decide)]
  have r7₆ : s₆.gpr .r7 = (s₄.gpr .r7 ^^^ s₃.gpr .r5) &&& s.gpr .r3 := by
    rw [u₆.gpr, dpVal, u₅.gpr, dpVal, u₄.other .r5 (by decide), r3₅]
  have r5₇ : s₇.gpr .r5 = s₃.gpr .r5 ^^^ ((s₄.gpr .r7 ^^^ s₃.gpr .r5) &&& s.gpr .r3) := by
    rw [u₇.gpr, dpVal, r5₆, r7₆]
  refine ⟨?_, ?_, K₇.trans (m₈.rest _)⟩
  · rw [m₈.mem, m₇]; exact writeW32_outside _ _ _ (by omega)
  · rw [m₈.mem, m₇, w32_write_self, r5₇, h3, select_val]
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      have e0 : w32 s.mem base (src + 8 * k) = (s.mem.readW (off base (src + 8 * k)) 32).toNat := rfl
      have e1 : w32 s.mem base (src + 8 * k + 4) = (s.mem.readW (off base (src + 8 * k + 4)) 32).toNat := rfl
      rw [e0] at hx0; rw [e1] at hx1
      rw [r5₃, pack_toNat _ _ hx0, e0, e1, Nat.mod_eq_of_lt hx1]; omega
    · simp only [ite_true]; rw [r7₄]

end VG.Proof.Mont.Arm
