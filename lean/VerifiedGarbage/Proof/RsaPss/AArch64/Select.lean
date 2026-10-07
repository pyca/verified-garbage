import VerifiedGarbage.Proof.RsaPss.AArch64.PadLen

/-!
# RSASSA-PSS on AArch64: selecting the hash value of the last block

`select` copies the `N`-byte hash value at `scratch + oSt` to
`scratch + oSel` under the mask of `b = ⌊(ℓ + L) / B⌋`, a byte at a time
(`select_ok`).
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_subImm wp_eor wp_orr wp_and wp_lsl
  wp_lsr wp_ldrb wp_strb wp_sub)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_countdown wp_mov)
open VG.Proof.RsaPss.AArch64.LenLoop (lsr_val mask_val)

/-- The hash value's `N` bytes copied from `oSt` to `oSel` if `c`. -/
def vSel (V : Nat → Byte) (c : Prop) [Decidable c] (j : Nat) (o : Nat) : Byte :=
  if c ∧ oSel ≤ o ∧ o < oSel + j then V (oSt + (o - oSel)) else V o

theorem vSel_zero (V : Nat → Byte) (c : Prop) [Decidable c] : vSel V c 0 = V := by
  funext o; simp only [vSel]; split <;> first | omega | rfl

theorem vSel_succ (V : Nat → Byte) (c : Prop) [Decidable c] {j : Nat} :
    upd (vSel V c j) (oSel + j) (if c then V (oSt + j) else V (oSel + j)) = vSel V c (j + 1) := by
  funext o
  simp only [upd, vSel]
  by_cases e : o = oSel + j
  · subst e
    rw [ite_eq_left rfl]
    by_cases h : c
    · rw [ite_eq_left h, ite_eq_left ⟨h, by omega, by omega⟩, Nat.add_sub_cancel_left]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.1)]
  · rw [ite_eq_right e]
    have hc : (c ∧ oSel ≤ o ∧ o < oSel + (j + 1)) ↔ (c ∧ oSel ≤ o ∧ o < oSel + j) := by
      constructor
      · rintro ⟨h₁, h₂, h₃⟩; exact ⟨h₁, h₂, by omega⟩
      · rintro ⟨h₁, h₂, h₃⟩; exact ⟨h₁, h₂, by omega⟩
    simp only [hc]

theorem byte_sel (a s : Byte) (c : Prop) [Decidable c] :
    (BitVec.setWidth 64 s ^^^ ((BitVec.setWidth 64 a ^^^ BitVec.setWidth 64 s) &&&
      (if c then BitVec.allOnes 64 else 0))).setWidth 8 = if c then a else s := by
  by_cases h : c
  · simp only [h, ite_true, BitVec.and_allOnes]
    ext i hi; simp; cases a[i] <;> cases s[i] <;> rfl
  · simp only [h, ite_false]
    apply BitVec.eq_of_toNat_eq; simp

/-- `select`, from `b` in `x27` and `ℓ` in `x22`. -/
theorem select_ok (H : Hash) {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    {ℓ b : Nat} (hB : 2 ^ lgB H = H.P.B) (hlg : lgB H < 64) (hN : 0 < H.P.N) (hN' : H.P.N ≤ 64)
    (hL : H.P.L ≤ 16) (hℓ : ℓ < 2 ^ 62) (hb : b < 2 ^ 62)
    (h22 : t.gpr .x22 = BitVec.ofNat 64 ℓ) (h27 : t.gpr .x27 = BitVec.ofNat 64 b) :
    WP isa (select H) t fun t' => Keep [.x15, .x9, .x13, .x10, .x11, .x12, .x14] t t' ∧
      Frame [⟨S, oRsa⟩] t.mem t'.mem ∧
      Rep t'.mem S (vSel V (b = (ℓ + H.P.L) / H.P.B) H.P.N) := by
  generalize hfbd : (ℓ + H.P.L) / H.P.B = fb
  unfold select lastBlk eqMask eq1
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_addImm (by omega) fun u₁ o₁ e₁ => wp_lsr hlg fun u₂ o₂ e₂ => wp_eor fun u₃ o₃ e₃ =>
    wp_subImm (by decide) fun u₄ o₄ e₄ => wp_lsr (by decide) fun u₅ o₅ e₅ => wp_movz fun u₆ o₆ e₆ =>
    wp_sub fun u₇ o₇ e₇ => wp_addImm (by decide) fun u₈ o₈ e₈ => wp_addImm (by decide) fun u₉ o₉ e₉ =>
    wp_movz fun u₁₀ o₁₀ e₁₀ => wp_nil ?_)
  have O : Only [.x15, .x13, .x9, .x10, .x11, .x12] t u₁₀ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans o₁₀))))))))).mono
  have hfb : fb < 2 ^ 63 := by rw [← hfbd]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have x13 : u₁₀.gpr .x13 = if b = fb then BitVec.allOnes 64 else 0 := by
    rw [o₁₀.get .x13, o₉.get .x13, o₈.get .x13, e₇, e₆, o₆.get .x13, e₅, e₄, e₃, o₂.get .x27, o₁.get .x27, h27,
      e₂, e₁, h22, BitVec.ofNat_add_ofNat, lsr_val (by omega), hB, hfbd, mask_val (by simp; omega) (by simp; omega)]
    by_cases e : b = fb
    · rw [ite_eq_left (by rw [e]), ite_eq_left e]
    · rw [ite_eq_right fun h' => e ((ofNat_eq_iff (by omega) (by omega)).mp h'), ite_eq_right e]
  refine WP.mono (wp_countdown (cnt := .x12) (N := H.P.N) (by omega) hN
    (fun j v => Keep [.x14, .x15, .x10, .x11, .x12] u₁₀ v ∧ v.gpr .x10 = off S (oSt + j) ∧
      v.gpr .x11 = off S (oSel + j) ∧ Frame [⟨S, oRsa⟩] t.mem v.mem ∧ Rep v.mem S (vSel V (b = fb) j))
    (fun j hj v ⟨hK, h10, h11, hF, hR⟩ _ => ?_)
    ⟨Keep.refl _ _, by rw [Nat.add_zero, o₁₀.get .x10, o₉.get .x10, e₈, o₇.get .x20, o₆.get .x20, o₅.get .x20,
      o₄.get .x20, o₃.get .x20, o₂.get .x20, o₁.get .x20, L.x20],
      by rw [Nat.add_zero, o₁₀.get .x11, e₉, o₈.get .x20, o₇.get .x20, o₆.get .x20, o₅.get .x20,
      o₄.get .x20, o₃.get .x20, o₂.get .x20, o₁.get .x20, L.x20], by rw [O.mem]; exact Frame.refl _ _,
      by rw [O.mem, vSel_zero]; exact R⟩
    (by rw [e₁₀]; apply BitVec.eq_of_toNat_eq; simp; omega))
    fun v ⟨hK, _, _, hF, hR⟩ => ⟨(O.keep.trans hK).mono, hF, hR⟩
  have rd : v.rd = t.rd := by rw [hK.rd, O.rd]
  have wr : v.wr = t.wr := by rw [hK.wr, O.wr]
  have h1 : oSt + j + 1 ≤ oRsa := by unfold oSt oRsa; omega
  have h2 : oSel + j + 1 ≤ oRsa := by unfold oSel oRsa; omega
  refine wp_ldrb (by decide) (by rw [h10, BitVec.add_zero]) (by rw [rd, wr]; exact L.ld h1) fun w₁ q₁ g₁ => ?_
  refine wp_ldrb (by decide) (by rw [q₁.get .x11, h11, BitVec.add_zero]) (by rw [q₁.rd, q₁.wr, rd, wr]; exact L.ld h2)
    fun w₂ q₂ g₂ => wp_eor fun w₃ q₃ g₃ => wp_and fun w₄ q₄ g₄ => wp_eor fun w₅ q₅ g₅ => ?_
  have Q₅ : Only [.x14, .x15] v w₅ := (q₁.trans (q₂.trans (q₃.trans (q₄.trans q₅)))).mono
  refine wp_strb (by decide) (by rw [Q₅.get .x11, h11, BitVec.add_zero]) (by rw [Q₅.wr, wr]; exact L.st h2)
    fun w₆ m₆ => wp_addImm (by decide) fun w₇ q₇ g₇ => wp_addImm (by decide) fun w₈ q₈ g₈ =>
    wp_subImm (by decide) fun w₉ q₉ g₉ => wp_nil ?_
  have ha : v.mem (off S (oSt + j)) = V (oSt + j) := by
    rw [hR _ (by omega)]; simp only [vSel]; rw [ite_eq_right (by unfold oSt oSel; omega)]
  have hs : v.mem (off S (oSel + j)) = V (oSel + j) := by
    rw [hR _ (by omega)]; simp only [vSel]; rw [ite_eq_right (by omega)]
  have hb' : (w₅.gpr .x15).setWidth 8 = if b = fb then V (oSt + j) else V (oSel + j) := by
    rw [g₅, q₄.get .x15, g₄, q₃.get .x15, g₃, q₂.get .x14, g₁, g₂, q₁.mem, ha, hs, q₃.get .x13, q₂.get .x13,
      q₁.get .x13, hK.get .x13, x13]
    exact byte_sel _ _ _
  have hm : w₉.mem = v.mem.writeW (off S (oSel + j)) ((w₅.gpr .x15).setWidth 8) := by
    rw [q₉.mem, q₈.mem, q₇.mem, m₆.mem, Q₅.mem]
  refine ⟨⟨(hK.trans (Q₅.keep.trans (m₆.keep.trans (q₇.keep.trans (q₈.keep.trans q₉.keep))))).mono, ?_, ?_,
    ?_, ?_⟩, ?_⟩
  · rw [q₉.get .x10, q₈.get .x10, g₇, m₆.gpr, Q₅.get .x10, h10, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      Nat.add_assoc]
  · rw [q₉.get .x11, g₈, q₇.get .x11, m₆.gpr, Q₅.get .x11, h11, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      Nat.add_assoc]
  · rw [hm]
    exact hF.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by unfold oRsa at *; omega))
  · rw [hm, hb', ← vSel_succ V _]
    exact hR.wb (by omega) _
  · rw [g₉, q₈.get .x12, q₇.get .x12, m₆.gpr, Q₅.get .x12]

end VG.Proof.RsaPss.AArch64
