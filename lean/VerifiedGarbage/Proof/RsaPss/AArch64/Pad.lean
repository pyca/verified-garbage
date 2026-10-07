import VerifiedGarbage.Proof.RsaPss.AArch64.Basic

/-!
# RSASSA-PSS on AArch64: the padding of a message of secret length

`pad80` ORs `0x80` into byte `ℓ` of `Y` through a mask for each of its
`nbm B` bytes (`pad80_ok`), and `fixedPad80` into byte `ℓ` alone
(`fixedPad_ok`); both leave the view `v80`.
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_subImm wp_eor wp_orr wp_lsl wp_lsr
  wp_ldrb wp_strb)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_countdown ofNat_succ')

/-- `Y` with `0x80` ORed into byte `ℓ`, over its first `j` bytes. -/
def v80 (V : Nat → Byte) (ℓ j : Nat) (o : Nat) : Byte :=
  if oY ≤ o ∧ o < oY + j then V o ||| (if o - oY = ℓ then 0x80 else 0) else V o

theorem v80_zero (V : Nat → Byte) (ℓ : Nat) : v80 V ℓ 0 = V := by
  funext o; simp only [v80]; split <;> first | omega | rfl

theorem v80_succ (V : Nat → Byte) (ℓ i : Nat) (b : Byte) (hb : b = V (oY + i) ||| (if i = ℓ then 0x80 else 0)) :
    upd (v80 V ℓ i) (oY + i) b = v80 V ℓ (i + 1) := by
  funext o
  simp only [upd, v80]
  by_cases h : o = oY + i
  · subst h
    have h1 : oY ≤ oY + i ∧ oY + i < oY + (i + 1) := ⟨by omega, by omega⟩
    simp only [ite_true, hb, h1, Nat.add_sub_cancel_left, and_self]
  · simp only [h, ite_false]
    by_cases h' : oY ≤ o ∧ o < oY + i
    · have h2 : oY ≤ o ∧ o < oY + (i + 1) := ⟨h'.1, by omega⟩
      simp only [h', h2]
    · have h2 : ¬ (oY ≤ o ∧ o < oY + (i + 1)) := by omega
      simp only [h', h2, ite_false]

theorem mask80 (b : Byte) (c : Bool) :
    (BitVec.setWidth 64 b ||| ((if c then (1 : BitVec 64) else 0) <<< 7)).setWidth 8 =
      b ||| (if c then 0x80 else 0) := by
  cases c <;> revert b <;> decide

theorem ofNat_eq_iff {i ℓ : Nat} (hi : i < 2 ^ 64) (hℓ : ℓ < 2 ^ 64) :
    BitVec.ofNat 64 i = BitVec.ofNat 64 ℓ ↔ i = ℓ :=
  ⟨fun h => by
    have := congrArg BitVec.toNat h
    simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hℓ] using this, fun h => h ▸ rfl⟩

/-- `0x80` into byte `ℓ` of `Y`, through a mask for each of its first
`nbm B` bytes. -/
theorem pad80_ok (H : Hash) {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    {ℓ nbm : Nat} (hB : 2 ^ lgB H = H.P.B) (hlg : lgB H < 64) (hℓ : ℓ < 2 ^ 62) (hnb : nbm * H.P.B ≤ 2048)
    (hnb0 : 0 < nbm * H.P.B) (h22 : t.gpr .x22 = BitVec.ofNat 64 ℓ)
    (hNb : t.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm) :
    WP isa (pad80 H) t fun t' => Keep [.x10, .x11, .x12, .x13, .x14] t t' ∧
      Frame [⟨S, oRsa⟩] t.mem t'.mem ∧ Rep t'.mem S (v80 V ℓ (nbm * H.P.B)) := by
  unfold pad80
  refine WP.seq (wp_addImm (by decide) fun u₁ o₁ e₁ => wp_movz fun u₂ o₂ e₂ => ?_)
  refine wp_ldrSp (by decide) (by rw [o₂.sp, o₁.sp, L.sp, o₂.rd, o₁.rd, o₂.wr, o₁.wr]; exact L.fld (d := sNb) (n := 8) (by decide)) fun u₃ o₃ e₃ => ?_
  refine wp_lsl hlg fun u₄ o₄ e₄ => wp_nil ?_
  rw [o₂.sp, o₁.sp, L.sp, o₂.mem, o₁.mem, hNb] at e₃
  have O₄ : Only [.x10, .x11, .x12] t u₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have hn : nbm * H.P.B < 2 ^ 64 := by omega
  have hnb' : nbm ≤ nbm * H.P.B := Nat.le_mul_of_pos_right _ (Nat.pos_of_mul_pos_left hnb0)
  have c12 : u₄.gpr .x12 = BitVec.ofNat 64 (nbm * H.P.B) := by
    rw [e₄, e₃, BitVec.shiftLeft_eq_mul_twoPow]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_twoPow, hB]
    have hB' : H.P.B ≤ nbm * H.P.B := Nat.le_mul_of_pos_left _ (Nat.pos_of_mul_pos_right hnb0)
    rw [Nat.mod_eq_of_lt (show nbm < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show H.P.B < 2 ^ 64 by omega)]
  refine WP.mono (wp_countdown (cnt := .x12) hn hnb0 (fun i u => Keep [.x10, .x11, .x12, .x13, .x14] t u ∧
      u.gpr .x10 = off S (oY + i) ∧ u.gpr .x11 = BitVec.ofNat 64 i ∧
      Frame [⟨S, oRsa⟩] t.mem u.mem ∧ Rep u.mem S (v80 V ℓ i))
    (fun i hi u ⟨hK, h10, h11, hF, hR⟩ _ => ?_)
    ⟨O₄.keep.mono, by rw [Nat.add_zero, o₄.get .x10, o₃.get .x10, o₂.get .x10, e₁, L.x20],
      by rw [o₄.get .x11, o₃.get .x11, e₂]; rfl, by rw [O₄.mem]; exact Frame.refl _ _,
      by rw [v80_zero, O₄.mem]; exact R⟩ c12) fun u h => ⟨h.1, h.2.2.2⟩
  have hiY : oY + i + 1 ≤ oRsa := by unfold oY oRsa; omega
  refine wp_ldrb (by decide) (by rw [h10, BitVec.add_zero]) (by rw [hK.rd, hK.wr]; exact L.ld hiY)
    fun v₁ p₁ f₁ => ?_
  refine wp_eor fun v₂ p₂ f₂ => wp_subImm (by decide) fun v₃ p₃ f₃ => wp_lsr (by decide) fun v₄ p₄ f₄ => ?_
  refine wp_lsl (by decide) fun v₅ p₅ f₅ => wp_orr fun v₆ p₆ f₆ => ?_
  have P₆ : Only [.x13, .x14] u v₆ := (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans p₆))))).mono
  refine wp_strb (by decide) (by rw [P₆.get .x10, h10, BitVec.add_zero])
    (by rw [P₆.wr, hK.wr]; exact L.st hiY) fun v₇ m₇ => ?_
  refine wp_addImm (by decide) fun v₈ p₈ f₈ => wp_addImm (by decide) fun v₉ p₉ f₉ =>
    wp_subImm (by decide) fun v₁₀ p₁₀ f₁₀ => wp_nil ?_
  have hb : (v₆.gpr .x13).setWidth 8 = V (oY + i) ||| (if i = ℓ then 0x80 else 0) := by
    have e14 : v₄.gpr .x14 = if i = ℓ then 1 else 0 := by
      rw [f₄, f₃, f₂, p₁.get .x11, p₁.get .x22, h11, hK.get .x22, h22,
        eq1_val (by simp; omega) (by simp; omega)]
      by_cases e : i = ℓ
      · rw [ite_eq_left ((ofNat_eq_iff (by omega) (by omega)).mpr e), ite_eq_left e]
      · rw [ite_eq_right fun h' => e ((ofNat_eq_iff (by omega) (by omega)).mp h'), ite_eq_right e]
    rw [f₆, f₅, p₅.get .x13, p₄.get .x13, p₃.get .x13, p₂.get .x13, f₁, e14, hR _ (by omega)]
    have : v80 V ℓ i (oY + i) = V (oY + i) := by simp only [v80]; split <;> first | omega | rfl
    rw [this]
    by_cases e : i = ℓ
    · simp only [e, ite_true]; exact mask80 _ true
    · simp only [e, ite_false]; exact mask80 _ false
  have hm : v₁₀.mem = u.mem.writeW (off S (oY + i)) ((v₆.gpr .x13).setWidth 8) := by
    rw [p₁₀.mem, p₉.mem, p₈.mem, m₇.mem, P₆.mem]
  refine ⟨⟨(hK.trans ((P₆.keep.trans (m₇.keep.trans (p₈.keep.trans (p₉.keep.trans p₁₀.keep)))))).mono, ?_, ?_,
    ?_, ?_⟩, ?_⟩
  · rw [p₁₀.get .x10, p₉.get .x10, f₈, m₇.gpr, P₆.get .x10, h10, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_assoc]
  · rw [p₁₀.get .x11, f₉, p₈.get .x11, m₇.gpr, P₆.get .x11, h11, BitVec.ofNat_add_ofNat]
  · rw [hm]; exact hF.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by unfold oY oRsa at *; omega)
      (by unfold oY oRsa at *; omega))
  · rw [hm, ← v80_succ V ℓ i _ hb]; exact hR.wb (by omega) _
  · rw [f₁₀, p₉.get .x12, p₈.get .x12, m₇.gpr, P₆.get .x12]

end VG.Proof.RsaPss.AArch64
