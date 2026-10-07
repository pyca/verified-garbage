import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyScan

/-!
# RSASSA-PSS verification on AArch64: the shift of `DB`

One pass of `shift` replaces each of the `dbLen` bytes of `DB`'s place in
`Y` with the one `d` bytes after it if bit 0 of `a` is set (`shiftPass_ok`);
ten passes, with `a = pos + 1` halved and `d` doubled each time, shift it by
`pos + 1` (`shift_ok`).
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_subImm wp_lsr wp_lsl wp_ldrb wp_strb
  wp_and wp_eor wp_sub wp_add)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_mov wp_countdown wp_ldrSp)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)

/-- `V` with the `n` bytes from `o` replaced by those `d` bytes after them,
if `c`. -/
def shV (V : Nat → Byte) (o n d : Nat) (c : Prop) [Decidable c] (x : Nat) : Byte :=
  if c ∧ o ≤ x ∧ x < o + n then V (x + d) else V x

theorem shV_zero (V : Nat → Byte) (o d : Nat) (c : Prop) [Decidable c] : shV V o 0 d c = V := by
  funext x; simp only [shV]; rw [ite_eq_right (by omega)]

theorem mask_bit (a : Nat) (ha : a < 2 ^ 63) :
    0#64 - (BitVec.ofNat 64 a - (BitVec.ofNat 64 a >>> 1) <<< 1) =
      if a % 2 = 1 then BitVec.allOnes 64 else 0#64 := by
  have e : BitVec.ofNat 64 a - (BitVec.ofNat 64 a >>> 1) <<< 1 = BitVec.ofNat 64 (a % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (a := a) (by omega)]
    have := Nat.div_add_mod a 2
    have h2 : a / 2 ^ 1 * 2 ^ 1 % 2 ^ 64 = a / 2 * 2 := Nat.mod_eq_of_lt (by omega)
    rw [h2]
    omega
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one a with h | h <;> rw [h] <;> decide

theorem shiftPass_ok (H : Hash) {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    {db d a : Nat} (hdb : 0 < db) (hD : H.D ≤ 64) (hfit : oY + 8 + H.D + db + d ≤ oRsa) (ha : a < 2 ^ 63)
    (h28 : t.gpr .x28 = BitVec.ofNat 64 d) (h27 : t.gpr .x27 = BitVec.ofNat 64 a)
    (h25 : t.gpr .x25 = BitVec.ofNat 64 db) :
    WP isa (shiftPass H) t fun t' => Keep [.x10, .x11, .x14, .x9, .x12, .x15] t t' ∧
      Frame [⟨S, oRsa⟩] t.mem t'.mem ∧ Rep t'.mem S (shV V (oY + 8 + H.D) db d (a % 2 = 1)) := by
  have c6 : oRsa = 8192 := rfl
  have c2 : oY = 3584 := rfl
  unfold shiftPass
  refine WP.seq (WP.mono (Q := fun (u : State) => Only [.x10, .x11, .x14, .x9, .x12] t u ∧
      u.gpr .x10 = off S (oY + 8 + H.D) ∧ u.gpr .x11 = off S (oY + 8 + H.D + d) ∧
      u.gpr .x14 = (if a % 2 = 1 then BitVec.allOnes 64 else 0#64) ∧ u.gpr .x12 = BitVec.ofNat 64 db) ?_
    fun u ⟨O, h10, h11, h14, h12⟩ => ?_)
  · refine wp_addImm (by omega) fun u₁ o₁ e₁ => wp_add fun u₂ o₂ e₂ => wp_lsr (by decide) fun u₃ o₃ e₃ =>
      wp_lsl (by decide) fun u₄ o₄ e₄ => wp_sub fun u₅ o₅ e₅ => wp_movz fun u₆ o₆ e₆ => wp_sub fun u₇ o₇ e₇ =>
      wp_mov fun u₈ o₈ e₈ => wp_nil ⟨(o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans
        o₈))))))).mono, ?_, ?_, ?_, ?_⟩
    · rw [o₈.get .x10, o₇.get .x10, o₆.get .x10, o₅.get .x10, o₄.get .x10, o₃.get .x10, o₂.get .x10, e₁, L.x20]
    · rw [o₈.get .x11, o₇.get .x11, o₆.get .x11, o₅.get .x11, o₄.get .x11, o₃.get .x11, e₂, o₁.get .x28, h28, e₁,
        L.x20, off_add]
    · rw [o₈.get .x14, e₇, e₆, o₆.get .x14, e₅, e₄, e₃, o₂.get .x27, o₁.get .x27, h27, o₄.get .x27,
        o₃.get .x27, o₂.get .x27, o₁.get .x27, h27, ← mask_bit a ha]
      rfl
    · rw [e₈, o₇.get .x25, o₆.get .x25, o₅.get .x25, o₄.get .x25, o₃.get .x25, o₂.get .x25, o₁.get .x25, h25]
  have Lu : Lay u F S := L.congr O.sp O.wr (O.get .x20)
  have Ru : Rep u.mem S V := O.mem ▸ R
  refine WP.mono (wp_countdown (cnt := .x12) (N := db) (by omega) hdb
    (fun j v => Keep [.x15, .x9, .x10, .x11, .x12] u v ∧ v.gpr .x10 = off S (oY + 8 + H.D + j) ∧
      v.gpr .x11 = off S (oY + 8 + H.D + j + d) ∧ Frame [⟨S, oRsa⟩] u.mem v.mem ∧
      Rep v.mem S (shV V (oY + 8 + H.D) j d (a % 2 = 1)))
    (fun j hj v ⟨hK, h10', h11', hF, hR⟩ _ => ?_)
    ⟨Keep.refl _ _, by rw [Nat.add_zero, h10], by rw [Nat.add_zero, h11], Frame.refl _ _, by rw [shV_zero]; exact Ru⟩
    h12) fun v ⟨hK, _, _, hF, hR⟩ => ⟨(O.keep.trans hK).mono, O.mem ▸ hF, hR⟩
  refine wp_ldrb (by decide) (by rw [h10', BitVec.add_zero]) (by rw [hK.rd, hK.wr]; exact Lu.ld (by omega))
    fun w₁ q₁ g₁ => ?_
  refine wp_ldrb (by decide) (by rw [q₁.get .x11, h11', BitVec.add_zero])
    (by rw [q₁.rd, q₁.wr, hK.rd, hK.wr]; exact Lu.ld (by omega)) fun w₂ q₂ g₂ => wp_eor fun w₃ q₃ g₃ =>
    wp_and fun w₄ q₄ g₄ => wp_eor fun w₅ q₅ g₅ => ?_
  have Q₅ : Only [.x15, .x9] v w₅ := (q₁.trans (q₂.trans (q₃.trans (q₄.trans q₅)))).mono
  refine wp_strb (by decide) (by rw [Q₅.get .x10, h10', BitVec.add_zero]) (by rw [Q₅.wr, hK.wr]; exact Lu.st (by omega))
    fun w₆ m₆ => wp_addImm (by decide) fun w₇ q₇ g₇ => wp_addImm (by decide) fun w₈ q₈ g₈ =>
    wp_subImm (by decide) fun w₉ q₉ g₉ => wp_nil ?_
  have hs : v.mem (off S (oY + 8 + H.D + j)) = V (oY + 8 + H.D + j) := by
    rw [hR _ (by omega)]; simp only [shV]; rw [ite_eq_right (by omega)]
  have ha' : v.mem (off S (oY + 8 + H.D + j + d)) = V (oY + 8 + H.D + j + d) := by
    rw [hR _ (by omega)]; simp only [shV]; rw [ite_eq_right (by omega)]
  have hv : (w₅.gpr .x15).setWidth 8 = if a % 2 = 1 then V (oY + 8 + H.D + j + d) else V (oY + 8 + H.D + j) := by
    rw [g₅, q₄.get .x15, q₃.get .x15, q₂.get .x15, g₁, g₄, g₃, g₂, q₁.mem, q₂.get .x15, g₁, ha', hs,
      q₃.get .x14, q₂.get .x14, q₁.get .x14, hK.get .x14, h14]
    exact byte_sel _ _ _
  have hm : w₉.mem = v.mem.writeW (off S (oY + 8 + H.D + j)) ((w₅.gpr .x15).setWidth 8) := by
    rw [q₉.mem, q₈.mem, q₇.mem, m₆.mem, Q₅.mem]
  refine ⟨⟨(hK.trans (Q₅.keep.trans (m₆.keep.trans (q₇.keep.trans (q₈.keep.trans q₉.keep))))).mono, ?_, ?_, ?_,
    ?_⟩, ?_⟩
  · rw [q₉.get .x10, q₈.get .x10, g₇, m₆.gpr, Q₅.get .x10, h10', off_add, Nat.add_assoc]
  · rw [q₉.get .x11, g₈, q₇.get .x11, m₆.gpr, Q₅.get .x11, h11', off_add,
      show oY + 8 + H.D + j + d + 1 = oY + 8 + H.D + (j + 1) + d by omega]
  · rw [hm]
    exact hF.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [hm, hv]
    refine (hR.wb (by omega) _).congr fun x _ => ?_
    simp only [upd, shV]
    by_cases e₁ : x = oY + 8 + H.D + j
    · subst e₁
      rw [ite_eq_left rfl]
      by_cases hc : a % 2 = 1
      · rw [ite_eq_left hc, ite_eq_left ⟨hc, by omega, by omega⟩]
      · rw [ite_eq_right hc, ite_eq_right (fun h => hc h.1)]
    · rw [ite_eq_right e₁]
      have hc : ((a % 2 = 1) ∧ oY + 8 + H.D ≤ x ∧ x < oY + 8 + H.D + (j + 1)) ↔
          ((a % 2 = 1) ∧ oY + 8 + H.D ≤ x ∧ x < oY + 8 + H.D + j) := by
        constructor
        · rintro ⟨h₁, h₂, h₃⟩; exact ⟨h₁, h₂, by omega⟩
        · rintro ⟨h₁, h₂, h₃⟩; exact ⟨h₁, h₂, by omega⟩
      simp only [hc]
  · rw [g₉, q₈.get .x12, q₇.get .x12, m₆.gpr, Q₅.get .x12]

/-- `DB`, then zeros. -/
def zf (W : Nat → Byte) (db m : Nat) : Byte := if m < db then W m else 0

/-- `Y` after `p` passes, from `V`: `DB`'s place holds `zf` from
`A mod 2^p` on. -/
def shW (V : Nat → Byte) (o db : Nat) (W : Nat → Byte) (r : Nat) (x : Nat) : Byte :=
  if o ≤ x ∧ x < o + db then zf W db (x - o + r) else V x

theorem shW_step {V W : Nat → Byte} {o db A p : Nat} (hz : ∀ m < db + 512, V (o + m) = zf W db m)
    (hp : p < 10) :
    ∀ x, shV (shW V o db W (A % 2 ^ p)) o db (2 ^ p) (A / 2 ^ p % 2 = 1) x =
      shW V o db W (A % 2 ^ (p + 1)) x := by
  intro x
  have hpw : 2 ^ p ≤ 512 := Nat.pow_le_pow_right (by decide) (show p ≤ 9 by omega)
  rw [Nat.mod_pow_succ]
  generalize 2 ^ p = P at hpw ⊢
  by_cases hx : o ≤ x ∧ x < o + db
  · obtain ⟨hx1, hx2⟩ := hx
    have e1 : shW V o db W (A % P + P * (A / P % 2)) x =
        zf W db (x - o + (A % P + P * (A / P % 2))) := by
      simp only [shW]; rw [ite_eq_left ⟨hx1, hx2⟩]
    rw [e1]
    by_cases hb : A / P % 2 = 1
    · simp only [shV]
      rw [ite_eq_left ⟨hb, hx1, hx2⟩, hb, Nat.mul_one]
      simp only [shW]
      by_cases hy : x + P < o + db
      · rw [ite_eq_left ⟨by omega, hy⟩, show x + P - o + A % P = x - o + (A % P + P) by omega]
      · rw [ite_eq_right (by omega), show x + P = o + (x + P - o) by omega, hz _ (by omega)]
        simp only [zf]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    · have hb0 : A / P % 2 = 0 := by omega
      simp only [shV]
      rw [ite_eq_right (fun h => hb h.1), hb0, Nat.mul_zero, Nat.add_zero]
      simp only [shW]; rw [ite_eq_left ⟨hx1, hx2⟩]
  · simp only [shV, shW]
    rw [ite_eq_right (fun h => hx h.2), ite_eq_right hx, ite_eq_right hx]

theorem shift_ok (H : Hash) (hD : H.D ≤ 64) {t : State} {F S : Addr} (L : Lay t F S) {V W : Nat → Byte}
    (R : Rep t.mem S V) {db pos : Nat} (hpos : pos < db) (hdb : db < 1024)
    (hfit : oY + 8 + H.D + db + 512 ≤ oRsa)
    (hz : ∀ m < db + 512, V (oY + 8 + H.D + m) = zf W db m) (h25 : t.gpr .x25 = BitVec.ofNat 64 db)
    (hP : t.mem.readW (off F sPos) 64 = BitVec.ofNat 64 pos) :
    WP isa (shift H) t fun t' => Keep [.x27, .x28, .x22, .x9, .x10, .x11, .x12, .x14, .x15] t t' ∧
      Frame [⟨S, oRsa⟩] t.mem t'.mem ∧ Rep t'.mem S (shW V (oY + 8 + H.D) db W (pos + 1)) ∧
      t'.gpr .x22 = BitVec.ofNat 64 (8 + H.D + (db - pos - 1)) := by
  have c6 : oRsa = 8192 := rfl
  have hrP : ∀ {u : State}, u.sp = F → u.rd = t.rd → u.wr = t.wr →
      InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 sPos) 8 := fun hsp hrd hwr => by
    rw [hsp, hrd, hwr]; exact L.fld (by decide)
  unfold shift
  refine WP.seq (WP.mono (Q := fun (u : State) => Only [.x27, .x28, .x22] t u ∧
      u.gpr .x27 = BitVec.ofNat 64 (pos + 1) ∧ u.gpr .x28 = 1#64 ∧ u.gpr .x22 = BitVec.ofNat 64 10) ?_
    fun u ⟨O, h27, h28, h22⟩ => ?_)
  · refine wp_ldrSp (by decide) (hrP L.sp rfl rfl) fun u₁ o₁ e₁ => wp_addImm (by decide) fun u₂ o₂ e₂ =>
      wp_movz fun u₃ o₃ e₃ => wp_movz fun u₄ o₄ e₄ => wp_nil ⟨(o₁.trans (o₂.trans (o₃.trans o₄))).mono, ?_, ?_, ?_⟩
    · rw [o₄.get .x27, o₃.get .x27, e₂, e₁, L.sp, hP, BitVec.ofNat_add_ofNat]
    · rw [o₄.get .x28, e₃]; rfl
    · rw [e₄]; rfl
  refine WP.seq (WP.mono (wp_countdown (cnt := .x22) (N := 10) (by decide) (by decide)
    (fun p v => Keep [.x27, .x28, .x22, .x9, .x10, .x11, .x12, .x14, .x15] u v ∧
      v.gpr .x27 = BitVec.ofNat 64 ((pos + 1) / 2 ^ p) ∧ v.gpr .x28 = BitVec.ofNat 64 (2 ^ p) ∧
      Frame [⟨S, oRsa⟩] u.mem v.mem ∧ Rep v.mem S (shW V (oY + 8 + H.D) db W ((pos + 1) % 2 ^ p)))
    (fun p hp v ⟨hK, h27', h28', hF, hR⟩ _ => ?_)
    ⟨Keep.refl _ _, by rw [h27, Nat.pow_zero, Nat.div_one], by rw [h28], Frame.refl _ _, ?_⟩ h22)
    fun v ⟨hK, _, _, hF, hR⟩ => ?_)
  · -- One pass.
    have hp9 : 2 ^ p ≤ 512 := Nat.pow_le_pow_right (by decide) (show p ≤ 9 by omega)
    have Lv : Lay v F S := L.congr (by rw [hK.sp, O.sp]) (by rw [hK.wr, O.wr]) (by rw [hK.get .x20, O.get .x20])
    have h25v : v.gpr .x25 = BitVec.ofNat 64 db := by rw [hK.get .x25, O.get .x25, h25]
    refine WP.seq (WP.mono (shiftPass_ok H Lv hR (db := db) (d := 2 ^ p) (a := (pos + 1) / 2 ^ p) (by omega) hD
      (by omega) (by have := Nat.div_le_self (pos + 1) (2 ^ p); omega) h28' h27' h25v) fun w ⟨kw, fw, rw'⟩ => ?_)
    refine wp_lsr (by decide) fun w₁ o₁ e₁ => wp_add fun w₂ o₂ e₂ => wp_subImm (by decide) fun w₃ o₃ e₃ =>
      wp_nil ⟨⟨(hK.trans (kw.trans (o₁.keep.trans (o₂.keep.trans o₃.keep)))).mono, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [o₃.get .x27, o₂.get .x27, e₁, kw.get .x27, h27', LenLoop.lsr_val (by have := Nat.div_le_self (pos + 1) (2 ^ p); omega),
        Nat.pow_one, Nat.div_div_eq_div_mul, Nat.pow_succ]
    · rw [o₃.get .x28, e₂, o₁.get .x28, kw.get .x28, h28', BitVec.ofNat_add_ofNat, Nat.pow_succ, Nat.mul_two]
    · rw [o₃.mem, o₂.mem, o₁.mem]; exact hF.trans fw
    · rw [o₃.mem, o₂.mem, o₁.mem]
      exact rw'.congr fun x _ => shW_step hz (by omega) x
    · rw [e₃, o₂.get .x22, o₁.get .x22, kw.get .x22]
  · -- No pass yet.
    refine (O.mem ▸ R).congr fun x _ => ?_
    simp only [shW, Nat.pow_zero, Nat.mod_one, Nat.add_zero]
    by_cases hx : oY + 8 + H.D ≤ x ∧ x < oY + 8 + H.D + db
    · rw [ite_eq_left hx, show x = oY + 8 + H.D + (x - (oY + 8 + H.D)) by omega, hz _ (by omega),
        Nat.add_sub_cancel_left]
    · rw [ite_eq_right hx]
  · -- `ℓ`.
    have hmod : (pos + 1) % 2 ^ 10 = pos + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hmod] at hR
    have hsp : v.sp = F := by rw [hK.sp, O.sp, L.sp]
    refine wp_ldrSp (by decide) (hrP hsp (by rw [hK.rd, O.rd]) (by rw [hK.wr, O.wr])) fun w₁ o₁ e₁ =>
      wp_sub fun w₂ o₂ e₂ => wp_subImm (by decide) fun w₃ o₃ e₃ => wp_addImm (by omega) fun w₄ o₄ e₄ =>
      wp_nil ⟨(O.keep.trans (hK.trans (o₁.keep.trans (o₂.keep.trans (o₃.keep.trans o₄.keep))))).mono,
        by rw [o₄.mem, o₃.mem, o₂.mem, o₁.mem, ← O.mem]; exact hF, by rw [o₄.mem, o₃.mem, o₂.mem, o₁.mem]; exact hR, ?_⟩
    have hPv : v.mem.readW (off F sPos) 64 = BitVec.ofNat 64 pos := by
      rw [← hP, slot_keep hF (L.slotSd (by decide)), O.mem]
    rw [e₄, e₃, e₂, o₁.get .x25, hK.get .x25, O.get .x25, h25, e₁, hsp, hPv, Offset.ofNat_sub_ofNat (by omega),
      Offset.ofNat_sub_ofNat (by omega), BitVec.ofNat_add_ofNat]
    congr 1; omega

end VG.Proof.RsaPss.AArch64
