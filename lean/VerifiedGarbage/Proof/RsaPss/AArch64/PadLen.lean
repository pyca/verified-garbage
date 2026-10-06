import VerifiedGarbage.Proof.RsaPss.AArch64.Pad
import VerifiedGarbage.Proof.Pbkdf2.AArch64.Iterate

/-!
# RSASSA-PSS on AArch64: `0x80` at a public offset, and the length field

`fixedPad80` ORs `0x80` into byte `ℓ` of `Y` (`fixedPad_ok`); `lenField`
writes the length field to `scratch + oLen` with `H`'s code
(`lenField_ok`), and `lenLoop` ORs it into the end of block
`⌊(ℓ + L) / B⌋` of `Y` through a mask for each block (`lenLoop_ok`).
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_subImm wp_eor wp_orr wp_and wp_lsl
  wp_lsr wp_ldrb wp_strb wp_sub)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_countdown wp_mov)
open VG.Proof.MdStream (Md)
open VG.Proof.RsaPkcs1Sig (frame_writeBytes)

/-! ## `0x80` at a public offset -/

theorem v80_fixed (V : Nat → Byte) {ℓ n : Nat} (h : ℓ < n) :
    upd V (oY + ℓ) (V (oY + ℓ) ||| 0x80) = v80 V ℓ n := by
  funext o
  simp only [upd, v80]
  by_cases e : o = oY + ℓ
  · subst e
    simp only [ite_true, show oY ≤ oY + ℓ ∧ oY + ℓ < oY + n from ⟨by omega, by omega⟩, Nat.add_sub_cancel_left,
      and_self]
  · simp only [e, ite_false]
    split
    · rw [ite_eq_right (by omega)]; simp
    · rfl

theorem or80 (b : Byte) : (BitVec.setWidth 64 b ||| (BitVec.ofNat 16 0x80).setWidth 64).setWidth 8 = b ||| 0x80 := by
  revert b; decide

theorem fixedPad_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    {ℓ n : Nat} (hℓ : ℓ < n) (h4 : oY + ℓ < 4096) :
    WP isa (fixedPad80 ℓ) t fun t' => Keep [.x10, .x9, .x13] t t' ∧
      Frame [⟨S, oRsa⟩] t.mem t'.mem ∧ Rep t'.mem S (v80 V ℓ n) := by
  unfold fixedPad80
  refine wp_addImm h4 fun u₁ o₁ e₁ => ?_
  have hY : oY + ℓ + 1 ≤ oRsa := by unfold oY oRsa at *; omega
  refine wp_ldrb (by decide) (by rw [e₁, L.x20, BitVec.add_zero]) (by rw [o₁.rd, o₁.wr]; exact L.ld hY)
    fun u₂ o₂ e₂ => wp_movz fun u₃ o₃ e₃ => wp_orr fun u₄ o₄ e₄ => ?_
  have O₄ : Only [.x10, .x9, .x13] t u₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine wp_strb (by decide) (by rw [o₄.get .x10, o₃.get .x10, o₂.get .x10, e₁,
      L.x20, BitVec.add_zero]) (by rw [O₄.wr]; exact L.st hY) fun u₅ m₅ => wp_nil ?_
  have hb : (u₄.gpr .x9).setWidth 8 = V (oY + ℓ) ||| 0x80 := by
    rw [e₄, o₃.get .x9, e₂, e₃, o₁.mem, R (oY + ℓ) (by omega)]
    exact or80 _
  refine ⟨(O₄.keep.trans m₅.keep).mono, ?_, ?_⟩
  · rw [m₅.mem, O₄.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (d := oY + ℓ) (n := 1) (by omega) (by unfold oRsa at *; omega))
  · rw [m₅.mem, O₄.mem, hb, ← v80_fixed V hℓ]
    exact R.wb (o := oY + ℓ) (by omega) _

/-! ## The length field -/

theorem lenField_ok (H : Hash) {md : Md H.P.B H.P.N H.P.L} (hs : Proof.Pbkdf2.AArch64.Shape (P := H.P) md)
    {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    (hNBL : H.P.N + H.P.B - H.P.L ≤ 192) (hL : H.P.L ≤ 16) :
    WP isa (.block (lenField H)) t fun t' => Keep [.x19, .x9, .x12] t t' ∧ t'.gpr .x19 = off S oSt ∧
      Frame [⟨S, oRsa⟩] t.mem t'.mem ∧ Rep t'.mem S (updL V oLen (md.lenOf (t.gpr .x22))) := by
  unfold lenField
  refine wp_addImm (by unfold oLen; omega) fun u₁ o₁ e₁ => ?_
  have ha : u₁.gpr .x19 + BitVec.ofNat 64 (H.P.N + H.P.B - H.P.L) = off S oLen := by
    rw [e₁, L.x20, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2; unfold oLen; omega
  have hin : InRegions u₁.wr (u₁.gpr .x19 + BitVec.ofNat 64 (H.P.N + H.P.B - H.P.L)) H.P.L := by
    rw [ha, o₁.wr]; exact L.st (by unfold oLen oRsa; omega)
  show WP isa (.block (H.P.len ++ [.addImm .x .x19 .x20 oSt])) u₁ _
  rw [WP.block_append_iff]
  refine WP.mono (WP.preservedV (hs.len u₁ hin) (by rw [Code.allInstrs_eq]; exact hs.lenKeepsV)) fun u₂ ⟨⟨hg, hrd, hwr, hsp, hm⟩, hv⟩ => ?_
  refine wp_addImm (by decide) fun u₃ o₃ e₃ => wp_nil ⟨⟨fun r hr => ?_, ?_, ?_, ?_, fun r hr => ?_⟩, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [o₃.gpr r (by simpa using hr.1), hg r hr.2.1 hr.2.2, o₁.gpr r (by simpa using hr.1)]
  · rw [o₃.rd, hrd, o₁.rd]
  · rw [o₃.wr, hwr, o₁.wr]
  · rw [o₃.sp, hsp, o₁.sp]
  · rw [o₃.vcs r hr, hv r hr, o₁.vcs r hr]
  · rw [e₃, hg .x20 (by decide) (by decide), o₁.get .x20, L.x20]
  · rw [o₃.mem, hm, ha, o₁.mem]
    exact (frame_writeBytes _ _ _).sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_singleton_self _, by
        rw [md.lenOf_length]; exact Offset.sub_base _ (by unfold oLen oRsa; omega)⟩
  · rw [o₃.mem, hm, ha, o₁.mem, o₁.get .x22]
    exact R.writeBytes (by rw [md.lenOf_length]; unfold oLen oRsa; omega)


/-! ## The length field into the last block -/

namespace LenLoop

/-- `Y` with the length field (`L` bytes at `oLen`) ORed into the end of
block `fb`. -/
def vLen (B L : Nat) (V : Nat → Byte) (fb : Nat) (o : Nat) : Byte :=
  if oY + B * fb + (B - L) ≤ o ∧ o < oY + B * fb + B then V o ||| V (oLen + (o - (oY + B * fb + (B - L))))
  else V o

/-- After the blocks before `b`. -/
def vB (B L : Nat) (V : Nat → Byte) (fb b : Nat) (o : Nat) : Byte := if fb < b then vLen B L V fb o else V o

/-- And the first `j` bytes of block `b`'s end. -/
def vIn (B L : Nat) (V : Nat → Byte) (fb b j : Nat) (o : Nat) : Byte :=
  if b = fb ∧ oY + B * b + (B - L) ≤ o ∧ o < oY + B * b + (B - L) + j then
    V o ||| V (oLen + (o - (oY + B * b + (B - L))))
  else vB B L V fb b o

theorem vIn_zero (B L : Nat) (V : Nat → Byte) (fb b : Nat) : vIn B L V fb b 0 = vB B L V fb b := by
  funext o; simp only [vIn]; split <;> first | omega | rfl

theorem vIn_end {B L : Nat} (hL : L ≤ B) (V : Nat → Byte) (fb b : Nat) :
    vIn B L V fb b L = vB B L V fb (b + 1) := by
  funext o
  simp only [vIn, vB]
  by_cases h : b = fb
  · subst h
    simp only [true_and, Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true, vLen,
      show oY + B * b + (B - L) + L = oY + B * b + B by omega]
  · have e : (fb < b + 1 ↔ fb < b) := by omega
    simp only [h, false_and, ite_false, e]

/-- Block `b` starts after block `fb` ends if `fb < b`. -/
theorem blk_le {B fb b : Nat} (h : fb < b) : B * fb + B ≤ B * b := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h

/-- The byte the inner loop writes. -/
theorem vIn_succ {B L : Nat} (V : Nat → Byte) {fb b j : Nat} :
    upd (vIn B L V fb b j) (oY + B * b + (B - L) + j)
      (if b = fb then V (oY + B * b + (B - L) + j) ||| V (oLen + j) else V (oY + B * b + (B - L) + j)) =
      vIn B L V fb b (j + 1) := by
  funext o
  simp only [upd, vIn, vB, vLen]
  by_cases e : o = oY + B * b + (B - L) + j
  · subst e
    rw [ite_eq_left rfl]
    by_cases h : b = fb
    · subst h
      rw [ite_eq_left rfl, ite_eq_left ⟨rfl, by omega, by omega⟩, show oY + B * b + (B - L) + j -
        (oY + B * b + (B - L)) = j by omega]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.1)]
      by_cases hb : fb < b
      · have := blk_le (B := B) hb
        rw [ite_eq_left hb, ite_eq_right (by omega)]
      · rw [ite_eq_right hb]
  · rw [ite_eq_right e]
    have c : (b = fb ∧ oY + B * b + (B - L) ≤ o ∧ o < oY + B * b + (B - L) + (j + 1)) ↔
        (b = fb ∧ oY + B * b + (B - L) ≤ o ∧ o < oY + B * b + (B - L) + j) := by omega
    simp only [c]

theorem byte_mask (y l : Byte) (c : Prop) [Decidable c] :
    (BitVec.setWidth 64 y ||| (BitVec.setWidth 64 l &&& (if c then BitVec.allOnes 64 else 0))).setWidth 8 =
      if c then y ||| l else y := by
  by_cases h : c
  · simp only [h, ite_true, BitVec.and_allOnes]
    ext i hi; simp
  · simp [h]

theorem mask_val {a b : BitVec 64} (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63) :
    (BitVec.setWidth 64 (BitVec.ofNat 16 0) - ((a ^^^ b) - BitVec.ofNat 64 1) >>> 63) =
      if a = b then BitVec.allOnes 64 else 0 := by
  rw [eq1_val ha hb]
  split <;> decide

theorem lsr_val {x : Nat} (hx : x < 2 ^ 64) {k : Nat} :
    BitVec.ofNat 64 x >>> k = BitVec.ofNat 64 (x / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

theorem vB_lt {B L : Nat} {V : Nat → Byte} {fb b o : Nat}
    (ho : oY + B * b ≤ o ∧ o < oY + B * b + B) : vB B L V fb b o = V o := by
  simp only [vB, vLen]
  by_cases h : fb < b
  · have := blk_le (B := B) h
    rw [ite_eq_left h, ite_eq_right (by omega)]
  · rw [ite_eq_right h]

end LenLoop

open LenLoop in
theorem lenLoop_ok (H : Hash) {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    {ℓ nbm : Nat} (hB : 2 ^ lgB H = H.P.B) (hlg : lgB H < 64) (hLB : H.P.L ≤ H.P.B) (hL0 : 0 < H.P.L)
    (hL16 : H.P.L ≤ 16) (hBl : H.P.B ≤ 128) (hℓ : ℓ < 2 ^ 62) (hnb : nbm * H.P.B ≤ 2048)
    (hfb : (ℓ + H.P.L) / H.P.B < nbm)
    (h22 : t.gpr .x22 = BitVec.ofNat 64 ℓ) (hNb : t.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm) :
    WP isa (lenLoop H) t fun t' => Keep [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] t t' ∧
      Frame [⟨S, oRsa⟩] t.mem t'.mem ∧ Rep t'.mem S (vLen H.P.B H.P.L V ((ℓ + H.P.L) / H.P.B)) := by
  generalize hfbd : (ℓ + H.P.L) / H.P.B = fb at hfb ⊢
  have hnb0 : 0 < nbm := by omega
  have hnb1 : nbm ≤ 2048 := Nat.le_trans (Nat.le_mul_of_pos_right _ (by omega)) hnb
  have hBnb : H.P.B * nbm ≤ 2048 := by rw [Nat.mul_comm]; exact hnb
  unfold lenLoop lastBlk
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_addImm (by unfold oY; omega) fun u₁ o₁ e₁ => wp_movz fun u₂ o₂ e₂ => ?_)
  refine wp_ldrSp (by decide) (by
    rw [o₂.sp, o₁.sp, L.sp, o₂.rd, o₁.rd, o₂.wr, o₁.wr]; exact L.fld (d := sNb) (n := 8) (by decide))
    fun u₃ o₃ e₃ => wp_addImm (by omega) fun u₄ o₄ e₄ => wp_lsr hlg fun u₅ o₅ e₅ => wp_nil ?_
  rw [o₂.sp, o₁.sp, L.sp, o₂.mem, o₁.mem, hNb] at e₃
  have O₅ : Only [.x10, .x11, .x12, .x15] t u₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  have x15 : u₅.gpr .x15 = BitVec.ofNat 64 fb := by
    rw [e₅, e₄, o₃.get .x22, o₂.get .x22, o₁.get .x22, h22, BitVec.ofNat_add_ofNat,
      lsr_val (by omega), hB, hfbd]
  refine WP.mono (wp_countdown (cnt := .x12) (N := nbm) (by omega) hnb0
    (fun b u => Keep [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] t u ∧
      u.gpr .x10 = off S (oY + H.P.B * b + (H.P.B - H.P.L)) ∧ u.gpr .x11 = BitVec.ofNat 64 b ∧
      u.gpr .x15 = BitVec.ofNat 64 fb ∧ Frame [⟨S, oRsa⟩] t.mem u.mem ∧
      Rep u.mem S (vB H.P.B H.P.L V fb b))
    (fun b hb u ⟨hK, h10, h11, h15, hF, hR⟩ _ => ?_)
    ⟨O₅.keep.mono, by rw [o₅.get .x10, o₄.get .x10, o₃.get .x10, o₂.get .x10, e₁, L.x20]; congr 2; omega,
      by rw [o₅.get .x11, o₄.get .x11, o₃.get .x11, e₂]; rfl, x15, by rw [O₅.mem]; exact Frame.refl _ _,
      by rw [O₅.mem]; exact R.congr fun o _ => by simp [vB]⟩
    (by rw [o₅.get .x12, o₄.get .x12, e₃])) fun u h => ⟨h.1, h.2.2.2.2.1,
      h.2.2.2.2.2.congr fun o _ => by simp only [vB, hfb, ite_true]⟩
  -- one block
  have hbB := blk_le (B := H.P.B) hb
  unfold eqMask eq1
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_eor fun v₁ p₁ f₁ => wp_subImm (by decide) fun v₂ p₂ f₂ => wp_lsr (by decide) fun v₃ p₃ f₃ =>
    wp_movz fun v₄ p₄ f₄ => wp_sub fun v₅ p₅ f₅ => wp_addImm (by decide) fun v₆ p₆ f₆ =>
    wp_mov fun v₇ p₇ f₇ => wp_movz fun v₈ p₈ f₈ => wp_nil ?_)
  have P₈ : Only [.x13, .x9, .x14, .x16, .x17] u v₈ :=
    (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans (p₇.trans p₈))))))).mono
  have x13 : v₈.gpr .x13 = if b = fb then BitVec.allOnes 64 else 0 := by
    rw [p₈.get .x13, p₇.get .x13, p₆.get .x13, f₅, f₄, p₄.get .x13, f₃, f₂, f₁, h11, h15,
      mask_val (by simp; omega) (by simp; omega)]
    by_cases e : b = fb
    · rw [ite_eq_left (by rw [e]), ite_eq_left e]
    · rw [ite_eq_right fun h' => e ((ofNat_eq_iff (by omega) (by omega)).mp h'), ite_eq_right e]
  have hB' : H.P.B * (b + 1) ≤ H.P.B * nbm := Nat.mul_le_mul_left _ hb
  refine WP.seq (WP.mono (wp_countdown (cnt := .x17) (N := H.P.L) (by omega) hL0
    (fun j v => Keep [.x8, .x9, .x14, .x16, .x17] v₈ v ∧ v.gpr .x14 = off S (oLen + j) ∧
      v.gpr .x16 = off S (oY + H.P.B * b + (H.P.B - H.P.L) + j) ∧ Frame [⟨S, oRsa⟩] t.mem v.mem ∧
      Rep v.mem S (vIn H.P.B H.P.L V fb b j))
    (fun j hj v ⟨hK', h14, h16, hF', hR'⟩ _ => ?_)
    ⟨Keep.refl _ _, by rw [Nat.add_zero, p₈.get .x14, p₇.get .x14, f₆, p₅.get .x20, p₄.get .x20, p₃.get .x20,
      p₂.get .x20, p₁.get .x20, hK.get .x20, L.x20], by
      rw [Nat.add_zero, p₈.get .x16, f₇, p₆.get .x10, p₅.get .x10, p₄.get .x10, p₃.get .x10, p₂.get .x10,
        p₁.get .x10, h10], by
      rw [P₈.mem]; exact hF, by rw [P₈.mem, vIn_zero]; exact hR⟩
    (by rw [f₈]; apply BitVec.eq_of_toNat_eq; simp; omega)) fun v ⟨hK', _, _, hF', hR'⟩ => ?_)
  · -- one byte
    have hS1 : oLen + j + 1 ≤ oRsa := by unfold oLen oRsa; omega
    have hS2 : oY + H.P.B * b + (H.P.B - H.P.L) + j + 1 ≤ oRsa := by
      rw [Nat.mul_succ] at hB'; unfold oY oRsa; omega
    have rd : v.rd = t.rd := by rw [hK'.rd, P₈.rd, hK.rd]
    have wr : v.wr = t.wr := by rw [hK'.wr, P₈.wr, hK.wr]
    refine wp_ldrb (by decide) (by rw [h14, BitVec.add_zero]) (by rw [rd, wr]; exact L.ld hS1)
      fun w₁ q₁ g₁ => wp_and fun w₂ q₂ g₂ => ?_
    refine wp_ldrb (by decide) (by rw [q₂.get .x16, q₁.get .x16, h16, BitVec.add_zero])
      (by rw [q₂.rd, q₁.rd, q₂.wr, q₁.wr, rd, wr]; exact L.ld hS2) fun w₃ q₃ g₃ => wp_orr fun w₄ q₄ g₄ => ?_
    have Q₄ : Only [.x9, .x8] v w₄ := (q₁.trans (q₂.trans (q₃.trans q₄))).mono
    refine wp_strb (by decide) (by rw [Q₄.get .x16, h16, BitVec.add_zero]) (by rw [Q₄.wr, wr]; exact L.st hS2)
      fun w₅ m₅ => wp_addImm (by decide) fun w₆ q₆ g₆ => wp_addImm (by decide) fun w₇ q₇ g₇ =>
      wp_subImm (by decide) fun w₈ q₈ g₈ => wp_nil ?_
    have hl : v.mem (off S (oLen + j)) = V (oLen + j) := by
      rw [hR' _ (by omega)]; simp only [vIn, vB, vLen]
      rw [ite_eq_right (by unfold oLen oY; omega)]
      split <;> first | rfl | (rw [ite_eq_right (by unfold oLen oY; omega)])
    have hy : v.mem (off S (oY + H.P.B * b + (H.P.B - H.P.L) + j)) = V (oY + H.P.B * b + (H.P.B - H.P.L) + j) := by
      rw [hR' _ (by omega)]; simp only [vIn]
      rw [ite_eq_right (by omega)]
      exact vB_lt ⟨by omega, by omega⟩
    have hb' : (w₄.gpr .x8).setWidth 8 = if b = fb then V (oY + H.P.B * b + (H.P.B - H.P.L) + j) ||| V (oLen + j)
        else V (oY + H.P.B * b + (H.P.B - H.P.L) + j) := by
      rw [g₄, q₃.get .x9, g₃, q₂.mem, q₁.mem, hy, g₂, g₁, hl, q₁.get .x13, hK'.get .x13, x13]
      exact byte_mask _ _ _
    have hm : w₈.mem = v.mem.writeW (off S (oY + H.P.B * b + (H.P.B - H.P.L) + j)) ((w₄.gpr .x8).setWidth 8) := by
      rw [q₈.mem, q₇.mem, q₆.mem, m₅.mem, Q₄.mem]
    refine ⟨⟨(hK'.trans (Q₄.keep.trans (m₅.keep.trans (q₆.keep.trans (q₇.keep.trans q₈.keep))))).mono, ?_, ?_,
      ?_, ?_⟩, ?_⟩
    · rw [q₈.get .x14, q₇.get .x14, g₆, m₅.gpr, Q₄.get .x14, h14, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        Nat.add_assoc]
    · rw [q₈.get .x16, g₇, q₆.get .x16, m₅.gpr, Q₄.get .x16, h16, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        Nat.add_assoc]
    · rw [hm]
      exact hF'.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by unfold oRsa at *; omega))
    · rw [hm, hb', ← vIn_succ]
      exact hR'.wb (by omega) _
    · rw [g₈, q₇.get .x17, q₆.get .x17, m₅.gpr, Q₄.get .x17]
  · refine wp_addImm (by omega) fun w₁ q₁ g₁ => wp_addImm (by decide) fun w₂ q₂ g₂ =>
      wp_subImm (by decide) fun w₃ q₃ g₃ => wp_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact (hK.trans (P₈.keep.trans (hK'.trans (q₁.keep.trans (q₂.keep.trans q₃.keep))))).mono
    · rw [q₃.get .x10, q₂.get .x10, g₁, hK'.get .x10, P₈.get .x10, h10, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      congr 2; rw [Nat.mul_succ]; omega
    · rw [q₃.get .x11, g₂, q₁.get .x11, hK'.get .x11, P₈.get .x11, h11, BitVec.ofNat_add_ofNat]
    · rw [q₃.get .x15, q₂.get .x15, q₁.get .x15, hK'.get .x15, P₈.get .x15, h15]
    · rw [q₃.mem, q₂.mem, q₁.mem]; exact hF'
    · rw [q₃.mem, q₂.mem, q₁.mem, ← vIn_end hLB]; exact hR'
    · rw [g₃, q₂.get .x12, q₁.get .x12, hK'.get .x12, P₈.get .x12]

end VG.Proof.RsaPss.AArch64
