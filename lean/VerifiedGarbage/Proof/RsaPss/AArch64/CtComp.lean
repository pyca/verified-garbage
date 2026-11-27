module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
public import VerifiedGarbage.Proof.RsaPss.AArch64.Basic
public import VerifiedGarbage.Proof.RsaPss.AArch64.TabCall
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode
public import VerifiedGarbage.Proof.Pbkdf2.AArch64.Iterate
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Block

/-! ### `RsaPss.AArch64.Select`, which this module and modules that import it used -/

section

/-! ### `RsaPss.AArch64.PadLen`, which this module and modules that import it used -/

section

/-! ### `RsaPss.AArch64.Pad`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS on AArch64: the padding of a message of secret length

`pad80` ORs `0x80` into byte `ℓ` of `Y` through a mask for each of its
`nbm B` bytes (`pad80_ok`), and `fixedPad80` into byte `ℓ` alone
(`fixedPad_ok`); both leave the view `v80`.
-/

@[expose] public section

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
  funext o; simp only [v80]; split <;> first | omega_arith | rfl

theorem v80_succ (V : Nat → Byte) (ℓ i : Nat) (b : Byte) (hb : b = V (oY + i) ||| (if i = ℓ then 0x80 else 0)) :
    upd (v80 V ℓ i) (oY + i) b = v80 V ℓ (i + 1) := by
  funext o
  simp only [upd, v80]
  by_cases h : o = oY + i
  · subst h
    have h1 : oY ≤ oY + i ∧ oY + i < oY + (i + 1) := ⟨by omega_arith, by omega_arith⟩
    simp only [ite_true, hb, h1, Nat.add_sub_cancel_left, and_self]
  · simp only [h, ite_false]
    by_cases h' : oY ≤ o ∧ o < oY + i
    · have h2 : oY ≤ o ∧ o < oY + (i + 1) := ⟨h'.1, by omega_arith⟩
      simp only [h', h2]
    · have h2 : ¬ (oY ≤ o ∧ o < oY + (i + 1)) := by omega_arith
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
  have hn : nbm * H.P.B < 2 ^ 64 := by omega_arith
  have hnb' : nbm ≤ nbm * H.P.B := Nat.le_mul_of_pos_right _ (Nat.pos_of_mul_pos_left hnb0)
  have c12 : u₄.gpr .x12 = BitVec.ofNat 64 (nbm * H.P.B) := by
    rw [e₄, e₃, BitVec.shiftLeft_eq_mul_twoPow]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_twoPow, hB]
    have hB' : H.P.B ≤ nbm * H.P.B := Nat.le_mul_of_pos_left _ (Nat.pos_of_mul_pos_right hnb0)
    rw [Nat.mod_eq_of_lt (show nbm < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show H.P.B < 2 ^ 64 by omega_arith)]
  refine WP.mono (wp_countdown (cnt := .x12) hn hnb0 (fun i u => Keep [.x10, .x11, .x12, .x13, .x14] t u ∧
      u.gpr .x10 = off S (oY + i) ∧ u.gpr .x11 = BitVec.ofNat 64 i ∧
      Frame [⟨S, oRsa⟩] t.mem u.mem ∧ Rep u.mem S (v80 V ℓ i))
    (fun i hi u ⟨hK, h10, h11, hF, hR⟩ _ => ?_)
    ⟨O₄.keep.mono, by rw [Nat.add_zero, o₄.get .x10, o₃.get .x10, o₂.get .x10, e₁, L.x20],
      by rw [o₄.get .x11, o₃.get .x11, e₂]; rfl, by rw [O₄.mem]; exact Frame.refl _ _,
      by rw [v80_zero, O₄.mem]; exact R⟩ c12) fun u h => ⟨h.1, h.2.2.2⟩
  have hiY : oY + i + 1 ≤ oRsa := by unfold oY oRsa; omega_arith
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
        eq1_val (by simp; omega_arith) (by simp; omega_arith)]
      by_cases e : i = ℓ
      · rw [ite_eq_left ((ofNat_eq_iff (by omega_arith) (by omega_arith)).mpr e), ite_eq_left e]
      · rw [ite_eq_right fun h' => e ((ofNat_eq_iff (by omega_arith) (by omega_arith)).mp h'), ite_eq_right e]
    rw [f₆, f₅, p₅.get .x13, p₄.get .x13, p₃.get .x13, p₂.get .x13, f₁, e14, hR _ (by omega_arith)]
    have : v80 V ℓ i (oY + i) = V (oY + i) := by simp only [v80]; split <;> first | omega_arith | rfl
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
  · rw [hm]; exact hF.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by unfold oY oRsa at *; omega_arith)
      (by unfold oY oRsa at *; omega_arith))
  · rw [hm, ← v80_succ V ℓ i _ hb]; exact hR.wb (by omega_arith) _
  · rw [f₁₀, p₉.get .x12, p₈.get .x12, m₇.gpr, P₆.get .x12]

end VG.Proof.RsaPss.AArch64

end

end

/-!
# RSASSA-PSS on AArch64: `0x80` at a public offset, and the length field

`fixedPad80` ORs `0x80` into byte `ℓ` of `Y` (`fixedPad_ok`); `lenField`
writes the length field to `scratch + oLen` with `H`'s code
(`lenField_ok`), and `lenLoop` ORs it into the end of block
`⌊(ℓ + L) / B⌋` of `Y` through a mask for each block (`lenLoop_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_subImm wp_eor wp_orr wp_and wp_lsl
  wp_lsr wp_ldrb wp_strb wp_sub)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_countdown wp_mov)
open VG.Proof.MdStream (Md)
open VG.Proof.RsaPkcs1Sig (frame_writeBytes)


/-! ## The length field -/

theorem lenField_ok (H : Hash) {md : Md H.P.B H.P.N H.P.L} (hs : Proof.Pbkdf2.AArch64.Shape (P := H.P) md)
    {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    (hNBL : H.P.N + H.P.B - H.P.L ≤ 192) (hL : H.P.L ≤ 16) :
    WP isa (.block (lenField H)) t fun t' => Keep [.x19, .x9, .x12] t t' ∧ t'.gpr .x19 = off S oSt ∧
      Frame [⟨S, oRsa⟩] t.mem t'.mem ∧ Rep t'.mem S (updL V oLen (md.lenOf (t.gpr .x22))) := by
  unfold lenField
  refine wp_addImm (by unfold oLen; omega_using []) fun u₁ o₁ e₁ => ?_
  have ha : u₁.gpr .x19 + BitVec.ofNat 64 (H.P.N + H.P.B - H.P.L) = off S oLen := by
    rw [e₁, L.x20, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2; unfold oLen; omega_using [hNBL]
  have hin : InRegions u₁.wr (u₁.gpr .x19 + BitVec.ofNat 64 (H.P.N + H.P.B - H.P.L)) H.P.L := by
    rw [ha, o₁.wr]; exact L.st (by unfold oLen oRsa; omega_using [hL])
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
        rw [md.lenOf_length]; exact Offset.sub_base _ (by unfold oLen oRsa; omega_using [hL])⟩
  · rw [o₃.mem, hm, ha, o₁.mem, o₁.get .x22]
    exact R.writeBytes (by rw [md.lenOf_length]; unfold oLen oRsa; omega_using [hL])


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
      show oY + B * b + (B - L) + L = oY + B * b + B by omega_using [hL]]
  · have e : (fb < b + 1 ↔ fb < b) := by omega_using [h]
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
      rw [ite_eq_left rfl, ite_eq_left ⟨rfl, by omega_using [], by omega_using []⟩, show oY + B * b + (B - L) + j -
        (oY + B * b + (B - L)) = j by omega_using []]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.1)]
      by_cases hb : fb < b
      · have := blk_le (B := B) hb
        rw [ite_eq_left hb, ite_eq_right (by omega_using [this])]
      · rw [ite_eq_right hb]
  · rw [ite_eq_right e]
    have c : (b = fb ∧ oY + B * b + (B - L) ≤ o ∧ o < oY + B * b + (B - L) + (j + 1)) ↔
        (b = fb ∧ oY + B * b + (B - L) ≤ o ∧ o < oY + B * b + (B - L) + j) := by omega_using [e]
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
    rw [ite_eq_left h, ite_eq_right (by omega_using [ho, this])]
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
  have hnb0 : 0 < nbm := by omega_arith
  have hnb1 : nbm ≤ 2048 := Nat.le_trans (Nat.le_mul_of_pos_right _ (by omega_arith)) hnb
  have hBnb : H.P.B * nbm ≤ 2048 := by rw [Nat.mul_comm]; exact hnb
  unfold lenLoop lastBlk
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_addImm (by unfold oY; omega_arith) fun u₁ o₁ e₁ => wp_movz fun u₂ o₂ e₂ => ?_)
  refine wp_ldrSp (by decide) (by
    rw [o₂.sp, o₁.sp, L.sp, o₂.rd, o₁.rd, o₂.wr, o₁.wr]; exact L.fld (d := sNb) (n := 8) (by decide))
    fun u₃ o₃ e₃ => wp_addImm (by omega_arith) fun u₄ o₄ e₄ => wp_lsr hlg fun u₅ o₅ e₅ => wp_nil ?_
  rw [o₂.sp, o₁.sp, L.sp, o₂.mem, o₁.mem, hNb] at e₃
  have O₅ : Only [.x10, .x11, .x12, .x15] t u₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  have x15 : u₅.gpr .x15 = BitVec.ofNat 64 fb := by
    rw [e₅, e₄, o₃.get .x22, o₂.get .x22, o₁.get .x22, h22, BitVec.ofNat_add_ofNat,
      lsr_val (by omega_arith), hB, hfbd]
  refine WP.mono (wp_countdown (cnt := .x12) (N := nbm) (by omega_arith) hnb0
    (fun b u => Keep [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] t u ∧
      u.gpr .x10 = off S (oY + H.P.B * b + (H.P.B - H.P.L)) ∧ u.gpr .x11 = BitVec.ofNat 64 b ∧
      u.gpr .x15 = BitVec.ofNat 64 fb ∧ Frame [⟨S, oRsa⟩] t.mem u.mem ∧
      Rep u.mem S (vB H.P.B H.P.L V fb b))
    (fun b hb u ⟨hK, h10, h11, h15, hF, hR⟩ _ => ?_)
    ⟨O₅.keep.mono, by rw [o₅.get .x10, o₄.get .x10, o₃.get .x10, o₂.get .x10, e₁, L.x20]; congr 2; omega_arith,
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
      mask_val (by simp; omega_arith) (by simp; omega_arith)]
    by_cases e : b = fb
    · rw [ite_eq_left (by rw [e]), ite_eq_left e]
    · rw [ite_eq_right fun h' => e ((ofNat_eq_iff (by omega_arith) (by omega_arith)).mp h'), ite_eq_right e]
  have hB' : H.P.B * (b + 1) ≤ H.P.B * nbm := Nat.mul_le_mul_left _ hb
  refine WP.seq (WP.mono (wp_countdown (cnt := .x17) (N := H.P.L) (by omega_arith) hL0
    (fun j v => Keep [.x8, .x9, .x14, .x16, .x17] v₈ v ∧ v.gpr .x14 = off S (oLen + j) ∧
      v.gpr .x16 = off S (oY + H.P.B * b + (H.P.B - H.P.L) + j) ∧ Frame [⟨S, oRsa⟩] t.mem v.mem ∧
      Rep v.mem S (vIn H.P.B H.P.L V fb b j))
    (fun j hj v ⟨hK', h14, h16, hF', hR'⟩ _ => ?_)
    ⟨Keep.refl _ _, by rw [Nat.add_zero, p₈.get .x14, p₇.get .x14, f₆, p₅.get .x20, p₄.get .x20, p₃.get .x20,
      p₂.get .x20, p₁.get .x20, hK.get .x20, L.x20], by
      rw [Nat.add_zero, p₈.get .x16, f₇, p₆.get .x10, p₅.get .x10, p₄.get .x10, p₃.get .x10, p₂.get .x10,
        p₁.get .x10, h10], by
      rw [P₈.mem]; exact hF, by rw [P₈.mem, vIn_zero]; exact hR⟩
    (by rw [f₈]; apply BitVec.eq_of_toNat_eq; simp; omega_arith)) fun v ⟨hK', _, _, hF', hR'⟩ => ?_)
  · -- one byte
    have hS1 : oLen + j + 1 ≤ oRsa := by unfold oLen oRsa; omega_arith
    have hS2 : oY + H.P.B * b + (H.P.B - H.P.L) + j + 1 ≤ oRsa := by
      rw [Nat.mul_succ] at hB'; unfold oY oRsa; omega_arith
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
      rw [hR' _ (by omega_arith)]; simp only [vIn, vB, vLen]
      rw [ite_eq_right (by unfold oLen oY; omega_arith)]
      split <;> first | rfl | (rw [ite_eq_right (by unfold oLen oY; omega_arith)])
    have hy : v.mem (off S (oY + H.P.B * b + (H.P.B - H.P.L) + j)) = V (oY + H.P.B * b + (H.P.B - H.P.L) + j) := by
      rw [hR' _ (by omega_arith)]; simp only [vIn]
      rw [ite_eq_right (by omega_arith)]
      exact vB_lt ⟨by omega_arith, by omega_arith⟩
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
      exact hF'.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by unfold oRsa at *; omega_arith))
    · rw [hm, hb', ← vIn_succ]
      exact hR'.wb (by omega_arith) _
    · rw [g₈, q₇.get .x17, q₆.get .x17, m₅.gpr, Q₄.get .x17]
  · refine wp_addImm (by omega_arith) fun w₁ q₁ g₁ => wp_addImm (by decide) fun w₂ q₂ g₂ =>
      wp_subImm (by decide) fun w₃ q₃ g₃ => wp_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact (hK.trans (P₈.keep.trans (hK'.trans (q₁.keep.trans (q₂.keep.trans q₃.keep))))).mono
    · rw [q₃.get .x10, q₂.get .x10, g₁, hK'.get .x10, P₈.get .x10, h10, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      congr 2; rw [Nat.mul_succ]; omega_arith
    · rw [q₃.get .x11, g₂, q₁.get .x11, hK'.get .x11, P₈.get .x11, h11, BitVec.ofNat_add_ofNat]
    · rw [q₃.get .x15, q₂.get .x15, q₁.get .x15, hK'.get .x15, P₈.get .x15, h15]
    · rw [q₃.mem, q₂.mem, q₁.mem]; exact hF'
    · rw [q₃.mem, q₂.mem, q₁.mem, ← vIn_end hLB]; exact hR'
    · rw [g₃, q₂.get .x12, q₁.get .x12, hK'.get .x12, P₈.get .x12]

end VG.Proof.RsaPss.AArch64

end

end

/-!
# RSASSA-PSS on AArch64: selecting the hash value of the last block

`select` copies the `N`-byte hash value at `scratch + oSt` to
`scratch + oSel` under the mask of `b = ⌊(ℓ + L) / B⌋`, a byte at a time
(`select_ok`).
-/

@[expose] public section

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
    · rw [ite_eq_left h, ite_eq_left ⟨h, by omega_using [], by omega_using []⟩, Nat.add_sub_cancel_left]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.1)]
  · rw [ite_eq_right e]
    have hc : (c ∧ oSel ≤ o ∧ o < oSel + (j + 1)) ↔ (c ∧ oSel ≤ o ∧ o < oSel + j) := by
      constructor
      · rintro ⟨h₁, h₂, h₃⟩; exact ⟨h₁, h₂, by omega_using [e, h₃]⟩
      · rintro ⟨h₁, h₂, h₃⟩; exact ⟨h₁, h₂, by omega_using [h₃]⟩
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
  refine WP.seq (wp_addImm (by omega_using [hL]) fun u₁ o₁ e₁ => wp_lsr hlg fun u₂ o₂ e₂ => wp_eor fun u₃ o₃ e₃ =>
    wp_subImm (by decide) fun u₄ o₄ e₄ => wp_lsr (by decide) fun u₅ o₅ e₅ => wp_movz fun u₆ o₆ e₆ =>
    wp_sub fun u₇ o₇ e₇ => wp_addImm (by decide) fun u₈ o₈ e₈ => wp_addImm (by decide) fun u₉ o₉ e₉ =>
    wp_movz fun u₁₀ o₁₀ e₁₀ => wp_nil ?_)
  have O : Only [.x15, .x13, .x9, .x10, .x11, .x12] t u₁₀ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans o₁₀))))))))).mono
  have hfb : fb < 2 ^ 63 := by rw [← hfbd]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_arith)
  have x13 : u₁₀.gpr .x13 = if b = fb then BitVec.allOnes 64 else 0 := by
    rw [o₁₀.get .x13, o₉.get .x13, o₈.get .x13, e₇, e₆, o₆.get .x13, e₅, e₄, e₃, o₂.get .x27, o₁.get .x27, h27,
      e₂, e₁, h22, BitVec.ofNat_add_ofNat, lsr_val (by omega_arith), hB, hfbd, mask_val (by simp; omega_using [hb]) (by simp; omega_using [hfb])]
    by_cases e : b = fb
    · rw [ite_eq_left (by rw [e]), ite_eq_left e]
    · rw [ite_eq_right fun h' => e ((ofNat_eq_iff (by omega_using [hb]) (by omega_using [hfb])).mp h'), ite_eq_right e]
  refine WP.mono (wp_countdown (cnt := .x12) (N := H.P.N) (by omega_using [hN']) hN
    (fun j v => Keep [.x14, .x15, .x10, .x11, .x12] u₁₀ v ∧ v.gpr .x10 = off S (oSt + j) ∧
      v.gpr .x11 = off S (oSel + j) ∧ Frame [⟨S, oRsa⟩] t.mem v.mem ∧ Rep v.mem S (vSel V (b = fb) j))
    (fun j hj v ⟨hK, h10, h11, hF, hR⟩ _ => ?_)
    ⟨Keep.refl _ _, by rw [Nat.add_zero, o₁₀.get .x10, o₉.get .x10, e₈, o₇.get .x20, o₆.get .x20, o₅.get .x20,
      o₄.get .x20, o₃.get .x20, o₂.get .x20, o₁.get .x20, L.x20],
      by rw [Nat.add_zero, o₁₀.get .x11, e₉, o₈.get .x20, o₇.get .x20, o₆.get .x20, o₅.get .x20,
      o₄.get .x20, o₃.get .x20, o₂.get .x20, o₁.get .x20, L.x20], by rw [O.mem]; exact Frame.refl _ _,
      by rw [O.mem, vSel_zero]; exact R⟩
    (by rw [e₁₀]; apply BitVec.eq_of_toNat_eq; simp; omega_using [hN']))
    fun v ⟨hK, _, _, hF, hR⟩ => ⟨(O.keep.trans hK).mono, hF, hR⟩
  have rd : v.rd = t.rd := by rw [hK.rd, O.rd]
  have wr : v.wr = t.wr := by rw [hK.wr, O.wr]
  have h1 : oSt + j + 1 ≤ oRsa := by unfold oSt oRsa; omega_using [hN', hj]
  have h2 : oSel + j + 1 ≤ oRsa := by unfold oSel oRsa; omega_using [hN', hj]
  refine wp_ldrb (by decide) (by rw [h10, BitVec.add_zero]) (by rw [rd, wr]; exact L.ld h1) fun w₁ q₁ g₁ => ?_
  refine wp_ldrb (by decide) (by rw [q₁.get .x11, h11, BitVec.add_zero]) (by rw [q₁.rd, q₁.wr, rd, wr]; exact L.ld h2)
    fun w₂ q₂ g₂ => wp_eor fun w₃ q₃ g₃ => wp_and fun w₄ q₄ g₄ => wp_eor fun w₅ q₅ g₅ => ?_
  have Q₅ : Only [.x14, .x15] v w₅ := (q₁.trans (q₂.trans (q₃.trans (q₄.trans q₅)))).mono
  refine wp_strb (by decide) (by rw [Q₅.get .x11, h11, BitVec.add_zero]) (by rw [Q₅.wr, wr]; exact L.st h2)
    fun w₆ m₆ => wp_addImm (by decide) fun w₇ q₇ g₇ => wp_addImm (by decide) fun w₈ q₈ g₈ =>
    wp_subImm (by decide) fun w₉ q₉ g₉ => wp_nil ?_
  have ha : v.mem (off S (oSt + j)) = V (oSt + j) := by
    rw [hR _ (by omega_using [h1])]; simp only [vSel]; rw [ite_eq_right (by unfold oSt oSel; omega_using [hN', hj])]
  have hs : v.mem (off S (oSel + j)) = V (oSel + j) := by
    rw [hR _ (by omega_using [h2])]; simp only [vSel]; rw [ite_eq_right (by omega_using [])]
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
    exact hF.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [h2]) (by unfold oRsa at *; omega_using [h2]))
  · rw [hm, hb', ← vSel_succ V _]
    exact hR.wb (by omega_using [h2]) _
  · rw [g₉, q₈.get .x12, q₇.get .x12, m₆.gpr, Q₅.get .x12]

end VG.Proof.RsaPss.AArch64

end

end

/-!
# RSASSA-PSS on AArch64: compressing every block

`compLoop` compresses each of the `nbm` blocks of `Y` into the hash value at
`scratch + oSt`, and copies it to `scratch + oSel` after block
`fb = ⌊(ℓ + L) / B⌋` (`compLoop_ok`): the hash value at `oSel` is then that
of the first `fb + 1` blocks. The compression function is the one whose
address the slot `sCmpH` holds (`compT`), `cn`, which the calls of `f`
reach.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_subImm wp_lsl wp_add wp_sub)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.Pbkdf2.AArch64 (CallOk)
open VG.Proof.MdStream (Md)

/-- The `n` bytes of `Y` in the view `V`. -/
def yList (V : Nat → Byte) (n : Nat) : List Byte := (List.range n).map fun i => V (oY + i)

theorem yList_getD {V : Nat → Byte} {n i : Nat} (h : i < n) : (yList V n).getD i 0 = V (oY + i) := by
  simp [yList, List.getD_eq_getElem?_getD, h]

/-- The regions the compression loop writes: the compression function's
working space, the hash value and the selected hash value. -/
def CompW (so N o : Nat) : Prop := o < so ∨ (oSt ≤ o ∧ o < oSt + N) ∨ (oSel ≤ o ∧ o < oSel + N)

instance (so N o : Nat) : Decidable (CompW so N o) := by unfold CompW; infer_instance

section
variable {H : Hash} (hH : HashOK H) {f : MdFns} {cn : String}

/-- The compression loop, after the blocks before `b`. -/
structure CInv (t : State) (F S : Addr) (V₀ : Nat → Byte) (h₀ : hH.md.HV) (nbm fb : Nat) (b : Nat)
    (u : State) : Prop where
  sp : u.sp = t.sp
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  cs : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x28], u.gpr r = t.gpr r
  x27 : u.gpr .x27 = BitVec.ofNat 64 b
  vec : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64
  fr : Frame [⟨S, oRsa⟩] t.mem u.mem
  keep : ∀ o < oRsa, ¬ CompW H.P.so H.P.N o → u.mem (off S o) = V₀ o
  st : hH.md.stateAt u.mem (off S oSt) = hH.md.compressList h₀ (yList V₀ (nbm * H.P.B)) b
  sel : fb < b → hH.md.stateAt u.mem (off S oSel) = hH.md.compressList h₀ (yList V₀ (nbm * H.P.B)) (fb + 1)
  sy : u.syms = t.syms

/-- An address of the working space outside a region of it. -/
theorem not_in (S : Addr) {o e k : Nat} (h : o + 1 ≤ e ∨ e + k ≤ o) (ho : o < 8192) (he : e + k ≤ 8192) :
    ¬ (⟨off S e, k⟩ : Region).Contains (off S o) 1 :=
  fun hc => Offset.disjoint S h (by omega_using [ho]) (by omega_using [he]) _ (Region.contains_self _ _) hc

theorem not_in0 (S : Addr) {o k : Nat} (h : k ≤ o) (ho : o < 8192) (hk : k ≤ 8192) :
    ¬ (⟨S, k⟩ : Region).Contains (off S o) 1 := by
  have := not_in S (o := o) (e := 0) (k := k) (.inr (by omega_using [h])) ho (by omega_using [hk])
  rwa [off, BitVec.add_zero] at this

theorem off_add (p : Addr) (a b : Nat) : off p a + BitVec.ofNat 64 b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

include hH in
theorem so_lt : H.P.so < 2048 := by
  have := hH.sizes.fits; have := hH.W; omega_arith

theorem lsl_val {x k : Nat} (hx : x * 2 ^ k < 2 ^ 64) : BitVec.ofNat 64 x <<< k = BitVec.ofNat 64 (x * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show x < 2 ^ 64 from Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) hx),
    Nat.mod_eq_of_lt hx]

/-- One block. -/
theorem comp_step {t : State} {F S : Addr} (L : Lay t F S) {V₀ : Nat → Byte} {h₀ : hH.md.HV} {ℓ nbm b : Nat}
    (hB : 2 ^ lgB H = H.P.B) (hlg : lgB H < 64) (hℓ : ℓ < 2 ^ 62) (hnb : nbm * H.P.B ≤ 2048) (hb : b < nbm)
    (h22 : t.gpr .x22 = BitVec.ofNat 64 ℓ) (h19 : t.gpr .x19 = off S oSt)
    (hNb : t.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm)
    (hC : t.mem.readW (off F sCmpH) 64 = t.syms cn) (hfc : Finds f.comp t.syms (t.syms cn) cn H.compC) {u : State}
    (I : CInv hH t F S V₀ h₀ nbm ((ℓ + H.P.L) / H.P.B) b u) :
    WP isa (seqs [.block (compArgs H), compT f, select H, .block nextBlock]) u fun u' =>
      CInv hH t F S V₀ h₀ nbm ((ℓ + H.P.L) / H.P.B) (b + 1) u' ∧
        ((u'.gpr .x9).toNat ≠ 0 ↔ b + 1 ≠ nbm) := by
  generalize hfbd : (ℓ + H.P.L) / H.P.B = fb at I ⊢
  obtain hso := so_lt hH
  have hN := hH.N_le
  have hN0 := hH.sizes.dims.N.1
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hL := hH.L
  obtain hBb : H.P.B * (b + 1) ≤ H.P.B * nbm := Nat.mul_le_mul_left _ hb
  obtain hBn : H.P.B * nbm ≤ 2048 := by rw [Nat.mul_comm]; exact hnb
  obtain hBb' : H.P.B * b + H.P.B ≤ H.P.B * nbm := by rw [← Nat.mul_succ]; exact hBb
  obtain hcm : b * H.P.B = H.P.B * b := Nat.mul_comm _ _
  obtain hnb1 : nbm ≤ 2048 := Nat.le_trans (Nat.le_mul_of_pos_right _ hB0) hnb
  obtain Lu : Lay u F S := L.congr I.sp I.wr (by rw [I.cs .x20 (by decide)])
  refine WP.of_syms ?_
  simp only [seqs]
  unfold compArgs
  refine WP.seq (WP.of_syms (wp_lsl hlg fun u₁ o₁ e₁ => wp_add fun u₂ o₂ e₂ => wp_addImm (by decide) fun u₃ o₃ e₃ =>
    wp_nil fun sy₃ => ?_))
  obtain O₃ : Only [.x1] u u₃ := (o₁.trans (o₂.trans o₃)).mono
  obtain x1 : u₃.gpr .x1 = off S (oY + H.P.B * b) := by
    rw [e₃, e₂, e₁, o₁.get .x20, I.x27, I.cs .x20 (by decide), L.x20, lsl_val (by rw [hB]; omega_arith),
      hB]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mul_comm b]; omega_arith
  obtain hcall : CallOk u₃ H.P.N H.P.B H.P.so (off S oSt) S (off S (oY + H.P.B * b)) := {
    x19 := by rw [O₃.get .x19, I.cs .x19 (by decide), h19]
    x20 := by rw [O₃.get .x20, I.cs .x20 (by decide), L.x20]
    x1 := x1
    st_scr := by
      have := Offset.disjoint S (d := oSt) (n := H.P.N) (e := 0) (k := H.P.so) (by unfold oSt; omega_arith)
        (by unfold oSt; omega_arith) (by omega_arith)
      rwa [BitVec.add_zero] at this
    src_st := Offset.disjoint S (by unfold oY oSt; omega_arith) (by unfold oY; omega_arith) (by unfold oSt; omega_arith)
    src_scr := by
      have := Offset.disjoint S (d := oY + H.P.B * b) (n := H.P.B) (e := 0) (k := H.P.so) (by unfold oY; omega_arith)
        (by unfold oY; omega_arith) (by omega_arith)
      rwa [BitVec.add_zero] at this
    cov := by
      rw [O₃.rd, O₃.wr]
      refine Covers.cons (Covers.one (Lu.ld (by unfold oY oRsa; omega_arith))) (Covers.cons
        (Covers.one (Lu.ld (by unfold oSt oRsa; omega_arith))) (Covers.cons (Covers.one ?_) Covers.nil))
      have := Lu.ld (o := 0) (n := H.P.so) (by unfold oRsa; omega_arith)
      rwa [off, BitVec.add_zero] at this
    covW := by
      rw [O₃.wr]
      refine Covers.cons (Covers.one (Lu.st (by unfold oSt oRsa; omega_arith))) (Covers.cons (Covers.one ?_) Covers.nil)
      have := Lu.st (o := 0) (n := H.P.so) (by unfold oRsa; omega_arith)
      rwa [off, BitVec.add_zero] at this }
  obtain hC₃ : u₃.mem.readW (u₃.sp + BitVec.ofNat 64 sCmpH) 64 = u₃.syms cn := by
    rw [O₃.mem, O₃.sp, Lu.sp, sy₃, I.sy, I.fr.readW (r := ⟨F, frameBytes⟩) (Offset.contains_base _ (by decide) (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact L.dFS) (by decide)]
    exact hC
  obtain hin₃ : InRegions (u₃.rd ++ u₃.wr) (u₃.sp + BitVec.ofNat 64 sCmpH) 8 := by
    rw [O₃.rd, O₃.wr, O₃.sp, Lu.sp]; exact Lu.fld (by decide)
  refine WP.seq (WP.mono_syms (compT_ok f hH.comp hcall hin₃ hC₃ (by rw [sy₃, I.sy]; exact hfc)
      (Q := fun s' => (s'.rd = u₃.rd ∧
      s'.wr = u₃.wr ∧ (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = u₃.gpr r) ∧ s'.sp = u₃.sp ∧
      Frame [⟨off S oSt, H.P.N⟩, ⟨S, H.P.so⟩] u₃.mem s'.mem ∧
      hH.md.stateAt s'.mem (off S oSt) = hH.md.compress (hH.md.stateAt u₃.mem (off S oSt))
        (hH.md.blockAt u₃.mem (off S (oY + H.P.B * b)))) ∧
      ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (u₃.v r).extractLsb' 0 64)
      fun s' a b c d e f g => ⟨⟨a, b, c, d, e, f⟩, g⟩)
    fun v ⟨⟨vrd, vwr, vcs, vsp, vfr, vst⟩, vv⟩ syv => ?_)
  obtain Lv : Lay v F S := Lu.congr (by rw [vsp, O₃.sp]) (by rw [vwr, O₃.wr])
    (by rw [vcs .x20 (by decide) (by decide), O₃.get .x20])
  obtain v22 : v.gpr .x22 = BitVec.ofNat 64 ℓ := by
    rw [vcs .x22 (by decide) (by decide), O₃.get .x22, I.cs .x22 (by decide), h22]
  obtain v27 : v.gpr .x27 = BitVec.ofNat 64 b := by rw [vcs .x27 (by decide) (by decide), O₃.get .x27, I.x27]
  refine WP.seq (WP.mono (select_ok H Lv (V := fun o => v.mem (off S o)) (fun _ _ => rfl) hB hlg hN0 hN hL.2 hℓ
    (by omega_arith) v22 v27) fun w ⟨wK, wfr, wR⟩ => ?_)
  rw [hfbd] at wR
  -- the frame's slot is kept
  obtain frS : Frame [⟨S, oRsa⟩] t.mem w.mem := by
    refine I.fr.trans ((Frame.sub (by rw [O₃.mem] at vfr; exact vfr) fun r hr => ?_).trans wfr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by unfold oSt oRsa; omega_arith)⟩
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by unfold oRsa; omega_arith)⟩
  obtain slot : w.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm := by
    rw [frS.readW (r := ⟨F, frameBytes⟩) (Offset.contains_base _ (by decide) (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact L.dFS) (by decide), hNb]
  refine wp_addImm (by decide) fun w₁ p₁ f₁ => wp_ldrSp (by decide) ?_ fun w₂ p₂ f₂ =>
    wp_sub fun w₃ p₃ f₃ => wp_nil ?_
  · rw [p₁.sp, wK.sp, Lv.sp, p₁.rd, p₁.wr, wK.rd, wK.wr]; exact Lv.fld (d := sNb) (n := 8) (by decide)
  obtain P₃ : Only [.x27, .x9] w w₃ := (p₁.trans (p₂.trans p₃)).mono
  rw [p₁.sp, wK.sp, Lv.sp, p₁.mem, slot] at f₂
  obtain x27 : w₃.gpr .x27 = BitVec.ofNat 64 (b + 1) := by
    rw [p₃.get .x27, p₂.get .x27, f₁, wK.get .x27, v27, BitVec.ofNat_add_ofNat]
  -- bytes outside the regions the call and the selection write
  obtain wv : ∀ o < oRsa, ¬ (oSel ≤ o ∧ o < oSel + H.P.N) → w.mem (off S o) = v.mem (off S o) := fun o ho h => by
    rw [wR o ho]; simp only [vSel]; rw [ite_eq_right (fun h' => h h'.2)]
  obtain vu : ∀ o < oRsa, ¬ (oSt ≤ o ∧ o < oSt + H.P.N) → H.P.so ≤ o → v.mem (off S o) = u.mem (off S o) :=
    fun o ho h h' => by
      rw [vfr (off S o) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact not_in S (by omega_arith) (by unfold oRsa at ho; omega_arith) (by unfold oSt; omega_arith)
        · exact not_in0 S h' (by unfold oRsa at ho; omega_arith) (by omega_arith)), O₃.mem]
  obtain hY : ∀ k < H.P.B, u.mem (off S (oY + H.P.B * b) + BitVec.ofNat 64 k) =
      (yList V₀ (nbm * H.P.B)).getD (H.P.B * b + k) 0 := fun k hk => by
    rw [off_add, yList_getD (by rw [Nat.mul_comm nbm]; omega_arith), I.keep _ (by unfold oY oRsa; omega_arith)
      (by unfold CompW oY oSt oSel; omega_arith), Nat.add_assoc]
  obtain stw : hH.md.stateAt w.mem (off S oSt) = hH.md.compressList h₀ (yList V₀ (nbm * H.P.B)) (b + 1) := by
    rw [hH.md.stateAt_congr (mem := v.mem) fun i hi => by
        rw [off_add]; exact wv _ (by unfold oSt oRsa; omega_arith) (by unfold oSt oSel; omega_arith), vst,
      O₃.mem, I.st, hH.md.compressList_succ]
    exact congrArg _ (hH.md.parse_congr fun k hk => hY k hk)
  intro syw
  refine ⟨⟨?sp, ?rd, ?wr, ?cs, x27, ?vec, ?fr, ?keep, ?st, ?sel, ?sy⟩, ?flag⟩
  case sy => rw [syw, I.sy]
  case sp => rw [P₃.sp, wK.sp, vsp, O₃.sp, I.sp]
  case rd => rw [P₃.rd, wK.rd, vrd, O₃.rd, I.rd]
  case wr => rw [P₃.wr, wK.wr, vwr, O₃.wr, I.wr]
  case cs =>
    intro r hr
    obtain h1 : r ∉ [Reg.x27, .x9] := by revert r; decide
    obtain h2 : r ∉ [Reg.x15, .x9, .x13, .x10, .x11, .x12, .x14] := by revert r; decide
    obtain h3 : r ∈ preserved := by revert r; decide
    obtain h4 : r ≠ .x30 := by revert r; decide
    obtain h5 : r ∉ [Reg.x1] := by revert r; decide
    rw [P₃.gpr r h1, wK.gpr r h2, vcs r h3 h4, O₃.gpr r h5, I.cs r hr]
  case vec => intro r hr; rw [P₃.vcs r hr, wK.vcs r hr, vv r hr, O₃.vcs r hr, I.vec r hr]
  case fr => rw [P₃.mem]; exact frS
  case keep =>
    intro o ho h
    unfold CompW at h
    rw [P₃.mem, wv o ho (by omega_arith), vu o ho (by omega_arith) (by omega_arith), I.keep o ho (by unfold CompW; omega_arith)]
  case st => rw [P₃.mem]; exact stw
  case sel =>
    intro hfb
    rw [P₃.mem]
    by_cases e : b = fb
    · rw [hH.reloc w.mem w.mem (off S oSt) (off S oSel) fun i hi => by
        rw [off_add, off_add, wR _ (by unfold oSel oRsa; omega_arith)]; simp only [vSel]
        rw [ite_eq_left ⟨e, by omega_arith, by omega_arith⟩, Nat.add_sub_cancel_left]
        exact (wv _ (by unfold oSt oRsa; omega_arith) (by unfold oSt oSel; omega_arith)).symm, stw, e]
    · rw [hH.md.stateAt_congr (mem := u.mem) fun i hi => by
        rw [off_add, wR _ (by unfold oSel oRsa; omega_arith)]; simp only [vSel]
        rw [ite_eq_right (fun h' => e h'.1)]
        exact vu _ (by unfold oSel oRsa; omega_arith) (by unfold oSel oSt; omega_arith) (by unfold oSel; omega_arith)]
      exact I.sel (by omega_arith)
  case flag =>
    rw [f₃, f₂, p₂.get .x27, f₁, wK.get .x27, v27, BitVec.ofNat_add_ofNat, BitVec.toNat_sub, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    omega_arith

/-- Every block: the hash value at `oSel` is that of the first `fb + 1`
blocks. -/
theorem compLoop_ok {t : State} {F S : Addr} (L : Lay t F S) {V₀ : Nat → Byte} (R : Rep t.mem S V₀) {ℓ nbm : Nat}
    (hB : 2 ^ lgB H = H.P.B) (hlg : lgB H < 64) (hℓ : ℓ < 2 ^ 62) (hnb : nbm * H.P.B ≤ 2048) (hnb0 : 0 < nbm)
    (h22 : t.gpr .x22 = BitVec.ofNat 64 ℓ) (h19 : t.gpr .x19 = off S oSt)
    (hNb : t.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm)
    (hC : t.mem.readW (off F sCmpH) 64 = t.syms cn) (hfc : Finds f.comp t.syms (t.syms cn) cn H.compC) :
    WP isa (compLoop f H) t
      (CInv hH t F S V₀ (hH.md.stateAt t.mem (off S oSt)) nbm ((ℓ + H.P.L) / H.P.B) nbm) := by
  unfold compLoop
  refine WP.seq (WP.of_syms (wp_movz fun u o e => wp_nil fun syu => ?_))
  refine VG.Proof.MlKem.AArch64.count_loop (cr := .x9) hnb0 _
    (fun b hb u I => comp_step hH L hB hlg hℓ hnb hb h22 h19 hNb hC hfc I) ?_
  exact {
    sp := o.sp, rd := o.rd, wr := o.wr
    cs := fun r hr => o.gpr r (by revert r; decide)
    x27 := by rw [e]; rfl
    vec := o.vcs
    fr := by rw [o.mem]; exact Frame.refl _ _
    keep := fun x hx _ => by rw [o.mem]; exact R x hx
    st := by rw [o.mem, hH.md.compressList_zero]
    sel := fun h => absurd h (Nat.not_lt_zero _)
    sy := syu }

end

end VG.Proof.RsaPss.AArch64
