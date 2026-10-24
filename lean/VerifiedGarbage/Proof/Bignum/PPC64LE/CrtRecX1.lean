module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtExport
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA private-key operation on PPC64LE: `h` and `m₂` into `X`

`xfer_ok`: a prime's array 4 into `X`'s array `j`, zero-extended.
`blkP_ok`, `blkQ_ok`: the registers for it, for `p` and for `q`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

theorem x11_val {w : Nat} (hw : w < 2 ^ 31) :
    (BitVec.ofNat 64 (8 * (w + 2)) - BitVec.ofNat 64 16) >>> 2 = BitVec.ofNat 64 (2 * w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 8 * (w + 2) < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 16 < 2 ^ 64 by decide),
    show 2 ^ 64 - 16 + 8 * (w + 2) = 8 * w + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (show 8 * w < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 2 * w < 2 ^ 64 by omega)]
  omega

/-- Three programs then a fourth, regrouped. -/
theorem wp_reassoc3 {a b c d : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b c)) d) s Q) : WP isa (.seq a (.seq b (.seq c d))) s Q := by
  obtain ⟨t, s', hx, hq⟩ := h
  cases hx with
  | seq h1 h2 =>
    cases h1 with
    | seq ha hbc =>
      cases hbc with
      | seq hb hc => exact ⟨_, _, .seq ha (.seq hb (.seq hc h2)), hq⟩

/-- `zeroWords`, `xb r14 j`, `r11 := r22`, `copyN`: `w_A` words of a prime's
array 4 (`r15`) into `X`'s array `j` (`r14`), zero-extended to `w_X` words
(`r11`), for `2 w_A` in `r22`. -/
theorem xfer_ok {s : State} {BX : Addr} {Z oA wA wX j : Nat} (hs : Scr s BX Z) (hA : oA + slot wA 8 ≤ Z)
    (hXA : slot wX 8 ≤ oA) (hj : j < 8) (hw1 : 1 ≤ wA) (hwx : wA ≤ wX) (hwX : wX < 2 ^ 31)
    (h14 : s.gpr .r14 = off BX (slot wX j)) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wX))
    (h22 : s.gpr .r22 = BitVec.ofNat 64 (2 * wA)) (h15 : s.gpr .r15 = off (off BX oA) (slot wA 4))
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2))) :
    WP isa (.seq Precompute.zeroWords (.seq (.block (xb .r14 j ++ ([.addi .r11 .r22 0] : List Instr))) copyN)) s fun t =>
      (val32 t.mem BX (slot wX j) (2 * wX) = val32 s.mem (off BX oA) (slot wA 4) (2 * wA) ∧
        Outside BX (slot wX j) (8 * wX) s.mem t.mem) ∧ Keep [.r0, .r11, .r14, .r15, .r17] s t := by
  have hn := hs.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  have eA4 := e wA 4; have eA8 := e wA 8
  have sXj := slot_le (w := wX) hj
  refine WP.seq (WP.mono (zeroWords_ok hs h14 h11 (by omega) hwX (by omega)) fun s₁ ⟨⟨_, hz, out1⟩, k1⟩ => ?_)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (xb_ok (rd := .r14) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h27)
    ((k1.gpr _ (by decide)).trans h28) j) fun s₂ ⟨⟨a14, m2⟩, k2⟩ => ?_
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 (2 * wA) ∧ t.mem = s₂.mem)
    (by prun [(k2.gpr .r22 (by decide)).trans ((k1.gpr .r22 (by decide)).trans h22), BitVec.add_zero])
    (by decide)) fun s₃ ⟨⟨a11, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  refine WP.mono (copySub_ok (a := oA + slot wA 4) (b := slot wX j) (w := wA) (hs.congr k13.wr)
    (by rw [k13.gpr _ (by decide), h15, off_off]) ((k3.gpr _ (by decide)).trans a14) a11 hw1
    (by omega) (by omega) (by omega) (by omega)) fun t ⟨⟨hw, out4⟩, k4⟩ => ⟨⟨?_, ?_⟩, (k13.trans k4).mono⟩
  · rw [m3, m2] at hw out4
    have hsrc : ∀ i < wA, word s₁.mem BX (oA + slot wA 4 + 8 * i) = word s.mem BX (oA + slot wA 4 + 8 * i) :=
      fun i hi => out1.word (Or.inr (by omega)) (by omega)
    have hsplit := wv_add t.mem BX (slot wX j) wA (wX - wA)
    rw [show wA + (wX - wA) = wX by omega] at hsplit
    have hlo : wv t.mem BX (slot wX j) wA = wv s.mem BX (oA + slot wA 4) wA :=
      wv_congr2 fun i hi => (hw i hi).trans (hsrc i hi)
    have hhi : wv t.mem BX (slot wX j + 8 * wA) (wX - wA) = 0 := (wv_eq_zero_iff _ _ _ _).mpr fun q hq => by
      rw [out4.word (Or.inr (by omega)) (by omega), show slot wX j + 8 * wA + 8 * q = slot wX j + 8 * (wA + q) by omega]
      exact hz _ (by omega)
    rw [Pre.val32_eq_wv, Pre.val32_eq_wv, wv_off, hsplit, hlo, hhi, Nat.mul_zero, Nat.add_zero]
  · rw [m3, m2] at out4
    exact out1.trans (out4.mono (by omega) (by omega))

/-- `r22 := r11`, `p`'s form: `2 w_A` in both, `w_A` in `r4`. -/
theorem midP_ok {t : State} {wA : Nat} (h11 : t.gpr .r11 = BitVec.ofNat 64 (2 * wA))
    (h4 : t.gpr .r4 = BitVec.ofNat 64 wA) (hw : wA < 2 ^ 58) :
    WP isa (.block [.addi .r22 .r11 0, .lsl .r11 .r4 1]) t fun t' =>
      (t'.gpr .r22 = BitVec.ofNat 64 (2 * wA) ∧ t'.gpr .r11 = BitVec.ofNat 64 (2 * wA) ∧ t'.mem = t.mem) ∧
        Keep [.r11, .r22] t t' := by
  refine WP.keep _ ?_ (by decide)
  prun [h11, h4, shl_ofNat (show wA * 2 ^ 1 < 2 ^ 64 by omega), BitVec.add_zero]
  congr 1; omega

/-- `r22 := r11`, `q`'s form. -/
theorem midQ_ok {t : State} {wA : Nat} (h11 : t.gpr .r11 = BitVec.ofNat 64 (2 * wA)) :
    WP isa (.block [.addi .r22 .r11 0]) t fun t' =>
      (t'.gpr .r22 = BitVec.ofNat 64 (2 * wA) ∧ t'.gpr .r11 = BitVec.ofNat 64 (2 * wA) ∧ t'.mem = t.mem) ∧
        Keep [.r11, .r22] t t' := by
  refine WP.keep _ ?_ (by decide)
  prun [h11, BitVec.add_zero]

/-- The registers for `xfer`: a prime's working space at `off BX oA` (the
header's word `oB`, its length at `oLen`), its array 4 in `r15`, `X`'s array
`j` in `r14`, `2 w_X` in `r11`, `2 w_A` in `r22`. -/
theorem blk_ok {s : State} {BX : Addr} {Z oA len oB oLen wX j : Nat} (mid : List Instr)
    (hmid : ∀ t : State, t.gpr .r11 = BitVec.ofNat 64 (2 * wsWords len) →
      t.gpr .r4 = BitVec.ofNat 64 (wsWords len) → WP isa (.block mid) t fun t' =>
        (t'.gpr .r22 = BitVec.ofNat 64 (2 * wsWords len) ∧ t'.gpr .r11 = BitVec.ofNat 64 (2 * wsWords len) ∧
          t'.mem = t.mem) ∧ Keep [.r11, .r22] t t')
    (hs : Scr s BX Z) (h23 : s.gpr .r23 = BX)
    (hoB : oB + 8 ≤ 256 ∧ oB % 8 = 0) (hoL : oLen + 8 ≤ 256 ∧ oLen % 8 = 0) (hZ : 256 ≤ Z)
    (hB : word s.mem BX oB = off BX oA) (hL : word s.mem BX oLen = BitVec.ofNat 64 len) (hl : 1 ≤ len)
    (hl' : len < 2 ^ 60) (hwX : wX < 2 ^ 31)
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2))) :
    WP isa (.block (setupP oB oLen ++ PublicChecked.base .r15 4 ++ mid ++ xb .r14 j ++
      ([.addi .r11 .r28 0, .subi .r11 .r11 16, .lsr .d .r11 .r11 2] : List Instr))) s fun t =>
      (t.gpr .r14 = off BX (slot wX j) ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * wX) ∧
        t.gpr .r22 = BitVec.ofNat 64 (2 * wsWords len) ∧ t.gpr .r15 = off (off BX oA) (slot (wsWords len) 4) ∧
        t.mem = s.mem) ∧ Keep [.r0, .r3, .r4, .r10, .r11, .r14, .r15, .r21, .r22, .r29] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (setupP_ok hs h23 hoB hoL hZ hB hL hl hl') fun s₁ ⟨⟨a10, _, a29, a11, a4, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) a10 a29 4) fun s₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hmid s₂ ((k2.gpr _ (by decide)).trans a11) ((k2.gpr _ (by decide)).trans a4))
    fun s₃ ⟨⟨a22, _, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  rw [WP.block_append_iff]
  refine WP.mono (xb_ok (rd := .r14) (by decide) (by decide) ((k13.gpr _ (by decide)).trans h27)
    ((k13.gpr _ (by decide)).trans h28) j) fun s₄ ⟨⟨a14, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 (2 * wX) ∧ t.mem = s₄.mem)
    (by prun [(k14.gpr .r28 (by decide)).trans h28, BitVec.add_zero, x11_val hwX]) (by decide))
    fun t ⟨⟨t11, tm⟩, k5⟩ => ⟨⟨(k5.gpr _ (by decide)).trans a14, t11,
      (k5.gpr _ (by decide)).trans ((k4.gpr _ (by decide)).trans a22),
      (k5.gpr _ (by decide)).trans ((k4.gpr _ (by decide)).trans ((k3.gpr _ (by decide)).trans a15)),
      by rw [tm, m4, m3, m2, m1]⟩, (k14.trans k5).mono⟩

end VG.Proof.Bignum.PPC64LE.Crt
