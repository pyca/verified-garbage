module

public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.RsaPss.AArch64.SignChecks
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# EMSA-PSS on AArch64: the mask of `maskedDB`'s top bits

`maskBits` stores `0xFF >>> z`, for `z = 8 emLen - emBits < 8`, to the slot
`sC`, a bit at a time (bit `j` is set iff `z < 8 - j`: `maskAcc`), and 0 to
`sLo` (`maskBits_ok`). `fitH` leaves `emLen` in `x9` and `x10` nonzero iff
`emLen < hLen + 2` (`fitH_ok`); `saltFits`, with the salt's length in `x12`,
leaves `x10` nonzero iff the salt does not fit (`saltFitsR_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_movz wp_subImm wp_lsr wp_lsl wp_orr wp_sub)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_mov borrow_ne)
open VG.Proof.RsaPss.AArch64 (borrow_or)

/-- The mask's bits `j < n`, from `z`. -/
def maskAcc (z : BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | n + 1 => maskAcc z n ||| ((z - BitVec.ofNat 64 (8 - n)) >>> 63) <<< n

theorem maskAcc_eq : ∀ z < 8, maskAcc (BitVec.ofNat 64 z) 8 = BitVec.setWidth 64 ((0xFF : Byte) >>> z) := by
  decide +kernel

theorem maskBit_ok (j : Nat) (hj : j < 8) {u : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ u', Only [.x12, .x11] u u' →
      u'.gpr .x11 = u.gpr .x11 ||| ((u.gpr .x9 - BitVec.ofNat 64 (8 - j)) >>> 63) <<< j → WP isa (.block is) u' Q) :
    WP isa (.block (maskBit j ++ is)) u Q := by
  unfold maskBit
  simp only [List.cons_append, List.nil_append]
  refine wp_subImm (by omega) fun u₁ o₁ e₁ => wp_lsr (by decide) fun u₂ o₂ e₂ => wp_lsl (by omega) fun u₃ o₃ e₃ =>
    wp_orr fun u₄ o₄ e₄ => k u₄ (o₁.trans (o₂.trans (o₃.trans o₄))).mono ?_
  rw [e₄, o₃.get .x11, o₂.get .x11, o₁.get .x11, e₃, e₂, e₁]

theorem maskSteps_ok : ∀ n, n ≤ 8 → ∀ {u : State} {is : List Instr} {Q : State → Prop}, u.gpr .x11 = 0 →
    (∀ u', Only [.x12, .x11] u u' → u'.gpr .x11 = maskAcc (u.gpr .x9) n → WP isa (.block is) u' Q) →
    WP isa (.block ((List.range n).flatMap maskBit ++ is)) u Q
  | 0, _, u, _, _, h, k => k u (Only.refl _ _) (by rw [h]; rfl)
  | n + 1, hn, u, is, Q, h, k => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_assoc]
    exact maskSteps_ok n (by omega) h fun u₁ o₁ e₁ => maskBit_ok n (by omega) fun u₂ o₂ e₂ =>
      k u₂ (o₁.trans o₂).mono (by rw [e₂, e₁, o₁.get .x9]; rfl)

theorem shl3_ofNat {k : Nat} (hk : k < 2 ^ 60) : BitVec.ofNat 64 k <<< 3 = BitVec.ofNat 64 (8 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  omega

/-- The mask to `sC` and `lo = 0` to `sLo`, from `emLen = k` in `x23` and
`emBits = eb` in `r`. -/
theorem maskBits_ok {u : State} {F : Addr} (hsp : u.sp = F) (hwC : InRegions u.wr (F + BitVec.ofNat 64 sC) 8)
    (hwL : InRegions u.wr (F + BitVec.ofNat 64 sLo) 8) {r : Reg} (hr : r ∉ [Reg.x9, .x11, .x12, .x16])
    {k eb : Nat} (hk : u.gpr .x23 = BitVec.ofNat 64 k) (heb : u.gpr r = BitVec.ofNat 64 eb) (h1 : eb ≤ 8 * k)
    (h2 : 8 * k - eb < 8) (hk2 : k < 2 ^ 60) :
    WP isa (.block (maskBits r)) u fun u' => Keep [.x9, .x11, .x12, .x16] u u' ∧
      u'.mem = (u.mem.writeW (F + BitVec.ofNat 64 sC) (BitVec.setWidth 64 ((0xFF : Byte) >>> (8 * k - eb)))).writeW
        (F + BitVec.ofNat 64 sLo) (0 : BitVec 64) := by
  unfold maskBits
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  refine wp_lsl (by decide) fun u₁ o₁ e₁ => wp_sub fun u₂ o₂ e₂ => wp_movz fun u₃ o₃ e₃ =>
    maskSteps_ok 8 (Nat.le_refl _) (by rw [e₃]; rfl) fun u₄ o₄ e₄ => ?_
  have hz : u₄.gpr .x11 = BitVec.setWidth 64 ((0xFF : Byte) >>> (8 * k - eb)) := by
    rw [e₄, o₃.get .x9, e₂, e₁, o₁.get r (by simp [hr.1]), heb, hk, shl3_ofNat hk2, Offset.ofNat_sub_ofNat h1]
    exact maskAcc_eq _ h2
  have O₄ : Only [.x9, .x11, .x12] u u₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine st_slot (by rw [O₄.sp, hsp]) (by decide) (by rw [O₄.wr]; exact hwC) (fun v₁ k₁ m₁ x₁ => ?_) (by decide)
  refine wp_movz fun v₂ o₂ e₂ => ?_
  refine st_slot (by rw [o₂.sp, k₁.sp, O₄.sp, hsp]) (by decide) (by rw [o₂.wr, k₁.wr, O₄.wr]; exact hwL)
    (fun v₃ k₃ m₃ _ => wp_nil ⟨(O₄.keep.trans (k₁.trans (o₂.keep.trans k₃))).mono, ?_⟩) (by decide)
  rw [m₃, o₂.mem, m₁, O₄.mem, e₂, hz]
  rfl

theorem fitH_ok (H : Hash) (hD : H.D + 2 < 4096) {u : State} {k : Nat} (hk : u.gpr .x23 = BitVec.ofNat 64 k)
    (hk2 : k < 2 ^ 63) :
    WP isa (.block (fitH H)) u fun u' => Only [.x9, .x10] u u' ∧ u'.gpr .x9 = BitVec.ofNat 64 k ∧
      (u'.gpr .x10 != 0) = decide (k < H.D + 2) := by
  unfold fitH
  refine wp_mov fun u₁ o₁ e₁ => wp_subImm (by omega) fun u₂ o₂ e₂ => wp_lsr (by decide) fun u₃ o₃ e₃ =>
    wp_nil ⟨(o₁.trans (o₂.trans o₃)).mono, by rw [o₃.get .x9, o₂.get .x9, e₁, hk], ?_⟩
  rw [e₃, e₂, e₁, hk]
  exact borrow_ne hk2 (by omega)

/-- `saltFits`, with the salt's length in `x12`. -/
theorem saltFitsR_ok (H : Hash) (hD : H.D + 2 < 4096) {u : State} {a : Nat} (ha : H.D + 2 ≤ a) (ha' : a < 2 ^ 32)
    (h9 : u.gpr .x9 = BitVec.ofNat 64 a) {y : BitVec 64} (h12 : u.gpr .x12 = y) :
    WP isa (.block (saltFits H)) u fun u' => Only [.x9, .x10, .x13] u u' ∧
      u'.gpr .x9 = BitVec.ofNat 64 (a - (H.D + 2)) ∧ (u'.gpr .x10 != 0) = decide (a - (H.D + 2) < y.toNat) := by
  unfold saltFits
  refine wp_subImm (by omega) fun u₂ o₂ e₂ => wp_sub fun u₃ o₃ e₃ => wp_lsr (by decide) fun u₄ o₄ e₄ =>
    wp_lsr (by decide) fun u₅ o₅ e₅ => wp_orr fun u₆ o₆ e₆ =>
      wp_nil ⟨(o₂.trans (o₃.trans (o₄.trans (o₅.trans o₆)))).mono, ?_, ?_⟩
  · rw [o₆.get .x9, o₅.get .x9, o₄.get .x9, o₃.get .x9, e₂, h9, Offset.ofNat_sub_ofNat ha]
  · have h12' : u₂.gpr .x12 = BitVec.ofNat 64 y.toNat := by rw [o₂.get .x12, h12, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
    rw [e₆, o₅.get .x10, e₄, e₃, e₂, h9, Offset.ofNat_sub_ofNat ha, h12', e₅, o₄.get .x12, o₃.get .x12, h12']
    exact borrow_or (by omega) y.isLt

end VG.Proof.RsaPss.AArch64
