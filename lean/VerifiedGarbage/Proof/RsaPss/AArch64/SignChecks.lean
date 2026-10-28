module
public import VerifiedGarbage.Impl.RsaPss.AArch64
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp

import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# RSASSA-PSS on AArch64: the encoding's parameters

`lo` and the mask `0xFF >>> z` of a modulus' first byte (`loV`, `maskV`), a
store to a slot of the frame (`st_slot`), and `saltFits`, which leaves
`emLen - hLen - 2` in `x9`, `x10` nonzero iff the salt is longer
(`saltFits_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_subImm wp_lsr wp_orr wp_strx wp_sub
  eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_addSp wp_mov setWidth_ofNat16 borrow_ne)

/-- `lo = k - emLen`: 1 if `n₀ = 1`. -/
def loV (x : Nat) : Nat := if x = 1 then 1 else 0

/-- The mask `0xFF >>> z`, as a word. -/
def maskV (x : Nat) : BitVec 64 := if x = 1 then BitVec.ofNat 64 0xFF else BitVec.ofNat 64 (2 ^ Nat.log2 x - 1)

/-- A slot of the frame, written. -/
theorem st_slot {t : State} {F : Addr} {d : Nat} (hsp : t.sp = F) (hd : d % 8 = 0 ∧ d < 32768)
    (hw : InRegions t.wr (F + BitVec.ofNat 64 d) 8) {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Keep [.x16] t t' → t'.mem = t.mem.writeW (F + BitVec.ofNat 64 d) (t.gpr r) →
      t'.gpr .x16 = F → WP isa (.block is) t' Q) (hr : r ≠ .x16) :
    WP isa (.block (st r d ++ is)) t Q := by
  unfold st
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  refine wp_strx hd (by rw [e₁]) (by rw [o₁.wr]; exact hw) fun u₂ m₂ => k u₂ (o₁.keep.trans m₂.keep).mono
    (by rw [m₂.mem, o₁.mem, o₁.get r (by simpa using hr)]) (by rw [m₂.gpr, e₁])

theorem borrow_or {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 64) :
    ((BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 ||| BitVec.ofNat 64 b >>> 63 != 0) = decide (a < b) := by
  by_cases h : b < 2 ^ 63
  · have e : BitVec.ofNat 64 b >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_zero]
      rw [Nat.mod_eq_of_lt hb]
      exact Nat.div_eq_of_lt h
    rw [e, BitVec.or_zero]
    exact borrow_ne ha h
  · have e : BitVec.ofNat 64 b >>> 63 = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt hb]
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [e, decide_eq_true (by omega)]
    generalize (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = x
    rw [bne_iff_ne, ne_eq]
    intro h'
    have := congrArg (fun y => y.getLsbD 0) h'
    simp at this

theorem saltFits_ok (H : Hash) (hD : H.D + 2 < 4096) {u : State} {F : Addr} (hsp : u.sp = F)
    (hrS : InRegions (u.rd ++ u.wr) (F + BitVec.ofNat 64 sSaltLen) 8) {a sl : Nat}
    (ha : H.D + 2 ≤ a) (ha' : a < 2 ^ 32) (h9 : u.gpr .x9 = BitVec.ofNat 64 a)
    (hsl : u.mem.readW (F + BitVec.ofNat 64 sSaltLen) 64 = BitVec.ofNat 64 sl) (hsl' : sl < 2 ^ 64) :
    WP isa (.block ([ld .x12 sSaltLen] ++ saltFits H)) u fun u' => Only [.x12, .x9, .x10, .x13] u u' ∧
      u'.gpr .x9 = BitVec.ofNat 64 (a - (H.D + 2)) ∧ (u'.gpr .x10 != 0) = decide (a - (H.D + 2) < sl) := by
  unfold saltFits ld
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrSp (by decide) (by rw [hsp]; exact hrS) fun u₁ o₁ e₁ => wp_subImm (by omega) fun u₂ o₂ e₂ =>
    wp_sub fun u₃ o₃ e₃ => wp_lsr (by decide) fun u₄ o₄ e₄ => wp_lsr (by decide) fun u₅ o₅ e₅ =>
    wp_orr fun u₆ o₆ e₆ => wp_nil ⟨(o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans o₆))))).mono, ?_, ?_⟩
  · rw [o₆.get .x9, o₅.get .x9, o₄.get .x9, o₃.get .x9, e₂, o₁.get .x9, h9, Offset.ofNat_sub_ofNat ha]
  · have h12 : u₁.gpr .x12 = BitVec.ofNat 64 sl := by rw [e₁, hsp, hsl]
    rw [e₆, o₅.get .x10, e₄, e₃, e₂, o₁.get .x9, h9, Offset.ofNat_sub_ofNat ha, o₂.get .x12, h12, e₅,
      o₄.get .x12, o₃.get .x12, o₂.get .x12, h12]
    exact borrow_or (by omega) hsl'

end VG.Proof.RsaPss.AArch64