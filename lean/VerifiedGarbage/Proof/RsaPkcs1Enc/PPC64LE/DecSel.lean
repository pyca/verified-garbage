module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecScan
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Select
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: the validity of the padding

The validity of the padding, the selected length and the mask of the
private-key operation's success (`validBlock_ok`), from the registers the
scan left.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
open VG.Proof.Bignum.PPC64LE (Keep)
open VG.Proof.RsaPkcs1Enc (firstZero vOf lselOf outByte)

/-- `-(x = 0)`, for `x < 2 ^ 63`. -/
theorem zero_mask64 (x : BitVec 64) (hx : x.toNat < 2 ^ 63) :
    (0 : BitVec 64) - ((x - BitVec.ofNat 64 1) >>> 63) = bm (decide (x = 0)) := by
  by_cases h : x = 0
  · subst h; decide
  · have hb : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    have e2 : (x - BitVec.ofNat 64 1) >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega),
        BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      show _ = 0
      omega
    rw [e2]
    simp only [bm, h, decide_false, Bool.false_eq_true, ite_false]; rfl

theorem ten_mask {sep : Nat} (h : sep < 2 ^ 63) :
    (0 : BitVec 64) - ((BitVec.ofNat 64 sep - BitVec.ofNat 64 10) >>> 63) = bm (decide (sep < 10)) := by
  rw [borrow _ _ h (by decide)]
  by_cases hs : sep < 10
  · simp only [show ¬ 10 ≤ sep by omega, ↓reduceIte, bm, hs, decide_true]; decide
  · simp only [show 10 ≤ sep by omega, ↓reduceIte, bm, hs, decide_false, Bool.false_eq_true]; decide

theorem bm_and (a b : Bool) : bm a &&& bm b = bm (a && b) := by
  cases a <;> cases b <;> rfl

theorem bm_not (a : Bool) : bm a ^^^ BitVec.allOnes 64 = bm (!a) := by
  cases a <;> decide

theorem sel_xor (x y : BitVec 64) (v : Bool) : x ^^^ ((y ^^^ x) &&& bm v) = if v then y else x := by
  cases v
  · simp [bm]
  · simp only [bm, ite_true, BitVec.and_allOnes]
    rw [← BitVec.xor_assoc, BitVec.xor_comm x y, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem byte_zero (b : Byte) : decide (b.setWidth 64 = (0 : BitVec 64)) = decide (b = 0) := by
  by_cases h : b = 0
  · subst h; decide
  · have hb : b.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    have : b.setWidth 64 ≠ 0 := fun e => hb (by
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))] at this)
    simp only [this, h, decide_false]

theorem byte_two (b : Byte) :
    decide (b.setWidth 64 ^^^ BitVec.ofNat 64 2 = (0 : BitVec 64)) = decide (b = 2) := by
  rw [decide_eq_decide, show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
  constructor
  · intro e
    have := congrArg (BitVec.setWidth 8) e
    rwa [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] at this
  · intro e; subst e; decide

theorem byte_lt (b : Byte) : (b.setWidth 64).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))]
  exact Nat.lt_trans b.isLt (by decide)

theorem byte2_lt (b : Byte) : (b.setWidth 64 ^^^ BitVec.ofNat 64 2).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_xor, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide)),
    BitVec.toNat_ofNat]
  exact Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow (n := 8) b.isLt (by decide)) (by decide)

theorem vOf_bm (a b : Byte) (f : Bool) (sep : Nat) :
    bm f &&& (bm (decide (a = 0)) &&& bm (decide (b = 2))) &&& bm (!decide (sep < 10)) = bm (vOf a b f sep) := by
  have e : (!decide (sep < 10)) = decide (10 ≤ sep) := by
    by_cases hs : sep < 10
    · simp only [hs, decide_true, Bool.not_true, show ¬ 10 ≤ sep by omega, decide_false]
    · simp only [hs, decide_false, Bool.not_false, show 10 ≤ sep by omega, decide_true]
  rw [bm_and, bm_and, bm_and, e]
  congr 1
  unfold vOf
  cases f <;> by_cases ha : a = 0 <;> by_cases hb : b = 2 <;> by_cases hs : 10 ≤ sep <;> simp [ha, hb, hs]

/-- `validBlock` from the load of `EM[1]` on. -/
def validRest : List Instr :=
  [.lbz .r9 .r11 1, .li .r4 2, .logic .xor .r9 .r9 .r4, .subi .r9 .r9 1, .lsr .d .r9 .r9 63,
    .sub .r9 .r0 .r9, .logic .and .r10 .r10 .r9, .logic .and .r5 .r5 .r10,
    .li .r4 10, .sub .r9 .r3 .r4, .lsr .d .r9 .r9 63, .sub .r9 .r0 .r9, .logic .xor .r9 .r9 .r8,
    .logic .and .r5 .r5 .r9,
    .sub .r9 .r7 .r3, .subi .r9 .r9 1, .logic .xor .r9 .r9 .r6, .logic .and .r9 .r9 .r5,
    .logic .xor .r6 .r6 .r9,
    .load .d .r4 .r12 Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR, .li .r9 1, .logic .xor .r4 .r4 .r9, .subi .r4 .r4 1,
    .lsr .d .r4 .r4 63, .sub .r4 .r0 .r4,
    .sub .r3 .r7 .r6, .logic .and .r6 .r6 .r4]

/-- The block's results, from the registers the scan left. -/
theorem validBlock_ok {s : State} {R : BitVec 64} {EM : List Byte} {t : State} (hc : Post s R EM t)
    (h0 : InRegions (t.rd ++ t.wr) (s.gpr .r3 + BitVec.ofNat 64 0) 1)
    (h1 : InRegions (t.rd ++ t.wr) (s.gpr .r3 + BitVec.ofNat 64 1) 1)
    {f : Bool} {sep al : Nat} (h5 : t.gpr .r5 = bm f) (h3 : t.gpr .r3 = BitVec.ofNat 64 sep)
    (h6 : t.gpr .r6 = BitVec.ofNat 64 al) (h0' : t.gpr .r0 = 0) (h8 : t.gpr .r8 = BitVec.allOnes 64)
    (hsep : sep < 2 ^ 63) (hR : (R ^^^ BitVec.ofNat 64 1).toNat < 2 ^ 63) :
    WP isa (.block validBlock) t fun u => (u.mem = t.mem ∧ u.gpr .r11 = s.gpr .r3 ∧ u.gpr .r7 = s.gpr .r7 ∧
      u.gpr .r5 = bm (vOf (t.mem (s.gpr .r3 + BitVec.ofNat 64 0)) (t.mem (s.gpr .r3 + BitVec.ofNat 64 1)) f sep) ∧
      u.gpr .r4 = bm (decide (R ^^^ BitVec.ofNat 64 1 = 0)) ∧
      u.gpr .r6 = (if vOf (t.mem (s.gpr .r3 + BitVec.ofNat 64 0)) (t.mem (s.gpr .r3 + BitVec.ofNat 64 1)) f sep then
          s.gpr .r7 - BitVec.ofNat 64 sep - BitVec.ofNat 64 1 else BitVec.ofNat 64 al) &&&
        bm (decide (R ^^^ BitVec.ofNat 64 1 = 0)) ∧
      u.gpr .r3 = s.gpr .r7 - (if vOf (t.mem (s.gpr .r3 + BitVec.ofNat 64 0)) (t.mem (s.gpr .r3 + BitVec.ofNat 64 1))
          f sep then s.gpr .r7 - BitVec.ofNat 64 sep - BitVec.ofNat 64 1 else BitVec.ofNat 64 al) ∧
      u.gpr .r12 = fb s) ∧
      Keep [.r12, .r11, .r7, .r10, .r9, .r4, .r5, .r6, .r3] t u := by
  have c1 : oOut < 2 ^ 15 ∧ oOut % 4 = 0 := by decide
  have c2 : oK < 2 ^ 15 ∧ oK % 4 = 0 := by decide
  have c3 : Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR < 2 ^ 15 ∧ Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR % 4 = 0 := by decide
  have i1 := slot_rd hc (d := oOut) (by decide) (by decide)
  have i2 := slot_rd hc (d := oK) (by decide) (by decide)
  have i3 := slot_rd hc (d := Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR) (by decide) (by decide)
  have c0 : (0 : Nat) < 2 ^ 15 := by decide
  have c1' : (1 : Nat) < 2 ^ 15 := by decide
  rw [show validBlock = ([fp, .load .d .r11 .r12 oOut, .load .d .r7 .r12 oK, .lbz .r10 .r11 0, .subi .r10 .r10 1,
      .lsr .d .r10 .r10 63, .sub .r10 .r0 .r10] : List Instr) ++ validRest from rfl, WP.block_append_iff]
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r11, .r7, .r10] (Q := fun u => u.mem = t.mem ∧
    u.gpr .r12 = fb s ∧ u.gpr .r11 = s.gpr .r3 ∧ u.gpr .r7 = s.gpr .r7 ∧
    u.gpr .r10 = bm (decide (t.mem (s.gpr .r3 + BitVec.ofNat 64 0) = 0))) ?_ rfl) fun u ⟨⟨um, u12, u11, u7, u10⟩, ku⟩ => ?_
  · prun [fp, exec_addSp0, hc.sp, c1, c2, i1, i2, hc.sl.out, hc.sl.k, h0',
      exec_lbz (s := ((t.write .r12 (fb s)).write .r11 (s.gpr .r3)).write .r7 (s.gpr .r7))
        (show Reg.r11 ≠ .r0 by decide) c0 (by exact h0)]
    simp only [read1_64, zero_mask64 _ (byte_lt _), byte_zero]
  have u0 : u.gpr .r0 = 0 := (ku.gpr _ (by decide)).trans h0'
  have u3 : u.gpr .r3 = BitVec.ofNat 64 sep := (ku.gpr _ (by decide)).trans h3
  have u5 : u.gpr .r5 = bm f := (ku.gpr _ (by decide)).trans h5
  have u6 : u.gpr .r6 = BitVec.ofNat 64 al := (ku.gpr _ (by decide)).trans h6
  have u8 : u.gpr .r8 = BitVec.allOnes 64 := (ku.gpr _ (by decide)).trans h8
  have j1 : InRegions (u.rd ++ u.wr) (u.gpr .r11 + BitVec.ofNat 64 1) 1 := by rw [ku.rd, ku.wr, u11]; exact h1
  have j3 : InRegions (u.rd ++ u.wr) (fb s + BitVec.ofNat 64 Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR) 8 := by
    rw [ku.rd, ku.wr]; exact i3
  have hr : u.mem.readW (fb s + BitVec.ofNat 64 Impl.RsaPkcs1Enc.PPC64LE.Decrypt.oR) 64 = R := by rw [um]; exact hc.r
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r9, .r4, .r10, .r5, .r6, .r3] (Q := fun w => w.mem = u.mem ∧
    w.gpr .r5 = bm (vOf (t.mem (s.gpr .r3 + BitVec.ofNat 64 0)) (t.mem (s.gpr .r3 + BitVec.ofNat 64 1)) f sep) ∧
    w.gpr .r4 = bm (decide (R ^^^ BitVec.ofNat 64 1 = 0)) ∧
    w.gpr .r6 = (if vOf (t.mem (s.gpr .r3 + BitVec.ofNat 64 0)) (t.mem (s.gpr .r3 + BitVec.ofNat 64 1)) f sep then
        s.gpr .r7 - BitVec.ofNat 64 sep - BitVec.ofNat 64 1 else BitVec.ofNat 64 al) &&&
      bm (decide (R ^^^ BitVec.ofNat 64 1 = 0)) ∧
    w.gpr .r3 = s.gpr .r7 - (if vOf (t.mem (s.gpr .r3 + BitVec.ofNat 64 0)) (t.mem (s.gpr .r3 + BitVec.ofNat 64 1))
        f sep then s.gpr .r7 - BitVec.ofNat 64 sep - BitVec.ofNat 64 1 else BitVec.ofNat 64 al)) ?_ rfl)
    fun w ⟨⟨wm, w5, w4, w6, w3⟩, kw⟩ => ⟨⟨wm.trans um, by rw [kw.gpr _ (by decide), u11],
      by rw [kw.gpr _ (by decide), u7], w5, w4, w6, w3, by rw [kw.gpr _ (by decide), u12]⟩,
      (ku.mono (by decide)).trans' (kw.mono (by decide))⟩
  · unfold validRest
    prun [exec_lbz (show Reg.r11 ≠ .r0 by decide) c1' j1, u0, u3, u5, u6, u7, u8, u10, u11, u12, c3, j3, hr]
    simp only [read1_64, zero_mask64 _ (byte2_lt _), zero_mask64 _ hR, ten_mask hsep, bm_not, byte_two, um,
      vOf_bm, sel_xor]
    exact ⟨trivial, trivial, trivial, trivial⟩

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
