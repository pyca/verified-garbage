module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Scan
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Select
public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: the validity of the padding

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecSel.lean`): the validity of the padding, the
selected length and the mask of the private-key operation's success
(`validBlock_ok`), from the registers the scan left.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (mov)
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

/-- The block's results, from the registers the scan left. -/
theorem validBlock_ok {s : State} {R : BitVec 64} {EM : List Byte} {t : State} (hp : Post s R EM t)
    (h0 : InRegions (t.rd ++ t.wr) (s.gpr .a0) 1)
    (h1 : InRegions (t.rd ++ t.wr) (s.gpr .a0 + BitVec.ofNat 64 1) 1)
    {f : Bool} {sep al : Nat} (h4 : t.gpr .a4 = bm f) (h5 : t.gpr .a5 = BitVec.ofNat 64 sep)
    (h6 : t.gpr .t6 = BitVec.ofNat 64 al) (ha6 : t.gpr .a6 = 0) (ha7 : t.gpr .a7 = BitVec.allOnes 64)
    (hsep : sep < 2 ^ 63) (hR : (R ^^^ BitVec.ofNat 64 1).toNat < 2 ^ 63) :
    WP isa (.block validBlock) t fun u => Only [.t1, .t2, .a0, .a1, .a3, .a4, .a5, .t6] t u ∧
      u.gpr .t1 = s.gpr .a0 ∧ u.gpr .t2 = s.gpr .a4 ∧
      u.gpr .a4 = bm (vOf (t.mem (s.gpr .a0)) (t.mem (s.gpr .a0 + BitVec.ofNat 64 1)) f sep) ∧
      u.gpr .a3 = bm (decide (R ^^^ BitVec.ofNat 64 1 = 0)) ∧
      u.gpr .t6 = (if vOf (t.mem (s.gpr .a0)) (t.mem (s.gpr .a0 + BitVec.ofNat 64 1)) f sep then
          s.gpr .a4 - BitVec.ofNat 64 sep - BitVec.ofNat 64 1 else BitVec.ofNat 64 al) &&&
        bm (decide (R ^^^ BitVec.ofNat 64 1 = 0)) ∧
      u.gpr .a5 = s.gpr .a4 - (if vOf (t.mem (s.gpr .a0)) (t.mem (s.gpr .a0 + BitVec.ofNat 64 1))
          f sep then s.gpr .a4 - BitVec.ofNat 64 sep - BitVec.ofNat 64 1 else BitVec.ofNat 64 al) := by
  unfold validBlock
  mrun [mov, hp.s2, hp.s1, hp.r, h0, h1, h4, h5, h6, ha6, ha7]
  refine ⟨⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, ?_⟩
  · obtain ⟨a, b, c, d, e, f, g, i⟩ : r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .a5 ∧
        r ≠ .t6 := by simpa using hr
    simp only [a, b, c, d, e, f, g, i, ite_false]
  simp only [zero_mask64 _ (byte_lt _), zero_mask64 _ (byte2_lt _), zero_mask64 _ hR, ten_mask hsep, bm_not,
    byte_two, byte_zero, vOf_bm, sel_xor]
  exact ⟨trivial, trivial, trivial, trivial⟩

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec
