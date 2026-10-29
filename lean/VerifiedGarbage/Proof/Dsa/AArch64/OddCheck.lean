module

public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import Aesop.BuiltinRules

import VerifiedGarbage.Proof.Dsa.AArch64.LastByte
import VerifiedGarbage.Proof.Dsa.AArch64.Masks
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
/-! # Public oddness checks on the encoded DSA moduli -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Parity.lean`, which only this module imported.
section

/-! # The shared oddness mask for DSA moduli -/

section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64
open VG.Proof.Bignum

theorem word_low_bit (x : BitVec 64) : x &&& 1 = BitVec.ofNat 64 (x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x.toNat % 2 < 2 ^ 64 by omega)]

theorem word_odd_mask (x : BitVec 64) : 0 - (x &&& 1) = mask (decide (x.toNat % 2 = 1)) := by
  rw [word_low_bit]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

/-- The implementation combines low bits before converting the result to a mask. -/
theorem modulus_odd_mask (p q : Byte) :
    0 - (p.zeroExtend 64 &&& q.zeroExtend 64 &&& 1) =
      mask (decide (p.toNat % 2 = 1 ∧ q.toNat % 2 = 1)) := by
  rw [word_odd_mask, BitVec.toNat_and]
  change mask (decide (((p.setWidth 64).toNat &&& (q.setWidth 64).toNat) % 2 = 1)) = _
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans p.isLt (show 2 ^ 8 < 2 ^ 64 by decide)),
    Nat.mod_eq_of_lt (Nat.lt_trans q.isLt (show 2 ^ 8 < 2 ^ 64 by decide))]
  exact congrArg mask (decide_eq_decide.mpr Nat.and_mod_two_eq_one)

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev oddCombine : List Instr :=
  [.logic .and .x .x3 .x3 .x2, movi .x2 1, .logic .and .x .x3 .x3 .x2,
    movi .x2 0, .sub .x .x3 .x2 .x3]

theorem oddCombine_ok {s : State} {p q : Byte}
    (ha : s.gpr .x3 = p.zeroExtend 64) (hd : s.gpr .x2 = q.zeroExtend 64) :
    WP isa (.block oddCombine) s fun t =>
      t.gpr .x3 = mask (decide (p.toNat % 2 = 1 ∧ q.toNat % 2 = 1)) ∧
      t.mem = s.mem ∧ Keep [.x3, .x2] s t := by
  refine WP.mono (WP.keep [.x3, .x2] (Q := fun t =>
    t.gpr .x3 = mask (decide (p.toNat % 2 = 1 ∧ q.toNat % 2 = 1)) ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨ht, hm⟩, hk⟩ => ⟨ht, hm, hk⟩
  unfold oddCombine
  brun [ha, hd]
  exact modulus_odd_mask p q

abbrev oddCheck : List Instr :=
  ([Core.field .x1 .p, Core.field .x9 .pLen, .subImm .x .x9 .x9 1,
    .add .x .x1 .x1 .x9, .ldrb .x3 .x1 0] : List Instr) ++
  ([Core.field .x1 .q, Core.field .x9 .qLen, .subImm .x .x9 .x9 1,
    .add .x .x1 .x1 .x9, .ldrb .x2 .x1 0] : List Instr) ++ oddCombine ++ Checks.accumulate

theorem oddCheck_ok {s : State} {B pp qp : Addr} {Z pl ql : Nat} {pLast qLast : Byte} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (hpp : word s.mem B Field.p.offset = pp) (hqp : word s.mem B Field.q.offset = qp)
    (hpl : word s.mem B Field.pLen.offset = BitVec.ofNat 64 pl)
    (hql : word s.mem B Field.qLen.offset = BitVec.ofNat 64 ql)
    (hp1 : 1 ≤ pl) (hp64 : pl < 2 ^ 64) (hq1 : 1 ≤ ql) (hq64 : ql < 2 ^ 64)
    (hpr : InRegions (s.rd ++ s.wr) (pp + BitVec.ofNat 64 (pl - 1)) 1)
    (hqr : InRegions (s.rd ++ s.wr) (qp + BitVec.ofNat 64 (ql - 1)) 1)
    (hpv : s.mem (pp + BitVec.ofNat 64 (pl - 1)) = pLast)
    (hqv : s.mem (qp + BitVec.ofNat 64 (ql - 1)) = qLast)
    (hm : word s.mem B Field.mask.offset = mask valid) :
    WP isa (.block oddCheck) s fun t =>
      word t.mem B Field.mask.offset = mask (decide (pLast.toNat % 2 = 1 ∧ qLast.toNat % 2 = 1) && valid) ∧
      Outside B Field.mask.offset 8 s.mem t.mem ∧ Keep [.x3, .x4, .x2, .x1, .x9] s t := by
  unfold oddCheck
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (lastByte_ok hs hdi hZ .p .pLen .x3 hpp hpl hp1 hp64 hpr hpv)
    fun u ⟨hua, hum, hku⟩ => ?_
  rw [WP.block_append_iff]
  have hudi := (hku.gpr .x0 (show Reg.x0 ∉ _ by decide)).trans hdi
  refine WP.mono (lastByte_ok (p := qp) (b := qLast) (hs.congr hku.wr) hudi hZ .q .qLen .x2
    (by rw [hum]; exact hqp) (by rw [hum]; exact hql) hq1 hq64
    (by rw [hku.rd, hku.wr]; exact hqr) (by rw [hum]; exact hqv))
    fun v ⟨hvd, hvm, hkv⟩ => ?_
  rw [WP.block_append_iff]
  have hva := (hkv.gpr .x3 (show Reg.x3 ∉ _ by decide)).trans hua
  refine WP.mono (oddCombine_ok hva hvd) fun z ⟨hza, hzm, hkz⟩ => ?_
  have hks := (hku.trans hkv).trans hkz
  have hzs := hs.congr hks.wr
  have hzdi := (hks.gpr .x0 (show Reg.x0 ∉ _ by decide)).trans hdi
  refine WP.mono (accumulate_ok (b := valid) hzs hzdi hZ hza (by rw [hzm, hvm, hum]; exact hm))
    fun t ⟨ht, hf, hk⟩ => ?_
  exact ⟨ht, by rw [← hum, ← hvm, ← hzm]; exact hf, (hks.trans hk).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
