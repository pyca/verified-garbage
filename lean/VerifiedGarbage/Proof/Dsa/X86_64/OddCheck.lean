module

public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import Aesop.BuiltinRules

import VerifiedGarbage.Proof.Dsa.X86_64.LastByte
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.TCB.X86_64.State
/-! # Public oddness checks on the encoded DSA moduli -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Parity.lean`, which only this module imported.
section

/-! # The shared oddness mask for DSA moduli -/

section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64
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

end VG.Proof.Dsa.X86_64
end

end

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev oddCombine : List Instr := [.alu .and .rax (.reg .rdx), .alu .and .rax (.imm 1),
  .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax), .mov .rax (.reg .rdx)]

theorem oddCombine_ok {s : State} {p q : Byte}
    (ha : s.gpr .rax = p.zeroExtend 64) (hd : s.gpr .rdx = q.zeroExtend 64) :
    WP isa (.block oddCombine) s fun t =>
      t.gpr .rax = mask (decide (p.toNat % 2 = 1 ∧ q.toNat % 2 = 1)) ∧
      t.mem = s.mem ∧ Keep [.rax, .rdx] s t := by
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
    t.gpr .rax = mask (decide (p.toNat % 2 = 1 ∧ q.toNat % 2 = 1)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨ht, hm⟩, hk⟩ => ⟨ht, hm, hk⟩
  unfold oddCombine
  xrun [ha, hd, show BitVec.signExtend 64 (1 : BitVec 32) = 1#64 from rfl]
  exact modulus_odd_mask p q

abbrev oddCheck : List Instr :=
  ([.mov .rsi (.mem (Core.field .p)), .mov .rcx (.mem (Core.field .pLen)),
    .movzx8 .rax { base := .rsi, index := some .rcx, disp := -1 }] : List Instr) ++
  ([.mov .rsi (.mem (Core.field .q)), .mov .rcx (.mem (Core.field .qLen)),
    .movzx8 .rdx { base := .rsi, index := some .rcx, disp := -1 }] : List Instr) ++
  oddCombine ++ Checks.accumulate

theorem oddCheck_ok {s : State} {B pp qp : Addr} {Z pl ql : Nat} {pLast qLast : Byte} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
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
      Outside B Field.mask.offset 8 s.mem t.mem ∧ Keep [.rax, .rdx, .rsi, .rcx] s t := by
  unfold oddCheck
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (lastByte_ok hs hdi hZ .p .pLen .rax hpp hpl hp1 hp64 hpr hpv)
    fun u ⟨hua, hum, hku⟩ => ?_
  rw [WP.block_append_iff]
  have hudi := (hku.gpr (show Reg.rdi ∉ _ by decide)).trans hdi
  refine WP.mono (lastByte_ok (p := qp) (b := qLast) (hs.congr hku.2.2) hudi hZ .q .qLen .rdx
    (by rw [hum]; exact hqp) (by rw [hum]; exact hql) hq1 hq64
    (by rw [hku.2.1, hku.2.2]; exact hqr) (by rw [hum]; exact hqv))
    fun v ⟨hvd, hvm, hkv⟩ => ?_
  rw [WP.block_append_iff]
  have hva := (hkv.gpr (show Reg.rax ∉ _ by decide)).trans hua
  refine WP.mono (oddCombine_ok hva hvd) fun z ⟨hza, hzm, hkz⟩ => ?_
  have hks := (hku.trans hkv).trans hkz
  have hzs := hs.congr hks.2.2
  have hzdi := (hks.gpr (show Reg.rdi ∉ _ by decide)).trans hdi
  refine WP.mono (accumulate_ok (b := valid) hzs hzdi hZ hza (by rw [hzm, hvm, hum]; exact hm))
    fun t ⟨ht, hf, hk⟩ => ?_
  exact ⟨ht, by rw [← hum, ← hvm, ← hzm]; exact hf, (hks.trans hk).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
