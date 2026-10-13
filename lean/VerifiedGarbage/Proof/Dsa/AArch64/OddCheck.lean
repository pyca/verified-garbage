module

public import VerifiedGarbage.Proof.Dsa.AArch64.LastByte
public import VerifiedGarbage.Proof.Dsa.AArch64.Parity
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Public oddness checks on the encoded DSA moduli -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev oddCombine : List Instr := [.logic .and .x .x3 .x3 .x4, movi .x4 1, .logic .and .x .x3 .x3 .x4,
  movi .x7 0, .sub .x .x15 .x7 .x3]

theorem oddCombine_ok {s : State} {p q : Byte}
    (ha : s.gpr .x3 = p.zeroExtend 64) (hd : s.gpr .x4 = q.zeroExtend 64) :
    WP isa (.block oddCombine) s fun t =>
      t.gpr .x15 = mask (decide (p.toNat % 2 = 1 ∧ q.toNat % 2 = 1)) ∧
      t.mem = s.mem ∧ Keep [.x3, .x4, .x7, .x15] s t := by
  refine WP.mono (WP.keep [.x3, .x4, .x7, .x15] (Q := fun t =>
    t.gpr .x15 = mask (decide (p.toNat % 2 = 1 ∧ q.toNat % 2 = 1)) ∧ t.mem = s.mem) ?_
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨ht, hm⟩, hk⟩ => ⟨ht, hm, hk⟩
  unfold oddCombine
  brun [ha, hd, show BitVec.setWidth 64 (1#16) = 1#64 from rfl,
    show BitVec.setWidth 64 (0#16) = 0#64 from rfl]
  exact modulus_odd_mask p q

abbrev oddCheck : List Instr :=
  ([Core.field .x1 .p, Core.field .x2 .pLen, .add .x .x1 .x1 .x2, .subImm .x .x1 .x1 1,
    .ldrb .x3 .x1 0] : List Instr) ++
  ([Core.field .x1 .q, Core.field .x2 .qLen, .add .x .x1 .x1 .x2, .subImm .x .x1 .x1 1,
    .ldrb .x4 .x1 0] : List Instr) ++
  oddCombine ++ Checks.accumulate

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
      Outside B Field.mask.offset 8 s.mem t.mem ∧ Keep [.x1, .x2, .x3, .x4, .x7, .x15] s t := by
  unfold oddCheck
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (lastByte_ok hs hdi hZ .p .pLen .x3 hpp hpl hp1 hp64 hpr hpv)
    fun u ⟨hua, hum, hku⟩ => ?_
  rw [WP.block_append_iff]
  have hudi := (hku.gpr .x0 (by decide)).trans hdi
  refine WP.mono (lastByte_ok (p := qp) (b := qLast) (hs.congr hku.wr) hudi hZ .q .qLen .x4
    (by rw [hum]; exact hqp) (by rw [hum]; exact hql) hq1 hq64
    (by rw [hku.rd, hku.wr]; exact hqr) (by rw [hum]; exact hqv))
    fun v ⟨hvd, hvm, hkv⟩ => ?_
  rw [WP.block_append_iff]
  have hva := (hkv.gpr .x3 (by decide)).trans hua
  refine WP.mono (oddCombine_ok hva hvd) fun z ⟨hza, hzm, hkz⟩ => ?_
  have hks := (hku.trans hkv).trans hkz
  have hzs := hs.congr hks.wr
  have hzdi := (hks.gpr .x0 (by decide)).trans hdi
  refine WP.mono (accumulate_ok (b := valid) hzs hzdi hZ hza (by rw [hzm, hvm, hum]; exact hm))
    fun t ⟨ht, hf, hk⟩ => ?_
  exact ⟨ht, by rw [← hum, ← hvm, ← hzm]; exact hf, (hks.trans hk).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
