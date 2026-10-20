module

import VerifiedGarbage.Proof.Dsa.AArch64.ScanField
public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.WidthChoice
public import VerifiedGarbage.Proof.Dsa.DomainShape
import VerifiedGarbage.Proof.Framework.Block
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! # The two public width scans and supported-size selection -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev shapeSizes : Prog isa := seqs [
  .block [Core.field .x1 .p, Core.field .x9 .pLen],
  Checks.significant,
  .block (shapeP ++ ([Core.field .x1 .q, Core.field .x9 .qLen] : List Instr)),
  Checks.significant,
  .block (shapeQ ++ ([ldh .x2 22, .subImm .x .x6 .x2 128] : List Instr)),
  widthChoice]

theorem shapeSizes_ok {s : State} {B pp qp : Addr} {Z : Nat} {p q : List Byte}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (hpp : word s.mem B Field.p.offset = pp) (hqp : word s.mem B Field.q.offset = qp)
    (hpl : word s.mem B Field.pLen.offset = BitVec.ofNat 64 p.length)
    (hql : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q.length)
    (hps : Src s B Z pp p) (hqs : Src s B Z qp q)
    (hp1 : 0 < p.length) (hp64 : p.length < 2 ^ 64) (hq1 : 0 < q.length) (hq64 : q.length < 2 ^ 64) :
    WP isa shapeSizes s fun t =>
      t.gpr .x3 = mask (decide (Spec.Dsa.supportedSizes
        (8 * (VG.Proof.Dsa.significant p).1) (8 * (VG.Proof.Dsa.significant q).1))) ∧
      word t.mem B Field.mask.offset = mask (decide (128 ≤ (VG.Proof.Dsa.significant q).2.toNat) &&
        decide (128 ≤ (VG.Proof.Dsa.significant p).2.toNat)) ∧
      word t.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 (VG.Proof.Dsa.significant q).1 ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep mmRegs s t := by
  have pbound := Nat.lt_of_le_of_lt (VG.Proof.Dsa.significant_fits p) hp64
  have qbound := Nat.lt_of_le_of_lt (VG.Proof.Dsa.significant_fits q) hq64
  unfold shapeSizes seqs
  refine WP.seq (WP.mono (WP.seq_iff.mp (scanField_ok hs hdi hZ .p .pLen hpp hpl hps hp1 hp64))
    fun u hu => WP.seq (WP.mono hu fun v ⟨hv8, hv9, hvm, hkv⟩ => ?_))
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have hvdi := (hkv.gpr .x0 (show Reg.x0 ∉ [Reg.x3, Reg.x8, Reg.x10, Reg.x1, Reg.x9] by decide)).trans hdi
  refine WP.mono (shapeP_context (hs.congr hkv.wr) hvdi hZ hv8 hv9)
    fun x ⟨hxp, hxm, hfx, hkx⟩ => ?_
  have hksx := hkv.trans hkx
  have hxdi := (hksx.gpr .x0 (show Reg.x0 ∉ _ by decide)).trans hdi
  have hxqp : word x.mem B Field.q.offset = qp :=
    (shape_field hfx .q (by decide) (by decide)).trans (by rw [hvm]; exact hqp)
  have hxql : word x.mem B Field.qLen.offset = BitVec.ofNat 64 q.length :=
    (shape_field hfx .qLen (by decide) (by decide)).trans (by rw [hvm]; exact hql)
  have hxqs := shape_source hfx hkx (Nat.le_trans (by decide) hZ)
    (hqs.congrK (by rw [hvm]; exact InScr.refl _ _ _) hkv)
  refine WP.mono (WP.seq_iff.mp (scanField_ok (hs.congr hksx.wr) hxdi hZ .q .qLen hxqp hxql hxqs hq1 hq64))
    fun y hy => WP.seq (WP.mono hy fun z ⟨hz8, hz9, hzm, hkz⟩ => ?_)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have hksz := hksx.trans hkz
  have hzdi := (hksz.gpr .x0 (show Reg.x0 ∉ _ by decide)).trans hdi
  refine WP.mono (shapeQ_context (valid := decide (128 ≤ (VG.Proof.Dsa.significant p).2.toNat))
    (hs.congr hksz.wr) hzdi hZ hz8 hz9 (by rw [hzm]; exact hxm))
    fun a ⟨haq, ham, hap, hfa, hka⟩ => ?_
  have hksa := hksz.trans hka
  have hadi := (hksa.gpr .x0 (show Reg.x0 ∉ _ by decide)).trans hdi
  have haw : word a.mem B 176 = BitVec.ofNat 64 (VG.Proof.Dsa.significant p).1 :=
    hap.trans (by rw [hzm]; exact hxp)
  refine WP.mono (readWidth_ok (hs.congr hksa.wr) hadi (Nat.le_trans (by decide) hZ) pbound haw)
    fun b ⟨hbz, hbd, hbm, hkb⟩ => ?_
  have hb8 := ((hka.trans hkb).gpr .x8 (show Reg.x8 ∉ _ by decide)).trans hz8
  refine WP.mono (widthChoice_ok pbound qbound hbd hb8 hbz) fun t ⟨ht, htm, hkt⟩ => ?_
  refine ⟨ht, by rw [htm, hbm]; exact ham, by rw [htm, hbm]; exact haq, ?_,
    ((hksa.trans hkb).trans hkt).mono (by decide)⟩
  rw [htm, hbm]
  have hfs : Frm B shapeRanges s.mem z.mem := by rw [hzm, ← hvm]; exact hfx
  exact hfs.trans hfa

end VG.Proof.Dsa.AArch64
