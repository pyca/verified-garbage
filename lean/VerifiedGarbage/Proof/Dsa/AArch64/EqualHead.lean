module

public import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Resolving both operands of a DSA equality check -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem equalHead_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (a b : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) :
    WP isa (.block (Core.pointer a.pointer ++ ([mov .x1 .x3] : List Instr) ++
      Core.pointer b.pointer ++ ([mov .x2 .x3, Core.field .x9 a.length, movi .x8 0] : List Instr))) s fun t =>
      t.gpr .x1 = pointerValue s.mem B a.pointer ∧ t.gpr .x2 = pointerValue s.mem B b.pointer ∧
      t.gpr .x9 = word s.mem B a.length.offset ∧ t.gpr .x8 = 0 ∧ t.mem = s.mem ∧
      Keep [.x3, .x4, .x1, .x2, .x9, .x8] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (pointer_ok hs hdi hZ a.pointer ha) fun u ⟨hua, hum, hku⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x1] (Q := fun v => v.gpr .x1 = pointerValue s.mem B a.pointer ∧ v.mem = u.mem)
    (by brun [hua]) rfl rfl rfl) fun v ⟨⟨hvsi, hvm⟩, hkv⟩ => ?_
  have hks := hku.trans hkv
  rw [WP.block_append_iff]
  refine WP.mono (pointer_ok (hs.congr hks.wr) ((hks.gpr .x0 (by decide)).trans hdi) hZ b.pointer hb)
    fun z ⟨hza, hzm, hkz⟩ => ?_
  rw [hvm, hum] at hza
  have hzsi := (hkz.gpr .x1 (show Reg.x1 ∉ [Reg.x3, Reg.x4] by decide)).trans hvsi
  have hksz := hks.trans hkz
  have hzdi := (hksz.gpr .x0 (show Reg.x0 ∉ _ by decide)).trans hdi
  have hzlen : word z.mem B a.length.offset = word s.mem B a.length.offset := by rw [hzm, hvm, hum]
  refine WP.mono (WP.keep [.x2, .x9, .x8] (Q := fun t =>
    t.gpr .x2 = pointerValue s.mem B b.pointer ∧ t.gpr .x9 = word s.mem B a.length.offset ∧
    t.gpr .x8 = 0 ∧ t.mem = z.mem) ?_ rfl rfl rfl) fun t ⟨⟨htd, htc, ht8, htm⟩, hkt⟩ =>
      ⟨(hkt.gpr .x1 (by decide)).trans hzsi, htd, htc, ht8, htm.trans (hzm.trans (hvm.trans hum)),
        (hksz.trans hkt).mono (by decide)⟩
  brun [hza, Core.field, hzdi, field_enc a.length, hzlen,
    (hs.congr hksz.wr).ld (Nat.le_trans (VG.Proof.Dsa.field_bounds a.length).2 hZ)]

end VG.Proof.Dsa.AArch64
