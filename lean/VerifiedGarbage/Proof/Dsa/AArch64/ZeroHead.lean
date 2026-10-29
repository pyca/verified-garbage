module

public import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract

/-! # Resolving the operand of a DSA zero check -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem zeroHead_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (a : Operand) (ha : pointerFits a.pointer) :
    WP isa (.block (Core.pointer a.pointer ++ ([mov .x1 .x3, Core.field .x9 a.length, movi .x8 0] : List Instr))) s fun t =>
      t.gpr .x1 = pointerValue s.mem B a.pointer ∧ t.gpr .x9 = word s.mem B a.length.offset ∧
      t.gpr .x8 = 0 ∧ t.mem = s.mem ∧ Keep [.x3, .x4, .x1, .x9, .x8] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (pointer_ok hs hdi hZ a.pointer ha) fun u ⟨hua, hum, hku⟩ => ?_
  have hudi := (hku.gpr .x0 (show Reg.x0 ∉ [Reg.x3, Reg.x4] by decide)).trans hdi
  have hul : word u.mem B a.length.offset = word s.mem B a.length.offset := by rw [hum]
  have hus := hs.congr hku.wr
  refine WP.mono (WP.keep [.x1, .x9, .x8] (Q := fun v =>
    v.gpr .x1 = pointerValue s.mem B a.pointer ∧ v.gpr .x9 = word s.mem B a.length.offset ∧
    v.gpr .x8 = 0 ∧ v.mem = u.mem) ?_ rfl rfl rfl) fun v ⟨⟨hvp, hvn, hv8, hvm⟩, hkv⟩ =>
      ⟨hvp, hvn, hv8, hvm.trans hum, (hku.trans hkv).mono (by decide)⟩
  brun [hua, Core.field, hudi, field_enc a.length, hul,
    hus.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds a.length).2 hZ)]

end VG.Proof.Dsa.AArch64
