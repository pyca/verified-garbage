module
public import VerifiedGarbage.Impl.Dsa.AArch64.Core

import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! # Resolving the two signature output halves -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev scalarHead (offset : Nat) (second : Bool) : List Instr :=
  ([movi .x3 offset, .add .x .x1 .x0 .x3,
    Core.field .x2 .out, Core.field .x9 .qLen, Core.field .x8 .mask] : List Instr) ++
    (if second then [.add .x .x2 .x2 .x9] else [])

theorem scalarHead_ok {s : State} {B out : Addr} {Z offset q : Nat} {valid : Bool}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z) (ho : offset < 2 ^ 16)
    (hout : word s.mem B Field.out.offset = out) (hq : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q)
    (hm : word s.mem B Field.mask.offset = mask valid) (second : Bool) :
    WP isa (.block (scalarHead offset second)) s fun t =>
      t.gpr .x1 = off B offset ∧ t.gpr .x2 = (if second then out + BitVec.ofNat 64 q else out) ∧
      t.gpr .x9 = BitVec.ofNat 64 q ∧ t.gpr .x8 = mask valid ∧
      t.mem = s.mem ∧ Keep [.x3, .x1, .x2, .x9, .x8] s t := by
  have hoff : (BitVec.ofNat 16 offset).setWidth 64 = BitVec.ofNat 64 offset := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  unfold scalarHead
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x1, .x2, .x9, .x8] (Q := fun t =>
    t.gpr .x1 = off B offset ∧ t.gpr .x2 = out ∧ t.gpr .x9 = BitVec.ofNat 64 q ∧
    t.gpr .x8 = mask valid ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨h1, h2, h9, h8, hmem⟩, hk⟩ => ?_
  · brun [h0, hoff, Core.field, fieldAddress, field_enc .out, field_enc .qLen, field_enc .mask,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .out).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .qLen).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ), hout, hq, hm]
  cases second
  · exact WP.block_nil ⟨h1, h2, h9, h8, hmem, hk⟩
  · refine WP.mono (WP.keep [.x2] (Q := fun u => u.gpr .x2 = out + BitVec.ofNat 64 q ∧ u.mem = t.mem)
      (by brun [h2, h9]) rfl rfl rfl) fun u ⟨⟨hu2, hum⟩, hku⟩ => ?_
    exact ⟨(hku.gpr .x1 (by decide)).trans h1, hu2, (hku.gpr .x9 (by decide)).trans h9,
      (hku.gpr .x8 (by decide)).trans h8, hum.trans hmem, (hk.trans hku).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
