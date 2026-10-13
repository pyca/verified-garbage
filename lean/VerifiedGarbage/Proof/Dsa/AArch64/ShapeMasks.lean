module

public import VerifiedGarbage.Proof.Dsa.AArch64.TopMask
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Saving actual DSA widths and accumulating their top-bit checks -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev shapeP : List Instr := ([sth .x8 22, mov .x3 .x9] : List Instr) ++ Checks.atLeast 128 ++
  ([.str .x .x15 .x0 Field.mask.offset] : List Instr)

abbrev shapeQ : List Instr :=
  ([.str .x .x8 .x0 Field.digestPrefixLen.offset, mov .x3 .x9] : List Instr) ++ Checks.atLeast 128 ++
    Checks.accumulate

theorem shapeP_ok {s : State} {B : Addr} {Z width : Nat} {head : Byte}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 width) (h9 : s.gpr .x9 = head.zeroExtend 64) :
    WP isa (.block shapeP) s fun t =>
      t.mem = (s.mem.writeW (off B (8 * 22)) (BitVec.ofNat 64 width)).writeW
        (off B Field.mask.offset) (mask (decide (128 ≤ head.toNat))) ∧ Keep [.x3, .x4, .x7, .x15] s t := by
  unfold shapeP
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (Q := fun u =>
    u.mem = s.mem.writeW (off B (8 * 22)) (BitVec.ofNat 64 width) ∧ u.gpr .x3 = head.zeroExtend 64)
    ?_ (by decide) (by decide) (by decide +kernel)) fun u ⟨⟨hum, hu3⟩, hku⟩ => ?_
  · brun [hdi, h8, h9, hdr_enc (show 22 < 32 by decide),
      hs.st (show 8 * 22 + 8 ≤ Z by exact Nat.le_trans (by decide) hZ), BitVec.add_zero]
  rw [WP.block_append_iff]
  refine WP.mono (topMask_ok hu3) fun v ⟨hv15, hvm, hkv⟩ => ?_
  have hvdi := ((hku.trans hkv).gpr .x0 (by decide)).trans hdi
  have hvs := hs.congr (hku.trans hkv).wr
  refine WP.mono (WP.keep [] (Q := fun t =>
    t.mem = v.mem.writeW (off B Field.mask.offset) (mask (decide (128 ≤ head.toNat)))) ?_
    (by decide) (by decide) (by decide +kernel)) fun t ⟨htm, hkt⟩ =>
      ⟨by rw [htm, hvm, hum], ((hku.trans hkv).trans hkt).mono (by decide)⟩
  brun [hvdi, hv15, field_enc, hvs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ)]

theorem shapeQ_ok {s : State} {B : Addr} {Z width : Nat} {head : Byte} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 width) (h9 : s.gpr .x9 = head.zeroExtend 64)
    (hmask : word s.mem B Field.mask.offset = mask valid) :
    WP isa (.block shapeQ) s fun t =>
      t.mem = (s.mem.writeW (off B Field.digestPrefixLen.offset) (BitVec.ofNat 64 width)).writeW
        (off B Field.mask.offset) (mask (decide (128 ≤ head.toNat) && valid)) ∧
        Keep [.x3, .x4, .x7, .x15] s t := by
  have he : (s.mem.writeW (off B Field.digestPrefixLen.offset) (BitVec.ofNat 64 width)).readW
      (off B Field.mask.offset) 64 = mask valid :=
    ((writeW_outside s.mem B (BitVec.ofNat 64 width) (d := Field.digestPrefixLen.offset) (by decide)).word
      (Or.inr (by decide)) (by decide)).trans hmask
  unfold shapeQ
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (Q := fun u =>
    u.mem = s.mem.writeW (off B Field.digestPrefixLen.offset) (BitVec.ofNat 64 width) ∧
      u.gpr .x3 = head.zeroExtend 64)
    ?_ (by decide) (by decide) (by decide +kernel)) fun u ⟨⟨hum, hu3⟩, hku⟩ => ?_
  · brun [hdi, h8, h9, field_enc,
      hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds .digestPrefixLen).2 hZ), BitVec.add_zero]
  rw [WP.block_append_iff]
  refine WP.mono (topMask_ok hu3) fun v ⟨hv15, hvm, hkv⟩ => ?_
  have hvdi := ((hku.trans hkv).gpr .x0 (by decide)).trans hdi
  have hvs := hs.congr (hku.trans hkv).wr
  rw [hum] at hvm
  refine WP.mono (WP.keep [.x3, .x15] (Q := fun t =>
    t.mem = (s.mem.writeW (off B Field.digestPrefixLen.offset) (BitVec.ofNat 64 width)).writeW
      (off B Field.mask.offset) (mask (decide (128 ≤ head.toNat) && valid))) ?_
    (by decide) (by decide) (by decide +kernel)) fun t ⟨htm, hkt⟩ =>
      ⟨htm, ((hku.trans hkv).trans hkt).mono (by decide)⟩
  unfold Checks.accumulate Core.field
  brun [hvdi, hv15, hvm, he, field_enc, hvs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ),
    hvs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ), mask_intersect]

end VG.Proof.Dsa.AArch64
