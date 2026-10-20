module
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Dsa.AArch64.TopMask
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.AArch64.Masks
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.Contract

/-! # Saving actual DSA widths and accumulating their top-bit checks -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev shapeP : List Instr :=
  ([sth .x8 22] : List Instr) ++ Checks.topMask ++ [.str .x .x3 .x0 Field.mask.offset]

abbrev shapeQ : List Instr :=
  ([.str .x .x8 .x0 Field.digestPrefixLen.offset] : List Instr) ++ Checks.topMask ++ Checks.accumulate

theorem shapeP_ok {s : State} {B : Addr} {Z width : Nat} {head : Byte}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 width) (h9 : s.gpr .x10 = head.zeroExtend 64) :
    WP isa (.block shapeP) s fun t =>
      t.mem = (s.mem.writeW (off B (8 * 22)) (BitVec.ofNat 64 width)).writeW
        (off B Field.mask.offset) (mask (decide (128 ≤ head.toNat))) ∧ Keep [.x3, .x4] s t := by
  refine WP.keep [.x3, .x4] ?_ rfl rfl rfl
  unfold shapeP Checks.topMask
  simp only [List.cons_append, List.nil_append]
  brun [hdr_enc (show 22 < 32 by decide), field_enc .mask, hdi, h8, h9,
    hs.st (show 8 * 22 + 8 ≤ Z by exact Nat.le_trans (by decide) hZ),
    hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ)]
  exact congrArg (fun x => (s.mem.writeW (off B (8 * 22)) (BitVec.ofNat 64 width)).writeW
    (off B Field.mask.offset) x) (byte_top_shift head)

theorem shapeQ_ok {s : State} {B : Addr} {Z width : Nat} {head : Byte} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 width) (h9 : s.gpr .x10 = head.zeroExtend 64)
    (hmask : word s.mem B Field.mask.offset = mask valid) :
    WP isa (.block shapeQ) s fun t =>
      t.mem = (s.mem.writeW (off B Field.digestPrefixLen.offset) (BitVec.ofNat 64 width)).writeW
        (off B Field.mask.offset) (mask (decide (128 ≤ head.toNat) && valid)) ∧ Keep [.x3, .x4] s t := by
  have he : word (s.mem.writeW (off B Field.digestPrefixLen.offset) (BitVec.ofNat 64 width)) B
      Field.mask.offset = mask valid :=
    ((writeW_outside s.mem B (BitVec.ofNat 64 width) (d := Field.digestPrefixLen.offset) (by decide)).word
      (Or.inr (by decide)) (by decide)).trans hmask
  refine WP.keep [.x3, .x4] ?_ rfl rfl rfl
  unfold shapeQ Checks.topMask Checks.accumulate Core.field
  simp only [List.cons_append, List.nil_append]
  brun [field_enc .mask, field_enc .digestPrefixLen, hdi, h8, h9, he,
    hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds .digestPrefixLen).2 hZ),
    hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ),
    hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ)]
  have hv := congrArg (fun x : BitVec 64 => x &&& mask valid) (byte_top_shift head)
  rw [mask_intersect] at hv
  exact congrArg (fun x => (s.mem.writeW (off B Field.digestPrefixLen.offset) (BitVec.ofNat 64 width)).writeW
    (off B Field.mask.offset) x) hv

end VG.Proof.Dsa.AArch64
