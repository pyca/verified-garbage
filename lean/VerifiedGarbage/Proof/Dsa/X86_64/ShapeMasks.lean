module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Dsa.X86_64.TopMask
import VerifiedGarbage.Proof.Dsa.Layout
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul

/-! # Saving actual DSA widths and accumulating their top-bit checks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev shapeP : List Instr := [.store (hdr 22) .r8, .alu .cmp .r9 (.imm 128), .alu .sbb .rax (.reg .rax),
  .alu .xor .rax (.imm (-1)), .store (Core.field .mask) .rax]

abbrev shapeQ : List Instr :=
  ([.store (Core.field .digestPrefixLen) .r8, .alu .cmp .r9 (.imm 128),
    .alu .sbb .rax (.reg .rax), .alu .xor .rax (.imm (-1))] : List Instr) ++ Checks.accumulate

theorem shapeP_ok {s : State} {B : Addr} {Z width : Nat} {head : Byte}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 width) (h9 : s.gpr .r9 = head.zeroExtend 64) :
    WP isa (.block shapeP) s fun t =>
      t.mem = (s.mem.writeW (off B (8 * 22)) (BitVec.ofNat 64 width)).writeW
        (off B Field.mask.offset) (mask (decide (128 ≤ head.toNat))) ∧ Keep [.rax, .r9] s t := by
  refine WP.keep [.rax, .r9] ?_ rfl
  unfold shapeP Core.field
  xrun [State.ea, hdr, hdrOff, fieldAddress, hdi, h8, h9,
    hs.st (show 8 * 22 + 8 ≤ Z by exact Nat.le_trans (by decide) hZ),
    hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ),
    show BitVec.signExtend 64 (128 : BitVec 32) = 128#64 from rfl,
    show BitVec.signExtend 64 (-1 : BitVec 32) = BitVec.allOnes 64 from rfl]
  exact congrArg (fun x => (s.mem.writeW (off B (8 * 22)) (BitVec.ofNat 64 width)).writeW
    (off B Field.mask.offset) x) (byte_top_mask head)

theorem shapeQ_ok {s : State} {B : Addr} {Z width : Nat} {head : Byte} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 width) (h9 : s.gpr .r9 = head.zeroExtend 64)
    (hmask : word s.mem B Field.mask.offset = mask valid) :
    WP isa (.block shapeQ) s fun t =>
      t.mem = (s.mem.writeW (off B Field.digestPrefixLen.offset) (BitVec.ofNat 64 width)).writeW
        (off B Field.mask.offset) (mask (decide (128 ≤ head.toNat) && valid)) ∧ Keep [.rax, .r9] s t := by
  have he : word (s.mem.writeW (off B Field.digestPrefixLen.offset) (BitVec.ofNat 64 width)) B
      Field.mask.offset = mask valid :=
    ((writeW_outside s.mem B (BitVec.ofNat 64 width) (d := Field.digestPrefixLen.offset) (by decide)).word
      (Or.inr (by decide)) (by decide)).trans hmask
  refine WP.keep [.rax, .r9] ?_ rfl
  unfold shapeQ Checks.accumulate Core.field
  simp only [List.cons_append, List.nil_append]
  xrun [State.ea, fieldAddress, hdi, h8, h9, he,
    hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds .digestPrefixLen).2 hZ),
    hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ),
    hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ),
    show BitVec.signExtend 64 (128 : BitVec 32) = 128#64 from rfl,
    show BitVec.signExtend 64 (-1 : BitVec 32) = BitVec.allOnes 64 from rfl]
  have hv := congrArg (fun x : BitVec 64 => x &&& mask valid) (byte_top_mask head)
  rw [mask_intersect] at hv
  exact congrArg (fun x => (s.mem.writeW (off B Field.digestPrefixLen.offset) (BitVec.ofNat 64 width)).writeW
    (off B Field.mask.offset) x) hv

end VG.Proof.Dsa.X86_64
