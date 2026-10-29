module

public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import Aesop.BuiltinRules

import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
/-! # Memory changed by the public DSA domain-shape check -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/TopMask.lean`, which only this module imported.
section

/-! # Testing byte-aligned modulus bit lengths -/

section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem byte_top_mask (b : Byte) :
    (0#64 - (BitVec.ofBool (decide ((b.zeroExtend 64).toNat < 128))).setWidth 64) ^^^ BitVec.allOnes 64 =
      mask (decide (128 ≤ b.toNat)) := by
  change mask (decide ((b.setWidth 64).toNat < 128)) ^^^ BitVec.allOnes 64 = _
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (show 2 ^ 8 < 2 ^ 64 by decide)),
    mask_complement, ← decide_not]
  exact congrArg mask (decide_eq_decide.mpr (by omega))

/-- The first significant byte must have its high bit set for an exact
byte-aligned DSA bit length. -/
theorem topMask_ok {s : State} {b : Byte} (h9 : s.gpr .r9 = b.zeroExtend 64) :
    WP isa (.block [.alu .cmp .r9 (.imm 128), .alu .sbb .rax (.reg .rax), .alu .xor .rax (.imm (-1))]) s fun t =>
      t.gpr .rax = mask (decide (128 ≤ b.toNat)) ∧ t.mem = s.mem ∧ Keep [.rax, .r9] s t := by
  refine WP.mono (WP.keep [.rax, .r9] (Q := fun t =>
    t.gpr .rax = mask (decide (128 ≤ b.toNat)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨ht, hm⟩, hk⟩ => ⟨ht, hm, hk⟩
  xrun [h9, show BitVec.signExtend 64 (128 : BitVec 32) = 128#64 from rfl,
    show BitVec.signExtend 64 (-1 : BitVec 32) = BitVec.allOnes 64 from rfl]
  exact byte_top_mask b

end VG.Proof.Dsa.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/ShapeMasks.lean`, which only this module imported.
section

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
end

end

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def shapeRanges : List (Nat × Nat) := [(176, 8), (352, 16)]

theorem shape_field_sep (f : Field) (h1 : f ≠ .digestPrefixLen) (h2 : f ≠ .mask) :
    (f.offset + 8 ≤ 176 ∨ 184 ≤ f.offset) ∧ (f.offset + 8 ≤ 352 ∨ 368 ≤ f.offset) := by
  cases f <;> simp_all [Field.offset]

theorem shape_field {mem mem' : Mem} {B : Addr} (hf : Frm B shapeRanges mem mem')
    (f : Field) (h1 : f ≠ .digestPrefixLen) (h2 : f ≠ .mask) :
    word mem' B f.offset = word mem B f.offset := by
  have hs := shape_field_sep f h1 h2
  apply hf.word_eq _ (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))
  intro r hr
  simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.1
  · exact hs.2

theorem shape_source {s t : State} {B p : Addr} {Z : Nat} {bytes : List Byte} {rs : List Reg}
    (hf : Frm B shapeRanges s.mem t.mem) (hk : Keep rs s t) (hZ : 368 ≤ Z)
    (hs : Src s B Z p bytes) : Src t B Z p bytes := by
  apply hs.congrK _ hk
  apply InScr.of_frm hf
  intro r hr
  simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> omega

theorem shape_outside {mem mem' : Mem} {B : Addr} {d : Nat}
    (hf : Outside B d 8 mem mem') (hd : d = 176 ∨ d = 352 ∨ d = 360) :
    Frm B shapeRanges mem mem' := by
  intro x hx
  apply hf x
  have hfirst := hx (176, 8) (by simp [shapeRanges])
  have hsecond := hx (352, 16) (by simp [shapeRanges])
  rcases hd with rfl | rfl | rfl <;> omega

/-- Either of the check's word stores lies in the same small mutation frame. -/
theorem shape_store {mem : Mem} {B : Addr} {d : Nat} (v : BitVec 64)
    (hd : d = 176 ∨ d = 352 ∨ d = 360) : Frm B shapeRanges mem (mem.writeW (off B d) v) := by
  intro x hx
  apply writeW_outside mem B v (by rcases hd with rfl | rfl | rfl <;> decide) x
  have hfirst := hx (176, 8) (by simp [shapeRanges])
  have hsecond := hx (352, 16) (by simp [shapeRanges])
  rcases hd with rfl | rfl | rfl <;> omega

theorem shapeP_context {s : State} {B : Addr} {Z width : Nat} {head : Byte}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 width) (h9 : s.gpr .r9 = head.zeroExtend 64) :
    WP isa (.block shapeP) s fun t =>
      word t.mem B 176 = BitVec.ofNat 64 width ∧ word t.mem B Field.mask.offset = mask (decide (128 ≤ head.toNat)) ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep [.rax, .r9] s t := by
  refine WP.mono (shapeP_ok hs hdi hZ h8 h9) fun t ⟨htm, hk⟩ => ?_
  refine ⟨?_, ?_, ?_, hk⟩
  · rw [htm, (writeW_outside _ B _ (d := Field.mask.offset) (by decide)).word (Or.inl (by decide)) (by decide)]
    exact word_writeW_self _ _ _ _
  · rw [htm, word_writeW_self]
  · rw [htm]
    exact (shape_store _ (Or.inl rfl)).trans (shape_store _ (Or.inr (Or.inr rfl)))

theorem shapeQ_context {s : State} {B : Addr} {Z width : Nat} {head : Byte} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 width) (h9 : s.gpr .r9 = head.zeroExtend 64)
    (hm : word s.mem B Field.mask.offset = mask valid) :
    WP isa (.block shapeQ) s fun t =>
      word t.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 width ∧
      word t.mem B Field.mask.offset = mask (decide (128 ≤ head.toNat) && valid) ∧
      word t.mem B 176 = word s.mem B 176 ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep [.rax, .r9] s t := by
  refine WP.mono (shapeQ_ok hs hdi hZ h8 h9 hm) fun t ⟨htm, hk⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, hk⟩
  · rw [htm, (writeW_outside _ B _ (d := Field.mask.offset) (by decide)).word (Or.inl (by decide)) (by decide)]
    exact word_writeW_self _ _ _ _
  · rw [htm, word_writeW_self]
  · rw [htm, (writeW_outside _ B _ (d := Field.mask.offset) (by decide)).word (Or.inl (by decide)) (by decide),
      (writeW_outside _ B _ (d := Field.digestPrefixLen.offset) (by decide)).word (Or.inl (by decide)) (by decide)]
  · rw [htm]
    exact (shape_store _ (Or.inr (Or.inl rfl))).trans (shape_store _ (Or.inr (Or.inr rfl)))

end VG.Proof.Dsa.X86_64
