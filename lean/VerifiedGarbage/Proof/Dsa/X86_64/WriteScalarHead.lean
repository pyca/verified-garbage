module
public import VerifiedGarbage.Impl.Dsa.X86_64.Core
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual

/-! # Resolving the two signature output halves -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev scalarHead (offset : Nat) (second : Bool) : List Instr :=
  ([.mov .rsi (.reg .rdi), .alu .add .rsi (.imm (BitVec.ofNat 32 offset)),
    .mov .rdx (.mem (Core.field .out)), .mov .rcx (.mem (Core.field .qLen)),
    .mov .r8 (.mem (Core.field .mask))] : List Instr) ++
    (if second then [.alu .add .rdx (.reg .rcx)] else [])

theorem scalarHead_ok {s : State} {B out : Addr} {Z offset q : Nat} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z) (ho : offset < 2 ^ 31)
    (hout : word s.mem B Field.out.offset = out) (hq : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q)
    (hm : word s.mem B Field.mask.offset = mask valid) (second : Bool) :
    WP isa (.block (scalarHead offset second)) s fun t =>
      t.gpr .rsi = off B offset ∧ t.gpr .rdx = (if second then out + BitVec.ofNat 64 q else out) ∧
      t.gpr .rcx = BitVec.ofNat 64 q ∧ t.gpr .r8 = mask valid ∧
      t.mem = s.mem ∧ Keep [.rsi, .rdx, .rcx, .r8] s t := by
  refine WP.mono (WP.keep [.rsi, .rdx, .rcx, .r8] (Q := fun t =>
      t.gpr .rsi = off B offset ∧ t.gpr .rdx = (if second then out + BitVec.ofNat 64 q else out) ∧
      t.gpr .rcx = BitVec.ofNat 64 q ∧ t.gpr .r8 = mask valid ∧ t.mem = s.mem) ?_ ?_)
    fun t ⟨⟨hsi, hdx, hcx, h8, hmem⟩, hk⟩ => ⟨hsi, hdx, hcx, h8, hmem, hk⟩
  · cases second <;> unfold scalarHead <;> simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append, List.nil_append]
    all_goals
      xrun [State.ea, Core.field, fieldAddress, hdi, hout, hq, hm, sx_ofNat ho,
        hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .out).2 hZ),
        hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .qLen).2 hZ),
        hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ)]
  · cases second <;> rfl

end VG.Proof.Dsa.X86_64
