module

import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Mont.X86.Compact.Prepared
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.TCB.X86.Isa

/-! # The reviewed Montgomery contract on entry to an i686 call -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Proof.Mont VG.Proof.Rsa.Mont

abbrev wsOf (s : State) : Addr := (arg s 0).setWidth 64
abbrev lenOf (s : State) : Nat := (arg s 1).toNat * 8

structure Entry (s : State) : Prop where
  stackFit : 16 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  rd : s.rd = [⟨argAddr s 0, 20⟩]
  wr : s.wr = [⟨wsOf s, lenOf s⟩]
  bound : (arg s 0).toNat + lenOf s ≤ 2 ^ 32
  savedSeparate : (⟨(s.gpr .esp).setWidth 64 - 16#64, 16⟩ : Region).Disjoint ⟨wsOf s, lenOf s⟩
  savedArgsSeparate : (⟨(s.gpr .esp).setWidth 64 - 16#64, 16⟩ : Region).Disjoint ⟨argAddr s 0, 20⟩
  argSeparate : (⟨wsOf s, lenOf s⟩ : Region).Disjoint ⟨argAddr s 0, 20⟩
  returnSeparate : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨wsOf s, lenOf s⟩
  layout : Layout s.mem (wsOf s) (arg s 1).toNat
  output : Operand (arg s 2).toNat
  left : Operand (arg s 3).toNat
  right : Operand (arg s 4).toNat
  inverse : ((s.mem.readW (wsOf s + BitVec.ofNat 64 (arrAt (wOf s.mem (wsOf s)) aM)) 64).toNat *
      (wordAt s.mem (wsOf s) minvWord).toNat + 1) % 2 ^ 64 = 0
  rightLt : numAt s.mem (wsOf s) (wOf s.mem (wsOf s)) (arg s 4).toNat <
      numAt s.mem (wsOf s) (wOf s.mem (wsOf s)) aM

theorem entry_of {s : State} (h : (mulContract abi 16).pre s) : Entry s := by
  sig_pre [mulContract, sig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Mont.X86.Compact
