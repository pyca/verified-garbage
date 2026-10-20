module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryResult
public import VerifiedGarbage.Proof.Dsa.X86.Generation.OuterSetup
import VerifiedGarbage.Proof.Dsa.X86.Generation.SavedPreserve

/-! # Release the inner frame and recover the untouched outer save frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem searchFreed_esp {s a b : State} (R : EntryResult s (allocated 148 a) b) :
    (freed 148 b).gpr .esp = a.gpr .esp := by
  rw [freed_esp, R.2.2.2.2.2, allocated_esp, BitVec.sub_add_cancel]

theorem searchFreed_wr {s a b : State} (R : EntryResult s (allocated 148 a) b) :
    (freed 148 b).wr = a.wr := by
  change b.wr.tail = a.wr
  rw [R.2.2.2.2.1, allocated_wr]
  rfl

theorem searchFreed_frame {s a b : State} {base : Addr}
    (F : SaveFrame a base) (R : EntryResult s (allocated 148 a) b) : SaveFrame (freed 148 b) base :=
  ⟨by rw [searchFreed_esp R]; exact F.esp,
   by rw [searchFreed_wr R]; exact F.write, F.nowrap⟩

theorem searchFreed_saved {s a b : State} (A : ParameterABI s)
    (saved : SavedRegisters s (outerBase s) a.mem) (R : EntryResult s (allocated 148 a) b) :
    SavedRegisters s (outerBase s) (freed 148 b).mem := saved.searchKeep A R.2.2.1
end VG.Proof.Dsa.X86.Generation
