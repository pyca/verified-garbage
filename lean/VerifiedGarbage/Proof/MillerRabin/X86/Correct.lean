module

import VerifiedGarbage.Proof.MillerRabin.X86.Frame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MillerRabin.X86.Baseline
public import VerifiedGarbage.Proof.MillerRabin.X86.EntryMemory

/-! # The callable i686 round meets the existing Miller–Rabin contract -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.MillerRabin.X86

theorem Entry.pushed_byte {s : State} (E : Entry s) {i : Nat} (index : i < lenOf s) :
    (entered s).mem (off (wsOf s) i) = s.mem (off (wsOf s) i) := by
  have saved := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide)
    (by change 16 ≤ _; have := E.stackFit; omega)
  apply saved
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  intro inside
  apply E.savedSeparate _ inside
  exact Offset.contains_base _ (by omega) (by have := E.bound; omega)

theorem correct (s : State)
    (h : (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56).pre s) :
    ∃ tr t, Exec isa (code montName montCode) s tr t ∧ abiPreserved s t ∧
      (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56).post s t := by
  have E := entry_of h
  obtain ⟨tr, t, exec, abi, result, frame⟩ := E.framed
  refine ⟨tr, t, exec, abi, ?_⟩
  sig_post [Spec.MillerRabin.roundContract, Spec.MillerRabin.roundSig, abi, argSlots, argVal, argBytes]
  refine ⟨?_, ?_⟩
  · intro b witness
    rw [BitVec.setWidth_append_eq_right]
    exact result b witness
  · apply roundFrame_keeps (g := geometry s) (by change (arg s 1).toNat * 8 = 8 * (arg s 1).toNat; omega)
    intro i index outside
    exact (frame i index outside).trans (E.pushed_byte index)

end VG.Proof.MillerRabin.X86
