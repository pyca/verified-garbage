module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseMain
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Impl.Ed448.PPC64LE.ScalarBase
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# `vg_ed448_scalar_base` on PPC64LE, verified

The function meets its contract of `Spec/Ed448/Contract.lean`, with no
stack: the proof against `basePPC`, which it implies, and a state satisfying
it. The code writes no nonvolatile register but `r14` (its calls change
only the volatile registers of `linkRegs`), and it returns with the `r14`
and the link register it was called with (`scalarBase_correct`), so the
ABI's obligations hold of every execution.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE

theorem scalarBase_ok (hl : Proof.Ed448.BaseLadder2Ok) (s : State) (hs : basePPC.pre s) :
    ∃ t s', Exec isa Impl.Ed448.PPC64LE.scalarBase s t s' ∧ abiPreserved s s' ∧ basePPC.post s s' := by
  obtain ⟨t, s', he, h, hlr, h14⟩ := scalarBase_correct hl hs
  have hd : ∀ r ∈ preserved.erase .r14, ∀ i ∈ instrs Impl.Ed448.PPC64LE.scalarBase, dstOf i ≠ some r := by
    have h : ((instrs Impl.Ed448.PPC64LE.scalarBase).all fun i =>
        (preserved.erase .r14).all fun r => dstOf i != some r) = true := by
      rw [← Code.allInstrs_eq]; decide +kernel
    intro r hr i hi
    have := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
    simpa using this
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, hlr⟩, h⟩
  by_cases e : r = .r14
  · subst e; exact h14
  · exact Exec.gpr (hd r ((List.mem_erase_of_ne e).mpr hr)) he (.inr (preserved_not_link r hr))

end VG.Proof.Ed448.PPC64LE
