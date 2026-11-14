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
it. The code writes no nonvolatile register but `r14`–`r31` (its calls
change only the volatile registers of `linkRegs`), and it returns with the
`r14`–`r31` and the link register it was called with (`scalarBase_correct`),
so the ABI's obligations hold of every execution.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE

theorem scalarBase_ok (hl : Proof.Ed448.BaseLadder2Ok) (s : State) (hs : basePPC.pre s) :
    ∃ t s', Exec isa Impl.Ed448.PPC64LE.scalarBase s t s' ∧ abiPreserved s s' ∧ basePPC.post s s' := by
  obtain ⟨t, s', he, h, hlr, h14, hnv⟩ := scalarBase_correct hl hs
  have hd : ∀ i ∈ instrs Impl.Ed448.PPC64LE.scalarBase, dstOf i ≠ some .r2 := by
    have h : ((instrs Impl.Ed448.PPC64LE.scalarBase).all fun i => dstOf i != some .r2) = true := by
      rw [← Code.allInstrs_eq]; decide +kernel
    intro i hi
    simpa using List.all_eq_true.mp h i hi
  have hpre : ∀ r ∈ preserved, r = .r2 ∨ r = .r14 ∨ ∃ i < 17, Impl.X448.PPC64LE.nvR i = r := by decide
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, hlr⟩, h⟩
  rcases hpre r hr with rfl | rfl | ⟨i, hi, rfl⟩
  · exact Exec.gpr hd he (.inr (preserved_not_link _ hr))
  · exact h14
  · exact hnv i hi

end VG.Proof.Ed448.PPC64LE
