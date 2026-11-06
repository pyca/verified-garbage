module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseMain
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Impl.Ed448.PPC64LE.ScalarBase
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# `vg_ed448_scalar_base` on PPC64LE, verified

The function meets its contract of `Spec/Ed448/Contract.lean`, with no
stack: the proof against `basePPC`, which it implies, and a state satisfying
it. The code writes no nonvolatile register and never writes the link
register or calls a function, so the ABI's obligations hold of every
execution.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE

theorem scalarBase_ok (hl : Proof.Ed448.BaseLadder2Ok) (s : State) (hs : basePPC.pre s) :
    ∃ t s', Exec isa Impl.Ed448.PPC64LE.scalarBase s t s' ∧ abiPreserved s s' ∧ basePPC.post s s' := by
  obtain ⟨t, s', he, h⟩ := scalarBase_correct hl hs
  have hd : ∀ r ∈ preserved, ∀ i ∈ instrs Impl.Ed448.PPC64LE.scalarBase, dstOf i ≠ some r := by
    have h : ((instrs Impl.Ed448.PPC64LE.scalarBase).all fun i =>
        preserved.all fun r => dstOf i != some r) = true := by
      rw [← Code.allInstrs_eq]; decide +kernel
    intro r hr i hi
    have := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
    simpa using this
  exact ⟨t, s', he, ⟨fun r hr => Exec.gpr (hd r hr) he (.inl (by decide +kernel)), Exec.sp he,
    Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h⟩

end VG.Proof.Ed448.PPC64LE
