module

public import VerifiedGarbage.Impl.Mont.X86.Compact
public import VerifiedGarbage.Proof.Mont.X86.Compact.Entry
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingCore
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingGeometry
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingEntry
import VerifiedGarbage.Proof.Framework.X86.RelCT
public import Init.Prelude
public import VerifiedGarbage.TCB.Artifact

/-! # Prepared multiplication is constant time under the public RSA contract -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Impl.Mont.X86
open VG.Proof.Rsa.Mont

theorem publicInputs {s t : State} (H : (mulContract abi 16).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ (∀ i < 5, arg s i = arg t i) ∧
      wOf s.mem (wsOf s) = wOf t.mem (wsOf t) := by
  sig_pub [mulContract, sig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  refine ⟨by with_reducible assumption, ?_, ?_⟩
  · intro i bound
    match i, bound with
    | 0, _ => with_reducible assumption
    | 1, _ => with_reducible assumption
    | 2, _ => with_reducible assumption
    | 3, _ => with_reducible assumption
    | 4, _ => with_reducible assumption
  · apply List.singleton_inj.mp
    with_reducible assumption

theorem constantTime : ConstantTime isa (mulContract abi 16).pre (mulContract abi 16).pub Compact.body := by
  apply RelCT.constantTime
  unfold Compact.body
  refine VG.X86.RelCT.frame (rs := savedRegisters) (R := fun _ _ => True)
    (fun _ _ H => (publicInputs H.2.2).1) ?_
  rintro a b tr ur u z ⟨s, t, H, rfl, rfl⟩ E G
  have A := entry_of H.1
  have B := entry_of H.2.1
  obtain ⟨sp, args, width⟩ := publicInputs H.2.2
  have geo := geometry_eq args width
  have pair : Pair (geometry s) [] (entered s) (entered t) :=
    ⟨A.context, geo.symm ▸ B.context, entered_agree A B sp args⟩
  exact ⟨(inner_trace A.geometry_valid _ _ _ _ _ _ pair E G).1, True.intro⟩

end VG.Proof.Mont.X86.Compact
