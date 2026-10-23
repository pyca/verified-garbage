module

public import VerifiedGarbage.Proof.X448.PPC64LE.Main
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.X448.PPC64LE.CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-!
# X448 on PPC64LE: verified

`vg_x448` meets the shared contract of `Spec/X448/Contract.lean`: the
proof against `x448PPC64LE`, which it implies, and a state satisfying it.
The code writes no nonvolatile register and never writes the link register
or calls a function, so the ABI's obligations hold of every execution.
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE

theorem x448_ok (s : State) (hs : x448PPC64LE.pre s) :
    ∃ t s', Exec isa Impl.X448.PPC64LE.x448 s t s' ∧ abiPreserved s s' ∧ x448PPC64LE.post s s' := by
  obtain ⟨t, s', he, h⟩ := x448_correct (XPre.of hs)
  have hd : ∀ r ∈ preserved, ∀ i ∈ instrs Impl.X448.PPC64LE.x448, dstOf i ≠ some r := by
    have h : ((instrs Impl.X448.PPC64LE.x448).all fun i => preserved.all fun r => dstOf i != some r) = true := by
      rw [← Code.allInstrs_eq]; decide +kernel
    intro r hr i hi
    have := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
    simpa using this
  exact ⟨t, s', he, ⟨fun r hr => Exec.gpr (hd r hr) he (.inl (by decide +kernel)), Exec.sp he,
    Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h⟩

theorem x448_ct' : ConstantTime isa x448PPC64LE.pre x448PPC64LE.pub Impl.X448.PPC64LE.x448 :=
  x448_ct fun _ _ _ _ ⟨h3, h4, h5, h6, hsp⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption⟩

/-- A state satisfying the precondition. -/
def x448Sat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 56⟩, ⟨0x3000, 56⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448_verified :
    Verified PPC64LE.target Impl.X448.PPC64LE.x448 (Spec.X448.x448Contract PPC64LE.abi) :=
  Verified.of_correct x448_ok x448_ct' (by
    contract_implies [Spec.X448.x448Contract, Spec.X448.x448Sig, Proof.X448.PPC64LE.x448PPC64LE,
      PPC64LE.abi, PPC64LE.argRegs] [Proof.X448.PPC64LE.x448Sat] using Proof.X448.PPC64LE.x448Sat)

end VG.Proof.X448.PPC64LE
