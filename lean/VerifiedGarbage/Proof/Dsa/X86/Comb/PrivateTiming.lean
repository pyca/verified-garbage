module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.RandomContext
meta import VerifiedGarbage.Impl.Dsa.X86.Comb
meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint

/-! The private comb scan body's addresses and branches depend only on public pointers
and fixed counts. All workspace values, including the exponent, are secret here. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb

def privateInputs : VG.X86.Taint.T :=
  { regs := .ofList [.edi, .esp, .esi], flags := false }

theorem private_core_check {n e : Nat} (h : Supported n e) :
    (VG.Taint.check taint privateInputs (core false n e)
      (VG.Taint.hintOf taint privateInputs (core false n e))).map
      (taint.le privateInputs) = some true := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> taint_decide

/-- All arithmetic workspace values, including the private exponent and masks,
are secret. Only fixed workspace addresses and loop counters control execution. -/
theorem private_core_relCT {n e : Nat} (h : Supported n e) :
    RelCT isa (VG.X86.Taint.Agree privateInputs) (core false n e)
      (VG.X86.Taint.Agree privateInputs) := by
  obtain ⟨τ, checked, retained⟩ := Option.map_eq_some_iff.mp (private_core_check h)
  exact VG.Proof.Dsa.X86.checkedProgramChange checked retained

end VG.Proof.Dsa.X86.Comb
