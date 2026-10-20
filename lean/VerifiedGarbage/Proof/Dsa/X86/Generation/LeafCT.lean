module
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.SeedAdd
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.Trial
public meta import VerifiedGarbage.Impl.Dsa.X86.Generate
public meta import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
public meta import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Impl.Dsa.X86.Generation.SeedAdd
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Shape
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Trial
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Fixed-schedule byte and trial-arithmetic helpers need only public addresses and counts -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation

def RegistersAgree (rs : List Reg) (s t : State) : Prop := ∀ r ∈ rs, s.gpr r = t.gpr r

theorem shape_ct (len : Nat) : RelCT isa (RegistersAgree [.edi]) (shape len) (fun _ _ => True) :=
  RelCT.taint (A := taint) (τr [.edi]) (fun _ _ h => agree_regs h) (hc := .block []) (by
    exact (congrArg Option.isSome (VG.Proof.Mont.X86.Dynamic.check_of_erase_eq (shape len) (shape 1)
      (τr [.edi]) (.block []) rfl rfl rfl)).trans (by rfl))

theorem seedAdd_ct (len : Nat) (width : len = 20 ∨ len = 32) :
    RelCT isa (RegistersAgree [.esi, .edi]) (seedAdd len) (fun _ _ => True) := by
  rcases width with rfl | rfl
  all_goals exact RelCT.taint (A := taint) (τr [.esi, .edi]) (fun _ _ h => agree_regs h) (by taint_decide)

theorem trialReduce_ct : RelCT isa (RegistersAgree [.ebp, .ecx]) trialReduce (fun _ _ => True) :=
  RelCT.taint (A := taint) (τr [.ebp, .ecx]) (fun _ _ h => agree_regs h) (by taint_decide)

theorem copyMasked_ct : RelCT isa (RegistersAgree [.esi, .edx, .ecx]) VG.Impl.Dsa.X86.Generate.copyMasked (fun _ _ => True) :=
  RelCT.taint (A := taint) (τr [.esi, .edx, .ecx]) (fun _ _ h => agree_regs h) (by taint_decide)
end VG.Proof.Dsa.X86.Generation
