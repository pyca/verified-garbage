module

public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn
public import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Saving and restoring registers has a trace fixed by public addresses -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem precomputeEntry_relCT :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ stackValue s 4 = stackValue t 4 ∧
      readSrc s (.mem (PublicFn.argument 4)) = some (stackValue s 4) ∧
      readSrc t (.mem (PublicFn.argument 4)) = some (stackValue t 4))
      (.block PrecomputeFn.entry) (VG.X86.Taint.Agree argumentTaint) := by
  unfold PrecomputeFn.entry
  rw [List.append_assoc]
  apply VG.RelCT.block_append
  exact VG.RelCT.seq (scratchArgument_relCT 4)
    (checkedProgramChange (τ' := { argumentTaint with regs := .ofList [.esp, .edi, .eax] })
      (hint := .block []) rfl rfl)

end VG.Proof.Bignum.X86
