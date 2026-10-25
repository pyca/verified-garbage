module
public import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentTiming

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Saving and restoring registers has a trace fixed by public addresses -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem publicEntry_relCT :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ stackValue s 8 = stackValue t 8 ∧
      readSrc s (.mem (PublicFn.argument 8)) = some (stackValue s 8) ∧
      readSrc t (.mem (PublicFn.argument 8)) = some (stackValue t 8))
      (.block PublicFn.entry) (VG.X86.Taint.Agree argumentTaint) := by
  unfold PublicFn.entry
  rw [List.append_assoc]
  apply VG.RelCT.block_append
  exact VG.RelCT.seq (scratchArgument_relCT 8)
    (checkedProgramChange (τ' := { argumentTaint with regs := .ofList [.esp, .edi, .eax] })
      (hint := .block []) (by kernel_rfl) (by kernel_rfl))

theorem publicRestore_relCT :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block PublicFn.restore) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (workspaceTaint false) (fun _ _ h => h) (hc := .block [])
  rfl

end VG.Proof.Bignum.X86
