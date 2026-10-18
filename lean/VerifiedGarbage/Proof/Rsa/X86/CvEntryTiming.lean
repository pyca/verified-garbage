module

public import VerifiedGarbage.Proof.Rsa.X86.CvPair
public import VerifiedGarbage.Proof.Dsa.X86.EntryTiming

/-! # Saving and restoring registers has a trace fixed by public addresses -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem entry_relCT :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ stackValue s 14 = stackValue t 14 ∧
      readSrc s (.mem (PublicFn.argument 14)) = some (stackValue s 14) ∧
      readSrc t (.mem (PublicFn.argument 14)) = some (stackValue t 14))
      (.block VG.Impl.Rsa.X86.CrtValues.entry) (VG.X86.Taint.Agree argumentTaint) := by
  unfold VG.Impl.Rsa.X86.CrtValues.entry
  rw [List.append_assoc]
  apply VG.RelCT.block_append
  exact VG.RelCT.seq (scratchArgument_relCT 14)
    (checkedProgramChange (τ' := { argumentTaint with regs := .ofList [.esp, .edi, .eax] })
      (hint := .block []) rfl rfl)

end VG.Proof.Rsa.X86.CrtValues
