module

public import VerifiedGarbage.Impl.Bignum.X86.CrtFn
public import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Saving and restoring registers has a trace fixed by public addresses -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem entry_relCT :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ stackValue s 16 = stackValue t 16 ∧
      readSrc s (.mem (PublicFn.argument 16)) = some (stackValue s 16) ∧
      readSrc t (.mem (PublicFn.argument 16)) = some (stackValue t 16))
      (.block Crt.entry) (VG.X86.Taint.Agree argumentTaint) := by
  unfold Crt.entry
  rw [List.append_assoc]
  apply VG.RelCT.block_append
  exact VG.RelCT.seq (scratchArgument_relCT 16)
    (checkedProgramChange (τ' := { argumentTaint with regs := .ofList [.esp, .edi, .eax] })
      (hint := .block []) rfl rfl)

theorem restore_relCT :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block Crt.restore) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (workspaceTaint false) (fun _ _ h => h) (hc := .block [])
  rfl

end VG.Proof.Bignum.X86.Crt
