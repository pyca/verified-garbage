module
public import VerifiedGarbage.Impl.Rsa.X86.Recover
public import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentTiming
public import VerifiedGarbage.Proof.Weierstrass.PointContract

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Saving and restoring registers has a trace fixed by public addresses -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem entry_relCT :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ stackValue s 10 = stackValue t 10 ∧
      readSrc s (.mem (PublicFn.argument 10)) = some (stackValue s 10) ∧
      readSrc t (.mem (PublicFn.argument 10)) = some (stackValue t 10))
      (.block VG.Impl.Rsa.X86.Recover.entry) (VG.X86.Taint.Agree argumentTaint) := by
  unfold VG.Impl.Rsa.X86.Recover.entry
  rw [List.append_assoc]
  apply VG.RelCT.block_append
  exact VG.RelCT.seq (scratchArgument_relCT 10)
    (checkedProgramChange (τ' := { argumentTaint with regs := .ofList [.esp, .edi, .eax] })
      (hint := .block []) rfl rfl)

end VG.Proof.Rsa.X86.Recover
