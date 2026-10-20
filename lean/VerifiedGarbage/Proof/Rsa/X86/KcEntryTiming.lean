module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Rsa.X86.KeyCheck
public import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentTiming

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Saving and restoring registers has a trace fixed by public addresses -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem entry_relCT (full : Bool) :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ stackValue s (VG.Impl.Rsa.X86.KeyCheck.scratchArg full) = stackValue t (VG.Impl.Rsa.X86.KeyCheck.scratchArg full) ∧
      readSrc s (.mem (PublicFn.argument (VG.Impl.Rsa.X86.KeyCheck.scratchArg full))) = some (stackValue s (VG.Impl.Rsa.X86.KeyCheck.scratchArg full)) ∧
      readSrc t (.mem (PublicFn.argument (VG.Impl.Rsa.X86.KeyCheck.scratchArg full))) = some (stackValue t (VG.Impl.Rsa.X86.KeyCheck.scratchArg full)))
      (.block (VG.Impl.Rsa.X86.KeyCheck.entry full)) (VG.X86.Taint.Agree argumentTaint) := by
  unfold VG.Impl.Rsa.X86.KeyCheck.entry
  rw [List.append_assoc]
  apply VG.RelCT.block_append
  exact VG.RelCT.seq (scratchArgument_relCT (VG.Impl.Rsa.X86.KeyCheck.scratchArg full))
    (checkedProgramChange (τ' := { argumentTaint with regs := .ofList [.esp, .edi, .eax] })
      (hint := .block []) rfl rfl)

end VG.Proof.Rsa.X86.KeyCheck
