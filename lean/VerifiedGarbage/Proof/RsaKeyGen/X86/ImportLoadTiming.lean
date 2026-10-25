module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.ImportEntry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Complete native import timing depends only on public input and workspace pointers -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Import
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Import

theorem args_trace (count out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .esi])) (.block (args count out))
      (VG.X86.Taint.Agree publicState) :=
  erased_relCT (.block (args count out)) (.block (args 0 0)) (.block [])
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem load_trace (count out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .esi])) (load count out)
      (VG.X86.Taint.Agree publicState) :=
  RelCT.seq (args_trace count out) code_trace

end VG.Proof.RsaKeyGen.X86.Import
