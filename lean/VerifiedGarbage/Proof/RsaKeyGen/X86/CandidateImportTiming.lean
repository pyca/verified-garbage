module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateImport
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoadTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Complete candidate construction keeps all random bytes secret -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateImport
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86

theorem code_trace (w out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .esi])) (CandidateImport.code w out)
      (VG.X86.Taint.Agree VG.Proof.RsaKeyGen.X86.Import.publicState) := by
  refine RelCT.seq (VG.Proof.RsaKeyGen.X86.Import.load_trace (2 * w) out) ?_
  exact erased_relCT (.block (CandidateBits.code w out)) (.block (CandidateBits.code 0 0)) (.block [])
    rfl rfl rfl (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.CandidateImport
