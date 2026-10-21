module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentShift
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.SigMaskTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.HalfPassTiming

/-! # Every alignment pass executes independently of the secret shift -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentShift
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.ExponentShift

theorem halfIf_trace (n marker out j : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (halfIf n marker out j)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq (SigMask.code_trace marker j) (HalfPass.code_trace n out out)

theorem passes_trace (n marker out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (passes n marker out)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq (halfIf_trace n marker out 1) (RelCT.seq (halfIf_trace n marker out 2) (halfIf_trace n marker out 3))

end VG.Proof.RsaKeyGen.X86.ExponentShift
