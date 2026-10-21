module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Close
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.DifferenceTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.NearTiming

/-! # Both secret prime candidates stay private through the arithmetic distance check -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Close
open VG VG.X86 VG.Impl.RsaKeyGen.X86.Close

theorem code_trace (n out tmp a b : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (code n out tmp a b)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  RelCT.seq (Difference.code_trace n out tmp a b) (Near.code_trace n out)

end VG.Proof.RsaKeyGen.X86.Close
