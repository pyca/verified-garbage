module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessLower
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # The witness lower-bound scan has fixed public length and addresses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessLower
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.WitnessLower

theorem code_trace (n src : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (code n src)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (code n src) (code 2 0)
    (VG.Taint.hintOf taint (roundTaint [.edi]) (Code.erase (code 2 0)))
    rfl rfl rfl (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.WitnessLower
