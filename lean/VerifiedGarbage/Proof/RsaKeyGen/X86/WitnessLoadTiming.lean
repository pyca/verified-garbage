module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessLoad
import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoadTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessSampleTiming
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks

/-! # Import and sampling reveal the entropy pointer and width, but no random bytes -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessLoad
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86

theorem code_trace (w : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi, .esi])) (VG.Impl.RsaKeyGen.X86.WitnessLoad.code w)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessLoad.code
  refine RelCT.seq (Import.load_trace (2 * w) (VG.Impl.Bignum.X86.PublicContext.slot w 6)) ?_
  exact (WitnessSample.code_trace w _ _).mono
    (fun _ _ H => taint.le_sound (by decide +kernel) H) (fun _ _ H => H)

end VG.Proof.RsaKeyGen.X86.WitnessLoad
