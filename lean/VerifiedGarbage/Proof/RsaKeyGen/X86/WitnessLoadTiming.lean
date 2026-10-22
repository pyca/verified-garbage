module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessLoad
import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoadTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessSampleTiming
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Import and sampling reveal the entropy pointer and width, but no random bytes -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessLoad
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86 VG.Proof.Dsa.X86

theorem zeros_trace (o n : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (VG.Impl.RsaKeyGen.X86.WitnessLoad.zeros o n))
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessLoad.zeros
  apply blockFlatMap_relCT
  intro j
  exact erased_relCT _ (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc 0) .eax])
    (.block []) rfl rfl rfl rfl

theorem codeAt_trace (D k w : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi, .esi])) (VG.Impl.RsaKeyGen.X86.WitnessLoad.codeAt D k w)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessLoad.codeAt VG.Impl.RsaKeyGen.X86.WitnessLoad.zeroTail
  refine RelCT.seq (Import.load_trace (D / 4) (VG.Impl.Bignum.X86.PublicContext.slot w 6)) ?_
  exact RelCT.seq ((zeros_trace _ _).mono (fun _ _ H => taint.le_sound (by decide +kernel) H) (fun _ _ H => H))
    (WitnessSample.codeAt_trace _ w _ _)

theorem code_trace (w : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi, .esi])) (VG.Impl.RsaKeyGen.X86.WitnessLoad.code w)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  codeAt_trace _ _ w

end VG.Proof.RsaKeyGen.X86.WitnessLoad
