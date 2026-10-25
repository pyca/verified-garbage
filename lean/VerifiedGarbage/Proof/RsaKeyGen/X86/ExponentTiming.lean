module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Exponent
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentMarkerTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentShiftTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.HalfPassTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Complete exponent preparation is independent of the candidate and its trailing zeros -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.Exponent

theorem clearTops_trace (n src out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (clearTops n src out))
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (.block (clearTops n src out)) (.block (clearTops 0 0 0)) (.block [])
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem finish_trace (n out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (finish n out))
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (.block (finish n out)) (.block (finish 0 0)) (.block [])
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem code_trace (w minusOne src out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (code w minusOne src out)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq (ExponentMarker.code_trace minusOne w)
    (RelCT.seq (checkedBlockInvariant rfl rfl)
      (RelCT.seq (RelCT.seq (clearTops_trace (2 * w) src out) (HalfPass.code_trace (2 * w) src out))
        (RelCT.seq (ExponentShift.passes_trace (2 * w) markerOffset out) (finish_trace (2 * w) out))))

end VG.Proof.RsaKeyGen.X86.Exponent
