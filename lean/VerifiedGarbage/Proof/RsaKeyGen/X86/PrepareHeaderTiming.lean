module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.PrepareHeader
public import VerifiedGarbage.Impl.RsaKeyGen.X86.HeaderRt
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.MontInverseTiming

/-! # Header and inverse preparation have a candidate-independent trace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PrepareHeader
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.PrepareHeader

theorem code_trace (w : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (code w)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq (Header.code_trace w) (MontInverse.code_trace (VG.Impl.Bignum.X86.PublicContext.slot w 0) 56)

theorem prepareRt_trace :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) VG.Impl.RsaKeyGen.X86.HeaderRt.prepare
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq (VG.Proof.Dsa.X86.erased_relCT _ (.block VG.Impl.RsaKeyGen.X86.HeaderRt.code) (.block [])
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)) (MontInverse.code_trace 256 56)

end VG.Proof.RsaKeyGen.X86.PrepareHeader
