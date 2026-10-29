module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.PrepareHeader
public import VerifiedGarbage.Impl.RsaKeyGen.X86.HeaderRt
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Impl.RsaKeyGen.X86.Header
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Impl.RsaKeyGen.X86.MontInverse
/-! # Header and inverse preparation have a candidate-independent trace -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/HeaderTiming.lean`, which only this module imported.
section

/-! # Prepared metadata initialization has no secret-dependent address -/

section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Header

theorem code_trace (w : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (code w))
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  erased_relCT (.block (code w)) (.block (code 0)) (.block [])
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.Header
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/MontInverseTiming.lean`, which only this module imported.
section

/-! # Full inverse setup uses a fixed native multiplication schedule -/

section
namespace VG.Proof.RsaKeyGen.X86.MontInverse
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.MontInverse

theorem code_trace (modulus inverse : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (code modulus inverse)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (code modulus inverse) (code 0 0)
    (.seq (roundTaint [.edi]) (.block []) (.block [])) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.MontInverse
end

end

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
