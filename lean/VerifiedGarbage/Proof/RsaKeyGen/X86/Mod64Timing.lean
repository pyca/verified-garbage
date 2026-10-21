module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # A public-exponent reduction bit keeps every candidate bit secret -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem bit_trace (exponent : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (bit exponent))
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  erased_relCT (.block (bit exponent)) (.block (bit 0)) (.block [])
    rfl rfl rfl (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.Mod64
