module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.InverseLift
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Inverse preparation accesses only fixed offsets from the public workspace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.InverseLift
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.InverseLift

theorem setup_trace (mo inv : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (setup mo inv))
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  erased_relCT (.block (setup mo inv)) (.block (setup 0 0)) (.block [])
    rfl rfl rfl (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.InverseLift
