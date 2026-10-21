module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Check
import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Timing
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint

/-! # Complete native coprimality executes independently of the remainder's value -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Gcd64

theorem setup_trace (offset : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block (setup offset))
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  erased_relCT (.block (setup offset)) (.block (setup 0)) (.block []) rfl rfl rfl (by decide +kernel)

theorem result_trace : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block result)
    (VG.X86.Taint.Agree (workspaceTaint false)) := checkedBlockInvariant rfl rfl

theorem check_trace (offset : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (check offset)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  RelCT.seq (setup_trace offset) (RelCT.seq code_trace result_trace)

end VG.Proof.RsaKeyGen.X86.Gcd64
