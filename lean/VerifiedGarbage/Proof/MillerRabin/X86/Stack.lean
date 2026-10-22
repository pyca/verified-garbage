module

public import VerifiedGarbage.Proof.MillerRabin.X86.ABI
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Call

/-! # Exact stack use and preservation of the stack pointer by ordinary instructions -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86

theorem body_noSp : NoSp VG.Impl.MillerRabin.X86.body := by
  apply NoSp.of_all
  decide

theorem round_stack : stackUse VG.Impl.MillerRabin.X86.code = stackBytes := by decide

end VG.Proof.MillerRabin.X86
