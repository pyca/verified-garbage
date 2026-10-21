module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Word
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Timing
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # A whole native-word reduction has a fixed secret-independent trace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem steps_trace (exponent count : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (steps exponent count))
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  blockFlatMap_relCT (List.range count) (fun _ => bit exponent) (fun _ => bit_trace exponent)

theorem word_trace (exponent : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (VG.Impl.RsaKeyGen.X86.Mod64.word exponent))
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := steps_trace exponent 32

end VG.Proof.RsaKeyGen.X86.Mod64
