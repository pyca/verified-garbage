module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayLoadTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64WordTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # A complete word iteration has only public-address stack and workspace accesses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem advance_trace : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block advance)
    (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl

theorem arrayStep_trace {g : ArrayGeometry} {candidate exponent other otherExponent i : Nat} :
    RelCT isa (fun s t => ArrayState g candidate exponent i s ∧ ArrayState g other otherExponent i t)
      (arrayStep g.exponent) (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  RelCT.seq loadWord_trace (RelCT.seq (word_trace g.exponent) advance_trace)

end VG.Proof.RsaKeyGen.X86.Mod64
