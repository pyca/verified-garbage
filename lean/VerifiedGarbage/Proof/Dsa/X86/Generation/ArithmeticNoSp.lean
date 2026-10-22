module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Exponent
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Workspace
public import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! The reused candidate arithmetic reads arguments without changing esp. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation

theorem candidate_exponent_noSp : NoSp (prepareCandidateExponent arithmeticLay) :=
  NoSp.of_all (by decide)

end VG.Proof.Dsa.X86.Generation
