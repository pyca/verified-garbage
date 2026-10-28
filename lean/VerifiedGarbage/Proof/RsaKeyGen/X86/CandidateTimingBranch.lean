module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDispatchTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDispatch
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Boolean status branches compose without publishing candidate arithmetic -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem DrawnPair.keepFlags {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    {s t u z : State} (P : DrawnPair E eBytes pBytes qBytes rBytes sBytes s t) (U : Fupd s u) (Z : Fupd t z) :
    DrawnPair E eBytes pBytes qBytes rBytes sBytes u z :=
  ⟨P.left.keepMem v U.mem (U.keeps []) (by decide) (by decide) U.syms,
    P.right.keepMem v Z.mem (Z.keeps []) (by decide) (by decide) Z.syms⟩

theorem TestPair.keepFlags {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    {s t u z : State} (P : TestPair E eBytes pBytes qBytes rBytes sBytes s t) (U : Fupd s u) (Z : Fupd t z) :
    TestPair E eBytes pBytes qBytes rBytes sBytes u z := by
  refine ⟨P.toDrawnPair.keepFlags v U Z, ?_, ?_⟩
  · rw [U.mem]; exact P.savedLeft
  · rw [Z.mem]; exact P.savedRight

end VG.Proof.RsaKeyGen.X86.Candidate
