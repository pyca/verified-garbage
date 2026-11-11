module
import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit

public import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Verified
public import VerifiedGarbage.Proof.TripleDes.X86_64.Frame
public import VerifiedGarbage.Proof.TripleDes.X86_64.SpSafe
public import VerifiedGarbage.Proof.TripleDes.X86_64.EcbCall.Verified
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.TripleDes.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Lit
public import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Verified
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Verified
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Verified
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.X86_64.StraightX
import VerifiedGarbage.Proof.Framework.X86_64.StraightZ
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.X86_64.Words
public import VerifiedGarbage.Proof.Rc2.Word
public import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Finish
public import VerifiedGarbage.Proof.TripleDes.Bytes
public import VerifiedGarbage.Proof.TripleDes.Permutation
public import VerifiedGarbage.Proof.TripleDes.X86_64.Box
public import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Component
public import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Copy
public import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Correct
public import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Loop
public import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Rotation
public import VerifiedGarbage.Proof.TripleDes.X86_64.KeySteps
public import VerifiedGarbage.Proof.TripleDes.X86_64.RoundBody
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Triple DES on x86-64 -/

@[expose] public section

namespace VG.Artifacts.TripleDes.X86_64

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact X86_64.target Proof.TripleDes.X86_64.Scrub.expandKeyReg,
  Spec.TripleDes.ecbEncryptApi.artifact X86_64.target Proof.TripleDes.X86_64.Scrub.ecbEncryptAvx512Reg,
  Spec.TripleDes.ecbEncryptApi.artifact X86_64.target Proof.TripleDes.X86_64.Scrub.ecbEncryptAvx2Reg,
  Spec.TripleDes.ecbEncryptApi.artifact X86_64.target Proof.TripleDes.X86_64.Scrub.ecbEncryptSseReg,
  Spec.TripleDes.ecbDecryptApi.artifact X86_64.target Proof.TripleDes.X86_64.Scrub.ecbDecryptAvx512Reg,
  Spec.TripleDes.ecbDecryptApi.artifact X86_64.target Proof.TripleDes.X86_64.Scrub.ecbDecryptAvx2Reg,
  Spec.TripleDes.ecbDecryptApi.artifact X86_64.target Proof.TripleDes.X86_64.Scrub.ecbDecryptSseReg]

end VG.Artifacts.TripleDes.X86_64
