module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Contract
import VerifiedGarbage.Impl.TripleDes.X86_64.Fn
import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Verified
import VerifiedGarbage.Proof.TripleDes.X86_64.Frame
import VerifiedGarbage.Proof.TripleDes.X86_64.SpSafe
import VerifiedGarbage.Proof.TripleDes.X86_64.EcbCall.Verified
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.TripleDes.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Lit
import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Verified
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.Verified
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Verified
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.X86_64.StraightX
import VerifiedGarbage.Proof.Framework.X86_64.StraightZ
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Finish
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.TripleDes.X86_64.Box
import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Component
import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Copy
import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Correct
import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Loop
import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Rotation
import VerifiedGarbage.Proof.TripleDes.X86_64.KeySteps
import VerifiedGarbage.Proof.TripleDes.X86_64.RoundBody
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.SpecApis


/-! # Triple DES on x86-64 -/

namespace VG.Artifacts.TripleDes.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.TripleDes.expandKeyApi.artifact X86_64.target { code := Impl.TripleDes.X86_64.Fn.expandKey, verified := Proof.TripleDes.X86_64.Scrub.expandKey_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.expandKey_spSafe },
  Spec.TripleDes.ecbEncryptApi.artifact X86_64.target { suffix := "_avx512", code := Impl.TripleDes.X86_64.Fn.ecbEncryptAvx512, verified := Proof.TripleDes.X86_64.Scrub.ecbEncryptAvx512_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.ecbEncryptAvx512_spSafe },
  Spec.TripleDes.ecbEncryptApi.artifact X86_64.target { suffix := "_avx2", code := Impl.TripleDes.X86_64.Fn.ecbEncryptAvx2, verified := Proof.TripleDes.X86_64.Scrub.ecbEncryptAvx2_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.ecbEncryptAvx2_spSafe },
  Spec.TripleDes.ecbEncryptApi.artifact X86_64.target { code := Impl.TripleDes.X86_64.Fn.ecbEncryptSse, verified := Proof.TripleDes.X86_64.Scrub.ecbEncryptSse_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.ecbEncryptSse_spSafe },
  Spec.TripleDes.ecbDecryptApi.artifact X86_64.target { suffix := "_avx512", code := Impl.TripleDes.X86_64.Fn.ecbDecryptAvx512, verified := Proof.TripleDes.X86_64.Scrub.ecbDecryptAvx512_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.ecbDecryptAvx512_spSafe },
  Spec.TripleDes.ecbDecryptApi.artifact X86_64.target { suffix := "_avx2", code := Impl.TripleDes.X86_64.Fn.ecbDecryptAvx2, verified := Proof.TripleDes.X86_64.Scrub.ecbDecryptAvx2_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.ecbDecryptAvx2_spSafe },
  Spec.TripleDes.ecbDecryptApi.artifact X86_64.target { code := Impl.TripleDes.X86_64.Fn.ecbDecryptSse, verified := Proof.TripleDes.X86_64.Scrub.ecbDecryptSse_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.ecbDecryptSse_spSafe }]

spec_apis artifacts

end VG.Artifacts.TripleDes.X86_64
