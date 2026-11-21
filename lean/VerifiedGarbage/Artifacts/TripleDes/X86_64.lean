module

public import VerifiedGarbage.Impl.TripleDes.X86_64.Fn
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
  Spec.TripleDes.expandKeyApi.artifact X86_64.target { code := Impl.TripleDes.X86_64.Fn.expandKey, verified := .scrubbed Proof.TripleDes.X86_64.Scrub.expandKey_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.expandKey_spSafe },
  Spec.TripleDes.ecbEncryptApi.artifact X86_64.target { suffix := "_avx512", code := Impl.TripleDes.X86_64.Fn.ecbEncryptAvx512, verified := .scrubbed Proof.TripleDes.X86_64.Scrub.ecbEncryptAvx512_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.ecbEncryptAvx512_spSafe },
  Spec.TripleDes.ecbEncryptApi.artifact X86_64.target { suffix := "_avx2", code := Impl.TripleDes.X86_64.Fn.ecbEncryptAvx2, verified := .scrubbed Proof.TripleDes.X86_64.Scrub.ecbEncryptAvx2_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.ecbEncryptAvx2_spSafe },
  Spec.TripleDes.ecbEncryptApi.artifact X86_64.target { code := Impl.TripleDes.X86_64.Fn.ecbEncryptSse, verified := .scrubbed Proof.TripleDes.X86_64.Scrub.ecbEncryptSse_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.ecbEncryptSse_spSafe },
  Spec.TripleDes.ecbDecryptApi.artifact X86_64.target { suffix := "_avx512", code := Impl.TripleDes.X86_64.Fn.ecbDecryptAvx512, verified := .scrubbed Proof.TripleDes.X86_64.Scrub.ecbDecryptAvx512_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.ecbDecryptAvx512_spSafe },
  Spec.TripleDes.ecbDecryptApi.artifact X86_64.target { suffix := "_avx2", code := Impl.TripleDes.X86_64.Fn.ecbDecryptAvx2, verified := .scrubbed Proof.TripleDes.X86_64.Scrub.ecbDecryptAvx2_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.ecbDecryptAvx2_spSafe },
  Spec.TripleDes.ecbDecryptApi.artifact X86_64.target { code := Impl.TripleDes.X86_64.Fn.ecbDecryptSse, verified := .scrubbed Proof.TripleDes.X86_64.Scrub.ecbDecryptSse_scrubbed, spSafe := Proof.TripleDes.X86_64.Scrub.ecbDecryptSse_spSafe }]

end VG.Artifacts.TripleDes.X86_64
