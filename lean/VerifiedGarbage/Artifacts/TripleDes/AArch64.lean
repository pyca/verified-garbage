module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Contract
import VerifiedGarbage.Impl.TripleDes.AArch64.Fn
import VerifiedGarbage.Proof.TripleDes.AArch64.VerifiedBlock
import VerifiedGarbage.Proof.TripleDes.AArch64.Bitsliced.Verified
import VerifiedGarbage.Proof.TripleDes.AArch64.Frame
import VerifiedGarbage.Proof.TripleDes.AArch64.ShortEcb
import VerifiedGarbage.Proof.TripleDes.AArch64.ModesResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Impl.TripleDes.AArch64.BitsliceAlloc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.AArch64.BlockIO
import VerifiedGarbage.Proof.Rc2.AArch64.Cipher
import VerifiedGarbage.Proof.Rc2.AArch64.MemOps
import VerifiedGarbage.Proof.TripleDes.AArch64.Box
import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Correct
import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Verified
import VerifiedGarbage.Proof.TripleDes.AArch64.Permutation
import VerifiedGarbage.Proof.TripleDes.AArch64.RoundBody
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES on AArch64 -/

namespace VG.Artifacts.TripleDes.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.TripleDes.expandKeyApi.artifact AArch64.target {
    code := Impl.TripleDes.AArch64.Fn.expandKey
    verified := Proof.TripleDes.AArch64.expandKeyCleared_scrubbed },
  Spec.TripleDes.ecbEncryptApi.artifact AArch64.target {
    code := Impl.TripleDes.AArch64.Fn.ecbEncrypt
    verified := Proof.TripleDes.AArch64.ModesResidue.ecbEncryptCode_scrubbed },
  Spec.TripleDes.ecbDecryptApi.artifact AArch64.target {
    code := Impl.TripleDes.AArch64.Fn.ecbDecrypt
    verified := Proof.TripleDes.AArch64.ModesResidue.ecbDecryptCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.TripleDes.AArch64
