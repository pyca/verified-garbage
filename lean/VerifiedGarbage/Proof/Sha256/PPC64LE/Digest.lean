module

import VerifiedGarbage.Proof.Sha256.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Sha256.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha224
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha256
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Digest
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha224
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha256
meta import VerifiedGarbage.Proof.MdStream.PPC64LE.Digest

/-!
# The one-shot SHA-224 and SHA-256 digests on PPC64LE

The one-shot digest over any streaming hash function
(`Impl/MdStream/PPC64LE/Digest.lean`) for SHA-224's and SHA-256's streaming
functions, as HMAC's code calls them (`Proof.Hmac.Stream.PPC64LE.Sha224.hash`,
`Sha256.hash`): its constant time, which the kernel checks, and the
contracts of `Spec.Sha256.digest224Api` and `digest256Api`.
-/

@[expose] public section

namespace VG.Proof.Sha256.PPC64LE.Digest

open VG.PPC64LE
open VG.Proof.MdStream.PPC64LE.Digest
open VG.Impl.MdStream.PPC64LE.Digest (digest code frameBytes)

namespace Sha224

open VG.Proof.Hmac.Stream.PPC64LE.Sha224 (hash ok)

theorem digest_ct : ConstantTime isa (digestG ok.SH hash.lbytes 96).pre (digestG ok.SH hash.lbytes 96).pub
    (digest hash) :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => agree hp) (by taint_decide)

theorem digestScratch : Verified PPC64LE.target (digest hash) (digestScratchContract ok.SH (hash.lbytes / 8)) :=
  MdStream.PPC64LE.Digest.digestScratch ok (by decide) digest_ct (by
    inst_sat [digestScratchContract, digestScratchSig, Spec.Sha256.digestPost, Spec.Hmac.sha224S, Spec.Hmac.sha224,
      PPC64LE.abi, PPC64LE.argRegs]
      using digestSat 28 hash.lbytes)

theorem verified : Verified PPC64LE.target (code hash)
    (Spec.Sha256.digestContract PPC64LE.abi 28 Spec.Sha256.sha224 (96 + frameBytes hash)) :=
  digestFrame digestScratch (by decide) (by
    inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, Spec.Hmac.sha224S,
      Spec.Hmac.sha224, PPC64LE.abi, PPC64LE.argRegs]
      using digestSat 28 0)

end Sha224

namespace Sha256

open VG.Proof.Hmac.Stream.PPC64LE.Sha256 (hash ok)

theorem digest_ct : ConstantTime isa (digestG ok.SH hash.lbytes 96).pre (digestG ok.SH hash.lbytes 96).pub
    (digest hash) :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => agree hp) (by taint_decide)

theorem digestScratch : Verified PPC64LE.target (digest hash) (digestScratchContract ok.SH (hash.lbytes / 8)) :=
  MdStream.PPC64LE.Digest.digestScratch ok (by decide) digest_ct (by
    inst_sat [digestScratchContract, digestScratchSig, Spec.Sha256.digestPost, Spec.Hmac.sha256S, Spec.Hmac.sha256,
      PPC64LE.abi, PPC64LE.argRegs]
      using digestSat 32 hash.lbytes)

theorem verified : Verified PPC64LE.target (code hash)
    (Spec.Sha256.digestContract PPC64LE.abi 32 Spec.Sha256.hash (96 + frameBytes hash)) :=
  digestFrame digestScratch (by decide) (by
    inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, Spec.Hmac.sha256S,
      Spec.Hmac.sha256, PPC64LE.abi, PPC64LE.argRegs]
      using digestSat 32 0)

end Sha256

end VG.Proof.Sha256.PPC64LE.Digest
