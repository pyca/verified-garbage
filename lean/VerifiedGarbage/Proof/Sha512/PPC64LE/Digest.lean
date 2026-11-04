module

import VerifiedGarbage.Proof.Sha512.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Sha512.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha384
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_224
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_256
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha384
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_224
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_256
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Digest
meta import VerifiedGarbage.Proof.MdStream.PPC64LE.Digest

/-!
# The one-shot SHA-384, SHA-512, SHA-512/224 and SHA-512/256 digests on PPC64LE

The one-shot digest over any streaming hash function
(`Impl/MdStream/PPC64LE/Digest.lean`) for the SHA-512 family's streaming functions, as HMAC's code calls them
(`Proof.Hmac.Stream.PPC64LE.Sha384.hash`, …): its constant time, which the kernel checks, and the contracts of
`Spec.Sha512.digest384Api`, `digest512Api`,
`digest512_224Api` and `digest512_256Api`.
-/

@[expose] public section

namespace VG.Proof.Sha512.PPC64LE.Digest

open VG.PPC64LE
open VG.Proof.MdStream.PPC64LE.Digest
open VG.Impl.MdStream.PPC64LE.Digest (digest code frameBytes)

namespace Sha384

open VG.Proof.Hmac.Stream.PPC64LE.Sha384 (hash ok)

theorem digest_ct : ConstantTime isa (digestG ok.SH hash.lbytes 96).pre (digestG ok.SH hash.lbytes 96).pub
    (digest hash) :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => agree hp) (by taint_decide)

theorem digestScratch : Verified PPC64LE.target (digest hash) (digestScratchContract ok.SH (hash.lbytes / 8)) :=
  MdStream.PPC64LE.Digest.digestScratch ok (by decide) digest_ct (by
    inst_sat [digestScratchContract, digestScratchSig, Spec.Sha256.digestPost, Spec.Hmac.sha384S, Spec.Hmac.sha384,
      PPC64LE.abi, PPC64LE.argRegs]
      using digestSat 48 hash.lbytes)

theorem verified : Verified PPC64LE.target (code hash)
    (Spec.Sha512.digestContract PPC64LE.abi 48 Spec.Sha512.sha384 (96 + frameBytes hash)) :=
  digestFrame digestScratch (by decide) (by
    inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, Spec.Hmac.sha384S,
      Spec.Hmac.sha384, PPC64LE.abi, PPC64LE.argRegs]
      using digestSat 48 0)

end Sha384

namespace Sha512

open VG.Proof.Hmac.Stream.PPC64LE.Sha512 (hash ok)

theorem digest_ct : ConstantTime isa (digestG ok.SH hash.lbytes 96).pre (digestG ok.SH hash.lbytes 96).pub
    (digest hash) :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => agree hp) (by taint_decide)

theorem digestScratch : Verified PPC64LE.target (digest hash) (digestScratchContract ok.SH (hash.lbytes / 8)) :=
  MdStream.PPC64LE.Digest.digestScratch ok (by decide) digest_ct (by
    inst_sat [digestScratchContract, digestScratchSig, Spec.Sha256.digestPost, Spec.Hmac.sha512S, Spec.Hmac.sha512,
      PPC64LE.abi, PPC64LE.argRegs]
      using digestSat 64 hash.lbytes)

theorem verified : Verified PPC64LE.target (code hash)
    (Spec.Sha512.digestContract PPC64LE.abi 64 Spec.Sha512.sha512 (96 + frameBytes hash)) :=
  digestFrame digestScratch (by decide) (by
    inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, Spec.Hmac.sha512S,
      Spec.Hmac.sha512, PPC64LE.abi, PPC64LE.argRegs]
      using digestSat 64 0)

end Sha512

namespace Sha512_224

open VG.Proof.Hmac.Stream.PPC64LE.Sha512_224 (hash ok)

theorem digest_ct : ConstantTime isa (digestG ok.SH hash.lbytes 96).pre (digestG ok.SH hash.lbytes 96).pub
    (digest hash) :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => agree hp) (by taint_decide)

theorem digestScratch : Verified PPC64LE.target (digest hash) (digestScratchContract ok.SH (hash.lbytes / 8)) :=
  MdStream.PPC64LE.Digest.digestScratch ok (by decide) digest_ct (by
    inst_sat [digestScratchContract, digestScratchSig, Spec.Sha256.digestPost, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224,
      PPC64LE.abi, PPC64LE.argRegs]
      using digestSat 28 hash.lbytes)

theorem verified : Verified PPC64LE.target (code hash)
    (Spec.Sha512.digestContract PPC64LE.abi 28 Spec.Sha512.sha512_224 (96 + frameBytes hash)) :=
  digestFrame digestScratch (by decide) (by
    inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, Spec.Hmac.sha512_224S,
      Spec.Hmac.sha512_224, PPC64LE.abi, PPC64LE.argRegs]
      using digestSat 28 0)

end Sha512_224

namespace Sha512_256

open VG.Proof.Hmac.Stream.PPC64LE.Sha512_256 (hash ok)

theorem digest_ct : ConstantTime isa (digestG ok.SH hash.lbytes 96).pre (digestG ok.SH hash.lbytes 96).pub
    (digest hash) :=
  VG.Taint.constantTime (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => agree hp) (by taint_decide)

theorem digestScratch : Verified PPC64LE.target (digest hash) (digestScratchContract ok.SH (hash.lbytes / 8)) :=
  MdStream.PPC64LE.Digest.digestScratch ok (by decide) digest_ct (by
    inst_sat [digestScratchContract, digestScratchSig, Spec.Sha256.digestPost, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256,
      PPC64LE.abi, PPC64LE.argRegs]
      using digestSat 32 hash.lbytes)

theorem verified : Verified PPC64LE.target (code hash)
    (Spec.Sha512.digestContract PPC64LE.abi 32 Spec.Sha512.sha512_256 (96 + frameBytes hash)) :=
  digestFrame digestScratch (by decide) (by
    inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, Spec.Hmac.sha512_256S,
      Spec.Hmac.sha512_256, PPC64LE.abi, PPC64LE.argRegs]
      using digestSat 32 0)

end Sha512_256

end VG.Proof.Sha512.PPC64LE.Digest
