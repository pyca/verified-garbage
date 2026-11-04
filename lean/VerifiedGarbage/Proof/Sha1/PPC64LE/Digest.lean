module

public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha1
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha1
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Digest
meta import VerifiedGarbage.Proof.MdStream.PPC64LE.Digest

/-!
# The one-shot SHA-1 digest on PPC64LE

The one-shot digest over any streaming hash function
(`Impl/MdStream/PPC64LE/Digest.lean`) for SHA-1's streaming functions, as HMAC's code calls them
(`Proof.Hmac.Stream.PPC64LE.Sha1.hash`): its constant time, which the kernel checks, and the contracts of
`Spec.Sha1.digestApi`.
-/

@[expose] public section

namespace VG.Proof.Sha1.PPC64LE.Digest

open VG.PPC64LE
open VG.Proof.MdStream.PPC64LE.Digest
open VG.Impl.MdStream.PPC64LE.Digest (digest code frameBytes)

open VG.Proof.Hmac.Stream.PPC64LE.Sha1 (hash ok)

theorem digest_ct : ConstantTime isa (digestG ok.SH hash.lbytes 96).pre (digestG ok.SH hash.lbytes 96).pub
    (digest hash) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ hp => agree hp) (by taint_decide)

theorem digestScratch : Verified PPC64LE.target (digest hash) (digestScratchContract ok.SH (hash.lbytes / 8)) :=
  MdStream.PPC64LE.Digest.digestScratch ok (by decide) digest_ct (by
    inst_sat [digestScratchContract, digestScratchSig, Spec.Sha256.digestPost, Spec.Hmac.sha1S, Spec.Hmac.sha1,
      PPC64LE.abi, PPC64LE.argRegs]
      using digestSat 20 hash.lbytes)

theorem verified : Verified PPC64LE.target (code hash) (Spec.Sha1.digestContract PPC64LE.abi (96 + frameBytes hash)) :=
  digestFrame digestScratch (by decide) (by
    inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, Spec.Hmac.sha1S,
      Spec.Hmac.sha1, PPC64LE.abi, PPC64LE.argRegs]
      using digestSat 20 0)

end VG.Proof.Sha1.PPC64LE.Digest
