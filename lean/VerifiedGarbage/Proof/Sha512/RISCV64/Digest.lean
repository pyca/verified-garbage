module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha384
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha384
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_224
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_224
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_256
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_256
public import VerifiedGarbage.Proof.MdStream.RISCV64.Digest
meta import VerifiedGarbage.Proof.MdStream.RISCV64.Digest

/-!
# The one-shot SHA-384, SHA-512, SHA-512/224 and SHA-512/256 digests on RISC-V

The one-shot digest over any streaming hash function
(`Impl/MdStream/RISCV64/Digest.lean`) for the SHA-512 family's streaming functions, as HMAC's code calls them:
its constant time, which the kernel checks, and the contracts of `Spec.Sha512.digest384Api`,
`digest512Api`, `digest512_224Api` and `digest512_256Api`.
-/

@[expose] public section

namespace VG.Proof.Sha512.RISCV64.Digest

open VG.RISCV64
open VG.Proof.MdStream.RISCV64.Digest
open VG.Impl.MdStream.RISCV64.Digest (digest dbytes)

namespace Sha384

open VG.Proof.Hmac.Stream.RISCV64.Sha384 (hash ok)

theorem digest_ct : ConstantTime isa (digestG ok.SH (dbytes hash + hash.F)).pre
    (digestG ok.SH (dbytes hash + hash.F)).pub (digest hash) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ hp => agree hp) (by taint_decide)

theorem verified : Verified RISCV64.target (digest hash) (Spec.Sha512.digestContract RISCV64.abi 48 Spec.Sha512.sha384 (dbytes hash + hash.F)) :=
  MdStream.RISCV64.Digest.verified ok digest_ct (by
    inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, Spec.Hmac.sha384S,
      Spec.Hmac.sha384, dbytes, Impl.MdStream.RISCV64.Digest.dso, RISCV64.abi, RISCV64.argRegs]
      using digestSat 48)

end Sha384

namespace Sha512

open VG.Proof.Hmac.Stream.RISCV64.Sha512 (hash ok)

theorem digest_ct : ConstantTime isa (digestG ok.SH (dbytes hash + hash.F)).pre
    (digestG ok.SH (dbytes hash + hash.F)).pub (digest hash) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ hp => agree hp) (by taint_decide)

theorem verified : Verified RISCV64.target (digest hash) (Spec.Sha512.digestContract RISCV64.abi 64 Spec.Sha512.sha512 (dbytes hash + hash.F)) :=
  MdStream.RISCV64.Digest.verified ok digest_ct (by
    inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, Spec.Hmac.sha512S,
      Spec.Hmac.sha512, dbytes, Impl.MdStream.RISCV64.Digest.dso, RISCV64.abi, RISCV64.argRegs]
      using digestSat 64)

end Sha512

namespace Sha512_224

open VG.Proof.Hmac.Stream.RISCV64.Sha512_224 (hash ok)

theorem digest_ct : ConstantTime isa (digestG ok.SH (dbytes hash + hash.F)).pre
    (digestG ok.SH (dbytes hash + hash.F)).pub (digest hash) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ hp => agree hp) (by taint_decide)

theorem verified : Verified RISCV64.target (digest hash) (Spec.Sha512.digestContract RISCV64.abi 28 Spec.Sha512.sha512_224 (dbytes hash + hash.F)) :=
  MdStream.RISCV64.Digest.verified ok digest_ct (by
    inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, Spec.Hmac.sha512_224S,
      Spec.Hmac.sha512_224, dbytes, Impl.MdStream.RISCV64.Digest.dso, RISCV64.abi, RISCV64.argRegs]
      using digestSat 28)

end Sha512_224

namespace Sha512_256

open VG.Proof.Hmac.Stream.RISCV64.Sha512_256 (hash ok)

theorem digest_ct : ConstantTime isa (digestG ok.SH (dbytes hash + hash.F)).pre
    (digestG ok.SH (dbytes hash + hash.F)).pub (digest hash) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ hp => agree hp) (by taint_decide)

theorem verified : Verified RISCV64.target (digest hash) (Spec.Sha512.digestContract RISCV64.abi 32 Spec.Sha512.sha512_256 (dbytes hash + hash.F)) :=
  MdStream.RISCV64.Digest.verified ok digest_ct (by
    inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, Spec.Hmac.sha512_256S,
      Spec.Hmac.sha512_256, dbytes, Impl.MdStream.RISCV64.Digest.dso, RISCV64.abi, RISCV64.argRegs]
      using digestSat 32)

end Sha512_256

end VG.Proof.Sha512.RISCV64.Digest
