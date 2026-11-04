module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256Family
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256Family
public import VerifiedGarbage.Proof.MdStream.RISCV64.Digest
meta import VerifiedGarbage.Proof.MdStream.RISCV64.Digest

/-!
# The one-shot SHA-224 and SHA-256 digests on RISC-V

The one-shot digest over any streaming hash function
(`Impl/MdStream/RISCV64/Digest.lean`) for SHA-224's and SHA-256's streaming functions, as HMAC's code calls them:
its constant time, which the kernel checks, and the contracts of `Spec.Sha256.digest224Api` and
`digest256Api`.
-/

@[expose] public section

namespace VG.Proof.Sha256.RISCV64.Digest

open VG.RISCV64
open VG.Proof.MdStream.RISCV64.Digest
open VG.Impl.MdStream.RISCV64.Digest (digest dbytes)

namespace Sha224

open VG.Proof.Hmac.Stream.RISCV64.Sha256Family (hash224 ok224)

theorem digest_ct : ConstantTime isa (digestG ok224.SH (dbytes hash224 + hash224.F)).pre
    (digestG ok224.SH (dbytes hash224 + hash224.F)).pub (digest hash224) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ hp => agree hp) (by taint_decide)

theorem verified : Verified RISCV64.target (digest hash224) (Spec.Sha256.digestContract RISCV64.abi 28 Spec.Sha256.sha224 (dbytes hash224 + hash224.F)) :=
  MdStream.RISCV64.Digest.verified ok224 digest_ct (by
    inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, Spec.Hmac.sha224S,
      Spec.Hmac.sha224, dbytes, Impl.MdStream.RISCV64.Digest.dso, RISCV64.abi, RISCV64.argRegs]
      using digestSat 28)

end Sha224

namespace Sha256

open VG.Proof.Hmac.Stream.RISCV64.Sha256Family (hash256 ok256)

theorem digest_ct : ConstantTime isa (digestG ok256.SH (dbytes hash256 + hash256.F)).pre
    (digestG ok256.SH (dbytes hash256 + hash256.F)).pub (digest hash256) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ hp => agree hp) (by taint_decide)

theorem verified : Verified RISCV64.target (digest hash256) (Spec.Sha256.digestContract RISCV64.abi 32 Spec.Sha256.hash (dbytes hash256 + hash256.F)) :=
  MdStream.RISCV64.Digest.verified ok256 digest_ct (by
    inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, Spec.Hmac.sha256S,
      Spec.Hmac.sha256, dbytes, Impl.MdStream.RISCV64.Digest.dso, RISCV64.abi, RISCV64.argRegs]
      using digestSat 32)

end Sha256

end VG.Proof.Sha256.RISCV64.Digest
