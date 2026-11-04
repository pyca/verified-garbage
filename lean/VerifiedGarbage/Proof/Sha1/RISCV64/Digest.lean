module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha1
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha1
public import VerifiedGarbage.Proof.MdStream.RISCV64.Digest
meta import VerifiedGarbage.Proof.MdStream.RISCV64.Digest

/-!
# The one-shot SHA-1 digest on RISC-V

The one-shot digest over any streaming hash function
(`Impl/MdStream/RISCV64/Digest.lean`) for SHA-1's streaming functions, as HMAC's code calls them:
its constant time, which the kernel checks, and the contracts of `Spec.Sha1.digestApi`.
-/

@[expose] public section

namespace VG.Proof.Sha1.RISCV64.Digest

open VG.RISCV64
open VG.Proof.MdStream.RISCV64.Digest
open VG.Impl.MdStream.RISCV64.Digest (digest dbytes)

open VG.Proof.Hmac.Stream.RISCV64.Sha1 (hash ok)

theorem digest_ct : ConstantTime isa (digestG ok.SH (dbytes hash + hash.F)).pre
    (digestG ok.SH (dbytes hash + hash.F)).pub (digest hash) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ hp => agree hp) (by taint_decide)

theorem verified : Verified RISCV64.target (digest hash) (Spec.Sha1.digestContract RISCV64.abi (dbytes hash + hash.F)) :=
  MdStream.RISCV64.Digest.verified ok digest_ct (by
    inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, Spec.Hmac.sha1S,
      Spec.Hmac.sha1, dbytes, Impl.MdStream.RISCV64.Digest.dso, RISCV64.abi, RISCV64.argRegs]
      using digestSat 20)

end VG.Proof.Sha1.RISCV64.Digest
