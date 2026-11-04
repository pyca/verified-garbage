module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256Family
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256Family
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Shared
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Shared
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash
public import VerifiedGarbage.Proof.MdStream.RISCV64.Digest
meta import VerifiedGarbage.Proof.MdStream.RISCV64.Digest

/-!
# HMAC-SHA-224 on RISC-V

The constant time of HMAC's code over any streaming hash function for
SHA-224's streaming functions (`Sha256Family.hash224`), which the kernel
checks, and the functions against the shared contracts of
`Spec.Hmac.sha224I`.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.RISCV64.Sha224

open VG.RISCV64
open Sha256Family (hash224 ok224)

theorem init_ct : ConstantTime isa (initG ok224.SH (hash224.ibytes + hash224.F)).pre
    (initG ok224.SH (hash224.ibytes + hash224.F)).pub hash224.init :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

theorem fin_ct : ConstantTime isa (finG ok224.SH (hash224.fbytes + hash224.F)).pre
    (finG ok224.SH (hash224.fbytes + hash224.F)).pub hash224.finalize :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

theorem init : Verified RISCV64.target hash224.init
    (Spec.Hmac.sha224I.initAnyKeyContract RISCV64.abi (hash224.ibytes + hash224.F)) :=
  Shared.init ok224 rfl init_ct (by
    inst_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, Hash.ibytes, Hash.iso, RISCV64.abi,
      RISCV64.argRegs]
      using Shared.initSat 96)

theorem finalize : Verified RISCV64.target hash224.finalize
    (Spec.Hmac.sha224I.finalizeContract RISCV64.abi (hash224.fbytes + hash224.F)) :=
  Shared.finalize ok224 rfl fin_ct (by
    inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, Hash.fbytes, Hash.fso, RISCV64.abi,
      RISCV64.argRegs]
      using Shared.finSat 96 28)


/-! ## The one-shot digest

The one-shot digest over any streaming hash function
(`Impl/MdStream/RISCV64/Digest.lean`) for these streaming functions: its
constant time, which the kernel checks, and its contract. -/

theorem digest_ct : ConstantTime isa (MdStream.RISCV64.Digest.digestG ok224.SH (Impl.MdStream.RISCV64.Digest.dbytes hash224 + hash224.F)).pre
    (MdStream.RISCV64.Digest.digestG ok224.SH (Impl.MdStream.RISCV64.Digest.dbytes hash224 + hash224.F)).pub (Impl.MdStream.RISCV64.Digest.digest hash224) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ hp => MdStream.RISCV64.Digest.agree hp) (by taint_decide)

theorem digest : Verified RISCV64.target (Impl.MdStream.RISCV64.Digest.digest hash224) (Spec.Sha256.digestContract RISCV64.abi 28 Spec.Sha256.sha224 (Impl.MdStream.RISCV64.Digest.dbytes hash224 + hash224.F)) :=
  MdStream.RISCV64.Digest.verified ok224 digest_ct (by
    inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, Spec.Hmac.sha224S,
      Spec.Hmac.sha224, Impl.MdStream.RISCV64.Digest.dbytes, Impl.MdStream.RISCV64.Digest.dso, RISCV64.abi, RISCV64.argRegs]
      using MdStream.RISCV64.Digest.digestSat 28)

end VG.Proof.Hmac.Stream.RISCV64.Sha224
