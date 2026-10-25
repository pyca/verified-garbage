module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256Family
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256Family
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Shared
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Shared
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash

/-!
# HMAC-SHA-256 on RISC-V

The constant time of HMAC's code over any streaming hash function for
SHA-256's streaming functions (`Sha256Family.hash256`), which the kernel
checks, and the functions against the shared contracts of
`Spec.Hmac.sha256I`.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.RISCV64.Sha256

open VG.RISCV64
open Sha256Family (hash256 ok256)

theorem init_ct : ConstantTime isa (initG ok256.SH (hash256.ibytes + hash256.F)).pre
    (initG ok256.SH (hash256.ibytes + hash256.F)).pub hash256.init :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

theorem fin_ct : ConstantTime isa (finG ok256.SH (hash256.fbytes + hash256.F)).pre
    (finG ok256.SH (hash256.fbytes + hash256.F)).pub hash256.finalize :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

theorem init : Verified RISCV64.target hash256.init
    (Spec.Hmac.sha256I.initAnyKeyContract RISCV64.abi (hash256.ibytes + hash256.F)) :=
  Shared.init ok256 rfl init_ct (by
    inst_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, Hash.ibytes, Hash.iso, RISCV64.abi,
      RISCV64.argRegs]
      using Shared.initSat 96)

theorem finalize : Verified RISCV64.target hash256.finalize
    (Spec.Hmac.sha256I.finalizeContract RISCV64.abi (hash256.fbytes + hash256.F)) :=
  Shared.finalize ok256 rfl fin_ct (by
    inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, Hash.fbytes, Hash.fso, RISCV64.abi,
      RISCV64.argRegs]
      using Shared.finSat 96 32)

end VG.Proof.Hmac.Stream.RISCV64.Sha256
