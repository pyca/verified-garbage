module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512Family
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512Family
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Shared
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Shared
meta import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Finalize
meta import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Init
public import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Finalize
public import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Init

/-!
# HMAC-SHA-384 on RISC-V

SHA-384's streaming functions (`Sha512Family.hash`), as HMAC's code over any
streaming hash function calls them; the constant time of HMAC's code for
them, which the kernel checks; and the functions against the shared
contracts of `Spec.Hmac.sha384I`.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.RISCV64.Sha384

open VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)

/-- SHA-384's streaming functions. -/
def hash : Hash :=
  Sha512Family.hash Spec.Sha512.H0_384 48 Spec.Sha512.init384Api.name Spec.Sha512.finalize384Api.name
    Impl.Sha512.RISCV64.Stream.finalize384

theorem finSd : sdepth Impl.Sha512.RISCV64.Stream.finalize384 ≤ 208 := by decide +kernel

/-- What the proofs need of them. -/
def ok : HashOK hash :=
  Sha512Family.ok Spec.Sha512.H0_384 48 _ _ _ Spec.Hmac.sha384 rfl ⟨by decide, by decide⟩
    Proof.Sha512.RISCV64.Stream.init384_verified Proof.Sha512.RISCV64.Stream.Finalize.finalize384_verified finSd (fun _ => rfl)

/-! ## Constant time -/

theorem init_ct : ConstantTime isa (initG ok.SH (hash.ibytes + hash.F)).pre
    (initG ok.SH (hash.ibytes + hash.F)).pub hash.init :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

theorem fin_ct : ConstantTime isa (finG ok.SH (hash.fbytes + hash.F)).pre
    (finG ok.SH (hash.fbytes + hash.F)).pub hash.finalize :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ hp => Shared.agree hp) (by taint_decide)

/-! ## The shared contracts -/

theorem init : Verified RISCV64.target hash.init
    (Spec.Hmac.sha384I.initAnyKeyContract RISCV64.abi (hash.ibytes + hash.F)) :=
  Shared.init ok rfl init_ct (by
    inst_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, Hash.ibytes, Hash.iso, RISCV64.abi,
      RISCV64.argRegs]
      using Shared.initSat 192)

theorem finalize : Verified RISCV64.target hash.finalize
    (Spec.Hmac.sha384I.finalizeContract RISCV64.abi (hash.fbytes + hash.F)) :=
  Shared.finalize ok rfl fin_ct (by
    inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, Hash.fbytes, Hash.fso, RISCV64.abi,
      RISCV64.argRegs]
      using Shared.finSat 192 48)

end VG.Proof.Hmac.Stream.RISCV64.Sha384
