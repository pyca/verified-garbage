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
# HMAC-SHA-512 on RISC-V

SHA-512's streaming functions (`Sha512Family.hash`), as HMAC's code over any
streaming hash function calls them; the constant time of HMAC's code for
them, which the kernel checks; and the functions against the shared
contracts of `Spec.Hmac.sha512I`.
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.RISCV64.Sha512

open VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)

/-- SHA-512's streaming functions. -/
def hash : Hash :=
  Sha512Family.hash Spec.Sha512.H0_512 64 Spec.Sha512.init512Api.name Spec.Sha512.finalizeApi.name
    Impl.Sha512.RISCV64.Stream.finalize

theorem finSd : sdepth Impl.Sha512.RISCV64.Stream.finalize ≤ 208 := by decide +kernel

/-- What the proofs need of them. -/
def ok : HashOK hash :=
  Sha512Family.ok Spec.Sha512.H0_512 64 _ _ _ Spec.Hmac.sha512 rfl ⟨by decide, by decide⟩
    Proof.Sha512.RISCV64.Stream.init512_verified Proof.Sha512.RISCV64.Stream.Finalize.finalize64_verified finSd (fun x => (List.take_of_length_le (Nat.le_of_eq (Proof.Hmac.Generic.Common.finalHash_length _ x))).symm)

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
    (Spec.Hmac.sha512I.initAnyKeyContract RISCV64.abi (hash.ibytes + hash.F)) :=
  Shared.init ok rfl init_ct (by
    inst_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, Hash.ibytes, Hash.iso, RISCV64.abi,
      RISCV64.argRegs]
      using Shared.initSat 192)

theorem finalize : Verified RISCV64.target hash.finalize
    (Spec.Hmac.sha512I.finalizeContract RISCV64.abi (hash.fbytes + hash.F)) :=
  Shared.finalize ok rfl fin_ct (by
    inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, Hash.fbytes, Hash.fso, RISCV64.abi,
      RISCV64.argRegs]
      using Shared.finSat 192 64)

end VG.Proof.Hmac.Stream.RISCV64.Sha512
