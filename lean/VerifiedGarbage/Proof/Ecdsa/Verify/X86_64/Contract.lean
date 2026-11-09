module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Tables
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# ECDSA verification over P-256 on x86-64: the contract the proof is written against

The facts of `Proof.Ecdsa.verifyContract Spec.Ecdsa.P256.inst` for x86-64, under the
calling convention with the comb's tables (`Abi.withConsts p256.combConsts`),
by name: `vg_ecdsa_p256_verify(public = rdi, digest = rsi, sig = rdx,
scratch = rcx)`, the result in `eax`, and the tables at the address of the
static `VG_P256_COMB`. This adapter supplies the correctness precondition and postcondition.
The timing proof uses the shared contract directly, including its public
input buffers.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Ecdsa.X86_64 (p256)
open VG.Proof.Ecdsa.X86_64 (TblHeld p256W p256W_length p256_combConsts satMem satMem_held)

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.P256.curve (bytesAt m pk 65) (hashToInt Spec.P256.curve (bytesAt m digest 32)) (bytesAt m sig 64)

end VG.Proof.Ecdsa.Verify.X86_64
