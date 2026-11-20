module

public import VerifiedGarbage.Proof.Ed448.X86.ScalarBaseOk
public import VerifiedGarbage.Proof.Ed448.X86.VerifyEquationOk
public import VerifiedGarbage.Proof.Ed448.X86.PublicKey.Verified
public import VerifiedGarbage.Proof.Ed448.X86.SignCached.Verified
public import VerifiedGarbage.Proof.Ed448.X86.Verify.Verified
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.Ed448.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.WholeLocal
import VerifiedGarbage.Proof.Ed448.X86.BaseLit
import VerifiedGarbage.Proof.Ed448.X86.ScalarLit
import VerifiedGarbage.Proof.Ed448.X86.VerifyLit
import VerifiedGarbage.Proof.Sha3.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Ed448.X86.ScalarBaseOk
meta import VerifiedGarbage.Proof.Ed448.X86.VerifyEquationOk
meta import VerifiedGarbage.Proof.Ed448.X86.PublicKey.Verified
meta import VerifiedGarbage.Proof.Ed448.X86.SignCached.Verified
meta import VerifiedGarbage.Proof.Ed448.X86.Verify.Verified
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.Ed448.X86.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Ed448.Contract
meta import VerifiedGarbage.Proof.Ed448.WholeLocal
meta import VerifiedGarbage.Proof.Ed448.X86.BaseLit
meta import VerifiedGarbage.Proof.Ed448.X86.ScalarLit
meta import VerifiedGarbage.Proof.Ed448.X86.VerifyLit
meta import VerifiedGarbage.Proof.Sha3.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# Ed448 on x86 (32-bit), without secret residue

`vg_ed448_public_key`, `vg_ed448_sign_cached` and `vg_ed448_verify` keep
their working space in frames of their own and call the Keccak sponge and
the scalar and point functions: each, as emitted (`Impl.Ed448.X86.Fn`),
zeroes the stack it and its callees use and then clears the registers a
callee may change (`X86.Scrub.verifiedScrubbedF`), given that the postconditions of the public key and the
signature read the memory on return only within their outputs, and that of
the verification not at all (as RISC-V's `Proof/Ed448/RISCV64/Scrub.lean`
proves them).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86.Scrub

open VG.X86 VG.X86.Scrub
open VG.Proof.Ed448.WholeLocal (bytesAt_congr)

variable (stack : Nat)

theorem publicKeyOut :
    PostOut (Spec.Ed448.publicKeyContract X86.abi stack) (Spec.Ed448.publicKeySig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, sd, sc], _ =>
      simp only [Spec.Ed448.publicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Ed448.bytesAt m₂ o 57 = _
      rw [bytesAt_congr hb.1]
      exact h

theorem signCachedOut :
    PostOut (Spec.Ed448.signCachedContract X86.abi stack) (Spec.Ed448.signCachedSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, sd, pk, ctx, cl, msg, len, sc], _ =>
      simp only [Spec.Ed448.signCachedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Ed448.bytesAt m₂ o 114 = _
      rw [bytesAt_congr hb.1]
      exact h

theorem verifyOut :
    PostOut (Spec.Ed448.verifyContract X86.abi stack) (Spec.Ed448.verifySig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _, _, _], _ => exact h

/-- `vg_ed448_public_key`. -/
theorem publicKey_scrubbed :
    VerifiedScrubbed target Impl.Ed448.X86.Fn.publicKey
      (Spec.Ed448.publicKeyContract X86.abi 280) 0 :=
  verifiedScrubbedF (api := Spec.Ed448.publicKeyApi)
    { code := Impl.Ed448.X86.PublicKey.code Impl.Ed448.X86.scalarBase
      verified := PublicKey.publicKey_verified scalarBase_calleeOk }
    (publicKeyOut _)

/-- `vg_ed448_sign_cached`. -/
theorem signCached_scrubbed :
    VerifiedScrubbed target Impl.Ed448.X86.Fn.signCached
      (Spec.Ed448.signCachedContract X86.abi 280) 0 :=
  verifiedScrubbedF (api := Spec.Ed448.signCachedApi)
    { code := Impl.Ed448.X86.SignCached.code Impl.Ed448.X86.scalarBase
      verified := SignCached.signCached_verified scalarBase_calleeOk }
    (signCachedOut _)

/-- `vg_ed448_verify`. -/
theorem verify_scrubbed :
    VerifiedScrubbed target Impl.Ed448.X86.Fn.verify
      (Spec.Ed448.verifyContract X86.abi 280) 32 :=
  verifiedScrubbedF (api := Spec.Ed448.verifyApi)
    { code := Impl.Ed448.X86.Verify.code Impl.Ed448.X86.verifyEquation
      verified := Verify.verify_verified verifyEquation_calleeOk }
    (verifyOut _)

end VG.Proof.Ed448.X86.Scrub
