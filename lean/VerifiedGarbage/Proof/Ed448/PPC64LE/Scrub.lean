module

public import VerifiedGarbage.Impl.Ed448.PPC64LE.Fn
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.PublicKeyVerified
public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignVerified
public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.VerifyVerified
public import VerifiedGarbage.Proof.Ed448.Facts
import VerifiedGarbage.Proof.Ed448.WholeLocal
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Ed448 on PPC64LE, without secret residue

`vg_ed448_public_key`, `vg_ed448_sign_cached` and `vg_ed448_verify`, each
followed by `Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.verifiedScrubbedAll`), which
clears the volatile registers and the stack their frames use (240, 624 and
352 bytes). The postconditions of `public_key` and `sign_cached` read the
memory on return only within their outputs, and that of `verify` not at
all (`PPC64LE.Scrub.PostOut`), by RISC-V's proofs
(`Proof/Ed448/RISCV64/Scrub.lean`). `verifiedScrubbedAll`'s side condition
(`scrubSide`) is proved at each theorem, by the kernel's evaluation of
it when this module is built.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub
open VG.Proof.Ed448.WholeLocal (bytesAt_congr)

/-! ## Postconditions -/

variable (cs : List (String × List (BitVec 64))) (stack : Nat)

theorem publicKeyOut :
    PostOut (Spec.Ed448.publicKeyContract (PPC64LE.abi.withConsts cs) stack)
      (Spec.Ed448.publicKeySig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, sd, sc], _ =>
      simp only [Spec.Ed448.publicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Ed448.bytesAt m₂ o 57 = _
      rw [bytesAt_congr hb.1]
      exact h

theorem signCachedOut :
    PostOut (Spec.Ed448.signCachedContract (PPC64LE.abi.withConsts cs) stack)
      (Spec.Ed448.signCachedSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, sd, pk, ctx, cl, msg, len, sc], _ =>
      simp only [Spec.Ed448.signCachedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Ed448.bytesAt m₂ o 114 = _
      rw [bytesAt_congr hb.1]
      exact h

theorem verifyOut :
    PostOut (Spec.Ed448.verifyContract (PPC64LE.abi.withConsts cs) stack)
      (Spec.Ed448.verifySig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _, _, _], _ => exact h

/-! ## The functions as emitted -/

/-- `vg_ed448_public_key` as emitted (`Impl.Ed448.PPC64LE.Fn.publicKey`) meets its
contract in constant time and returns without secret residue. -/
theorem publicKey_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Ed448.PPC64LE.Fn.publicKey
      (Spec.Ed448.publicKeyContract PPC64LE.abi (48 + 192)) 0 :=
  verifiedScrubbedAll (api := Spec.Ed448.publicKeyApi) {
      code := Impl.Ed448.PPC64LE.Whole.publicKeyCode
      verified := Proof.Ed448.PPC64LE.Whole.publicKey_framed Proof.Ed448.baseLadder2_ok }
    240 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (publicKeyOut [] _)
    (by dsimp only; lit_decide)

/-- `vg_ed448_sign_cached` as emitted (`Impl.Ed448.PPC64LE.Fn.signCached`) meets
its contract in constant time and returns without secret residue. -/
theorem signCached_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Ed448.PPC64LE.Fn.signCached
      (Spec.Ed448.signCachedContract PPC64LE.abi (48 + 576)) 0 :=
  verifiedScrubbedAll (api := Spec.Ed448.signCachedApi) {
      code := Impl.Ed448.PPC64LE.Whole.signCachedCode
      verified := Proof.Ed448.PPC64LE.Whole.signCached_framed Proof.Ed448.baseLadder2_ok }
    624 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (signCachedOut [] _)
    (by dsimp only; lit_decide)

/-- `vg_ed448_verify` as emitted (`Impl.Ed448.PPC64LE.Fn.verify`) meets its
contract in constant time and returns without secret residue. -/
theorem verify_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Ed448.PPC64LE.Fn.verify
      (Spec.Ed448.verifyContract PPC64LE.abi (48 + 304)) 32 :=
  verifiedScrubbedAll (api := Spec.Ed448.verifyApi) {
      code := Impl.Ed448.PPC64LE.Whole.verifyCode
      verified := Proof.Ed448.PPC64LE.Whole.verify_framed Proof.Ed448.recover_ok }
    352 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (verifyOut [] _)
    (by dsimp only; lit_decide)

end VG.Proof.Ed448.PPC64LE.Scrub
