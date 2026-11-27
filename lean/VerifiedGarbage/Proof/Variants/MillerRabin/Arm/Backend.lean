module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.MillerRabin.Arm.Verified
public import VerifiedGarbage.Proof.Bignum.Arm.CallOp
public import VerifiedGarbage.Proof.Framework.Arm.ScrubFill
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall

import VerifiedGarbage.Proof.Framework.Lit

/-!
# The shared Miller–Rabin round on ARMv7, over each Montgomery product

The variant of the round for a Montgomery product `b`
(`Variants/RsaMont/Arm.lean`): each of its products and squares calls `b`'s
(`MontBackend.callOp`), and `b`'s rewriting of its callers
(`MontBackend.caller`) applies to the round, with the proofs its interface
asks for. Its frame (56 bytes) and the product's call (48 bytes below it)
use 104 bytes of stack.
-/

@[expose] public section

namespace VG.Proof.Variants.MillerRabin.Arm.Backend

open VG.Arm VG.Arm.Scrub VG.Arm.ScrubFill VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm VG.Proof.MillerRabin.Arm

theorem roundStub : CodeOk (Impl.MillerRabin.Arm.code (MontCall.op "" (holeStub 40))) 104 := by lit_decide

theorem roundOk (b : MontBackend) :
    CodeOk (b.caller.code (Impl.MillerRabin.Arm.code (MontCall.op b.name b.mul))) 104 :=
  b.callerOk _ _ ((show FillB _ (Impl.MillerRabin.Arm.code (MontCall.op b.name b.mul)) by
    have := b.mulOk; fill_holes).codeOk roundStub)

def variant (b : MontBackend) : RoundImpl where
  code := b.caller.code (Impl.MillerRabin.Arm.code (MontCall.op b.name b.mul))
  verified := b.caller.verified (round_verified_lite b.callOp)
  stack := (roundOk b).1
  icallFree := (roundOk b).2
  mont := b
  suffix := b.suffix
  features := b.features

end VG.Proof.Variants.MillerRabin.Arm.Backend
