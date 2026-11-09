module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Message

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Optimized
open VG.AArch64
open VG.Impl.MlDsa.AArch64.Message

/-- The arguments the cached verifier saves, with the digest `tr` (`x7`) in
the slot of `rnd`. -/
def cachedVerifySaves : List (Reg × Nat) :=
  [(.x0, fKey), (.x1, fMsg), (.x2, fLen), (.x3, fCtx), (.x4, fCtxLen), (.x7, fRnd), (.x5, fSig), (.x6, fScr)]

/-- Private cached verifier. The eighth argument is saved in the message
frame's otherwise unused randomness slot. Its contract requires the digest
to equal SHAKE256 of the public key; raw verification remains separate. -/
def verifyMessageCached (c : Impl.Sha3.AArch64.Callee) (name : String)
    (verify : Prog isa) (p : Spec.MlDsa.Params) : Prog isa :=
  top (enter .x6 p cachedVerifySaves)
    (.seq (muHash c (.slot fRnd))
      (callA name verify [(.x0, .slot fKey), (.x1, .off oMU),
        (.x2, .slot fSig), (.x3, .slot fScr)]))

end VG.Impl.MlDsa.AArch64.Optimized
