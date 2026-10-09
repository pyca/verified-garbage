import VerifiedGarbage.Impl.MlDsa.AArch64.Message
import VerifiedGarbage.Spec.MlDsa.CachedVerify

namespace VG.Impl.MlDsa.AArch64.Optimized
open VG.AArch64
open VG.Impl.MlDsa.AArch64.Message

def cachedVerifySaves : List (Reg × Nat) :=
  verifySaves.map fun (r, o) => (if o == fRnd then .x7 else r, o)

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
