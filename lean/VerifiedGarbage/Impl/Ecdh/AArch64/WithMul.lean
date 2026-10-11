module

public import VerifiedGarbage.Impl.Ecdh.AArch64

@[expose] public section

namespace VG.Impl.Ecdh.AArch64.Cfg
open VG VG.AArch64

/-- The shared argument setup and validation before scalar multiplication. -/
def beforeMul (c : VG.Impl.Ecdsa.AArch64.Cfg) : Prog isa :=
  .seq (.block args) <| .seq (prefix' c) <| .seq (.block (peer c)) (validate c)

/-- ECDH with a separately specified scalar multiplication. Validation,
fixed-count inversion and final range checks are shared with `exchange`. -/
def exchangeWith (c : VG.Impl.Ecdsa.AArch64.Cfg) (mq : Prog isa) : Prog isa :=
  .seq (.block args) <| .seq (prefix' c) <| .seq (.block (peer c)) <|
  .seq (validate c) <| .seq mq <| .seq c.pPow (middle c)

end VG.Impl.Ecdh.AArch64.Cfg
