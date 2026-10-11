module

public import VerifiedGarbage.Impl.Ecdh.AArch64.WithMul

/-! Windowed ECDH builds its own signed digits, so its setup needs no scalar bit table. -/

@[expose] public section

namespace VG.Impl.P256.EcdhJac.Frontend
open VG VG.AArch64
open VG.Impl.Ecdh.AArch64.Cfg

def before (c : VG.Impl.Ecdsa.AArch64.Cfg) : Prog isa :=
  .seq (.block args) <| .seq (.block (c.setupWith none)) <| .seq (.block (peer c)) (validate c)

def exchange (c : VG.Impl.Ecdsa.AArch64.Cfg) (mq inverse : Prog isa) : Prog isa :=
  .seq (.block args) <| .seq (.block (c.setupWith none)) <| .seq (.block (peer c)) <|
  .seq (validate c) <| .seq mq <| .seq inverse (middle c)
end VG.Impl.P256.EcdhJac.Frontend
