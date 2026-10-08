import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.P256.EcdhJac
import VerifiedGarbage.Impl.Ecdh.AArch64.WithMul

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64

def before : Prog isa := Impl.Ecdh.AArch64.Cfg.beforeMul Impl.Ecdsa.AArch64.p256
def mq : Prog isa := .seq Impl.P256.EcdhJac.prep Impl.P256.EcdhJac.wrappedWindow
def multiply : Prog isa := .seq mq Impl.Ecdsa.AArch64.p256.pPow
def finish : Prog isa := Impl.Ecdh.AArch64.Cfg.middle Impl.Ecdsa.AArch64.p256
end VG.Proof.P256.EcdhJac
namespace VG
materialize_code Impl.P256.EcdhJac.exchange
materialize_code Proof.P256.EcdhJac.before
materialize_code Proof.P256.EcdhJac.multiply
materialize_code Proof.P256.EcdhJac.finish
end VG
