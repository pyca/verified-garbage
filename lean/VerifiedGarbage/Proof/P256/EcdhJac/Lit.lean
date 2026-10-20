module

public import VerifiedGarbage.Impl.P256.EcdhJac
meta import VerifiedGarbage.Impl.P256.EcdhJac
public import VerifiedGarbage.Impl.P256.EcdhJac.Frontend
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.P256.EcdhJac.Frontend
import VerifiedGarbage.Impl.Ecdh.AArch64.WithMul
import VerifiedGarbage.Impl.Ecdh.P256.AArch64
import VerifiedGarbage.Impl.P256.VerifyRegisters
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Spec.Weierstrass.Mul
meta import VerifiedGarbage.Impl.Ecdh.AArch64.WithMul
meta import VerifiedGarbage.Impl.Ecdh.P256.AArch64
meta import VerifiedGarbage.Impl.P256.VerifyRegisters
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Spec.Weierstrass.Mul

@[expose] public section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64

def before : Prog isa := Impl.P256.EcdhJac.Frontend.before Impl.Ecdsa.AArch64.p256
def mq : Prog isa := .seq Impl.P256.EcdhJac.prep Impl.P256.EcdhJac.wrappedWindow
def multiply : Prog isa := .seq mq Impl.P256.EcdhInverse.inverse
def finish : Prog isa := Impl.Ecdh.AArch64.Cfg.middle Impl.Ecdsa.AArch64.p256
end VG.Proof.P256.EcdhJac
namespace VG
materialize_code Impl.P256.EcdhJac.exchange
materialize_code Proof.P256.EcdhJac.before
materialize_code Proof.P256.EcdhJac.multiply
materialize_code Proof.P256.EcdhJac.finish
end VG
