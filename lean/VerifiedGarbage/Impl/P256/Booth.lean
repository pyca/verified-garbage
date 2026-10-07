import VerifiedGarbage.Impl.P256.CombArithmetic
import VerifiedGarbage.Impl.EcKey.P256.AArch64

/-! The shared secret-scalar Booth comb for P-256 signing and public keys. -/
namespace VG.Impl.P256.Booth
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64

def comb : Prog isa := p256.combCfg.combJWith CombArithmetic.program
def sign : Prog isa := p256.signWith comb
def publicKey : Prog isa := Impl.EcKey.AArch64.Cfg.publicKeyWith p256 comb

end VG.Impl.P256.Booth
