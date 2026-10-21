module

public import VerifiedGarbage.Impl.P256.CombArithmetic
public import VerifiedGarbage.Impl.EcKey.AArch64

/-! The shared secret-scalar Booth comb for P-256 signing and public keys:
pipelined (`TCombCfg.combJP`), each window's mixed addition woven with the
next window's selection. -/

@[expose] public section

namespace VG.Impl.P256.Booth
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

/-- The comb's mixed addition, its forwarded field program. -/
def mixed : List Instr :=
  Forward.optimize (fprog CombArithmetic.K.M (maddJ CombArithmetic.K.S CombArithmetic.K.A
    CombArithmetic.K.E CombArithmetic.K.D))

def comb : Prog isa := p256.combCfg.combJP CombArithmetic.program mixed
def sign : Prog isa := p256.signWith comb
def publicKey : Prog isa := Impl.EcKey.AArch64.Cfg.publicKeyWith p256 comb

end VG.Impl.P256.Booth
