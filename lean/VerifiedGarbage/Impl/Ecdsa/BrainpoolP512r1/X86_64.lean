module

public import VerifiedGarbage.Impl.Ecdsa.X86_64.CombGeneral
public import VerifiedGarbage.Impl.BrainpoolP512r1.CombTable7

/-! # brainpoolP512r1 on x86-64

ECDH, verification and the public key multiply by `vg_brainpoolp512r1_mul`,
the ladder of complete additions (`Cfg.mulFn`). The signature computes `[k]G`
by the fixed-base comb of 7-bit digits from the tables of
`Impl/BrainpoolP512r1/CombTable7.lean` (`Proof/BrainpoolP512r1/Comb7.lean`
checks them), its additions the complete ones for any `a` (`Cfg.signG`): 74
additions rather than the ladder's 512 doublings and additions. -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86_64

open VG.X86_64

def brainpoolp512r1 : Cfg where
  n := 8
  C := Spec.BrainpoolP512r1.curve
  fastN := true
  windows := false
  mul := some Impl.Weierstrass.Mul.brainpoolp512r1
  inverse := some Impl.Weierstrass.Inverse.brainpoolp512r1
  checkPoint := some Impl.Weierstrass.CheckPoint.brainpoolp512r1

/-- The comb's tables: `[m 2^(7j)]G` for `m = 1 … 64`, `j < 74`. -/
def brainpoolp512r1Comb : CombData :=
  { w := 7, tbl := Impl.BrainpoolP512r1.comb7, start := Impl.BrainpoolP512r1.comb7Start,
    tsym := "VG_BRAINPOOLP512R1_COMB" }

/-- The signature's configuration: `brainpoolp512r1`, with the comb's tables
declared (`gtab`, which `Cfg.combConsts` lists). -/
def brainpoolp512r1S : Cfg := { brainpoolp512r1 with gtab := some brainpoolp512r1Comb }

/-- `vg_ecdsa_brainpoolp512r1_sign`, its `[k]G` by the comb (`Cfg.signG`). -/
def signBrainpoolP512r1 : Prog isa := brainpoolp512r1S.signG brainpoolp512r1Comb

end VG.Impl.Ecdsa.X86_64
