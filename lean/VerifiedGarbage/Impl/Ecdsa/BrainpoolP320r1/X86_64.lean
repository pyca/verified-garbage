module

public import VerifiedGarbage.Impl.Ecdsa.X86_64.CombGeneral
public import VerifiedGarbage.Impl.BrainpoolP320r1.CombTable7

/-! # brainpoolP320r1 on x86-64

ECDH, verification and the public key multiply by `vg_brainpoolp320r1_mul`,
the ladder of complete additions (`Cfg.mulFn`). The signature computes `[k]G`
by the fixed-base comb of 7-bit digits from the tables of
`Impl/BrainpoolP320r1/CombTable7.lean` (checked by `Proof/BrainpoolP320r1/Comb7.lean`), its
additions the complete ones for any `a` (`Cfg.signG`): 46 additions rather
than the ladder's 320 doublings and additions. -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86_64

open VG.X86_64

def brainpoolp320r1 : Cfg where
  n := 5
  C := Spec.BrainpoolP320r1.curve
  fastN := true
  windows := false
  mul := some Impl.Weierstrass.Mul.brainpoolp320r1
  inverse := some Impl.Weierstrass.Inverse.brainpoolp320r1
  checkPoint := some Impl.Weierstrass.CheckPoint.brainpoolp320r1

/-- The comb's tables: `[m 2^(7j)]G` for `m = 1 … 64`, `j < 46`. -/
def brainpoolp320r1Comb : CombData :=
  { w := 7, tbl := Impl.BrainpoolP320r1.comb7, start := Impl.BrainpoolP320r1.comb7Start,
    tsym := "VG_BRAINPOOLP320R1_COMB" }

/-- The signature's configuration: `brainpoolp320r1`, with the comb's tables
declared (`gtab`, which `Cfg.combConsts` lists). -/
def brainpoolp320r1S : Cfg := { brainpoolp320r1 with gtab := some brainpoolp320r1Comb }

/-- `vg_ecdsa_brainpoolp320r1_sign`, its `[k]G` by the comb (`Cfg.signG`). -/
def signBrainpoolP320r1 : Prog isa := brainpoolp320r1S.signG brainpoolp320r1Comb

end VG.Impl.Ecdsa.X86_64
