module

public import VerifiedGarbage.Impl.Ecdsa.X86_64.CombGeneral
public import VerifiedGarbage.Impl.BrainpoolP384r1.CombTable7

/-! # brainpoolP384r1 on x86-64

ECDH, verification and the public key multiply by `vg_brainpoolp384r1_mul`,
the ladder of complete additions (`Cfg.mulFn`). The signature computes `[k]G`
by the fixed-base comb of 7-bit digits from the tables of
`Impl/BrainpoolP384r1/CombTable7.lean` (checked by `Proof/BrainpoolP384r1/Comb7.lean`), its
additions the complete ones for any `a` (`Cfg.signG`): 55 additions rather
than the ladder's 384 doublings and additions. -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86_64

open VG.X86_64

def brainpoolp384r1 : Cfg where
  n := 6
  C := Spec.BrainpoolP384r1.curve
  fastN := true
  windows := false
  mul := some Impl.Weierstrass.Mul.brainpoolp384r1
  inverse := some Impl.Weierstrass.Inverse.brainpoolp384r1
  checkPoint := some Impl.Weierstrass.CheckPoint.brainpoolp384r1

/-- The comb's tables: `[m 2^(7j)]G` for `m = 1 … 64`, `j < 55`. -/
def brainpoolp384r1Comb : CombData :=
  { w := 7, tbl := Impl.BrainpoolP384r1.comb7, start := Impl.BrainpoolP384r1.comb7Start,
    tsym := "VG_BRAINPOOLP384R1_COMB" }

/-- The signature's configuration: `brainpoolp384r1`, with the comb's tables
declared (`gtab`, which `Cfg.combConsts` lists). -/
def brainpoolp384r1S : Cfg := { brainpoolp384r1 with gtab := some brainpoolp384r1Comb }

/-- `vg_ecdsa_brainpoolp384r1_sign`, its `[k]G` by the comb (`Cfg.signG`). -/
def signBrainpoolP384r1 : Prog isa := brainpoolp384r1S.signG brainpoolp384r1Comb

end VG.Impl.Ecdsa.X86_64
