module

public import VerifiedGarbage.Impl.Ecdsa.X86_64.CombGeneral
public import VerifiedGarbage.Impl.BrainpoolP256r1.CombTable7

/-! # brainpoolP256r1 on x86-64

ECDH, verification and the public key multiply by `vg_brainpoolp256r1_mul`,
the ladder of complete additions (`Cfg.mulFn`). The signature computes `[k]G`
by the fixed-base comb of 7-bit digits from the tables of
`Impl/BrainpoolP256r1/CombTable7.lean` (AArch64's, ARMv7's and RISC-V's), its
additions the complete ones for any `a` (`Cfg.signG`): 37 additions rather
than the ladder's 256 doublings and additions. -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86_64

open VG.X86_64

def brainpoolp256r1 : Cfg where
  n := 4
  C := Spec.BrainpoolP256r1.curve
  fastN := true
  windows := false
  mul := some Impl.Weierstrass.Mul.brainpoolp256r1
  inverse := some Impl.Weierstrass.Inverse.brainpoolp256r1
  checkPoint := some Impl.Weierstrass.CheckPoint.brainpoolp256r1

/-- The comb's tables: `[m 2^(7j)]G` for `m = 1 … 64`, `j < 37`. -/
def brainpoolp256r1Comb : CombData :=
  { w := 7, tbl := Impl.BrainpoolP256r1.comb7, start := Impl.BrainpoolP256r1.comb7Start,
    tsym := "VG_BRAINPOOLP256R1_COMB" }

/-- The signature's configuration: `brainpoolp256r1`, with the comb's tables
declared (`gtab`, which `Cfg.combConsts` lists). -/
def brainpoolp256r1S : Cfg := { brainpoolp256r1 with gtab := some brainpoolp256r1Comb }

/-- `vg_ecdsa_brainpoolp256r1_sign`, its `[k]G` by the comb (`Cfg.signG`). -/
def signBrainpoolP256r1 : Prog isa := brainpoolp256r1S.signG brainpoolp256r1Comb

end VG.Impl.Ecdsa.X86_64
