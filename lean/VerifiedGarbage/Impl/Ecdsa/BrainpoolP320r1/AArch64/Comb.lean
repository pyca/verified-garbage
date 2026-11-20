module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.AArch64
public import VerifiedGarbage.Impl.BrainpoolP320r1.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombGeneral

/-! # Fixed-base brainpoolP320r1 signing on AArch64

The constant-time comb uses complete general-curve RCB addition. The
selected point's negation scratch holds 3b once selection is complete.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.AArch64.BrainpoolP320r1

open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

def combCfg : Cfg := { brainpoolp320r1 with
  tbl := VG.Impl.BrainpoolP320r1.comb7
  start := VG.Impl.BrainpoolP320r1.comb7Start
  tsym := "VG_BRAINPOOLP320R1_COMB7" }

def b3 : Nat := combCfg.mont (3 * combCfg.C.b)

def comb : Prog isa := combCfg.combCfg.generalComb b3

def signComb : Prog isa := combCfg.signWith comb

end VG.Impl.Ecdsa.AArch64.BrainpoolP320r1
