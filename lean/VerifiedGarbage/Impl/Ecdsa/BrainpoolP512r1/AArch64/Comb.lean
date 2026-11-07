module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.AArch64
public import VerifiedGarbage.Impl.BrainpoolP512r1.CombTable7
public import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombGeneral

/-! # Fixed-base brainpoolP512r1 signing on AArch64

The constant-time comb uses complete general-curve RCB addition. The
selected point's negation scratch holds 3b once selection is complete.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.AArch64.BrainpoolP512r1

open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

def combCfg : Cfg := { brainpoolp512r1 with
  tbl := VG.Impl.BrainpoolP512r1.comb7
  start := VG.Impl.BrainpoolP512r1.comb7Start
  tsym := "VG_BRAINPOOLP512R1_COMB7" }

def b3 : Nat := combCfg.mont (3 * combCfg.C.b)

def comb : Prog isa := combCfg.combCfg.generalComb b3

def signComb : Prog isa := combCfg.signWith comb

end VG.Impl.Ecdsa.AArch64.BrainpoolP512r1
