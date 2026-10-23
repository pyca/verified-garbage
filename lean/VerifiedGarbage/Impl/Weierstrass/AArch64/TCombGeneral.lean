module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.TComb

/-! # Fixed-base table comb with general-curve complete addition

After selecting and conditionally negating the entry, the negation scratch
is available for the Montgomery representation of 3b.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.AArch64.TCombCfg

open VG VG.AArch64 VG.Impl.Weierstrass

def generalSum (K : TCombCfg) (b3 : Nat) : Prog isa :=
  .seq (.block (setConst K.M.n K.neg b3))
    (.seq (fprogB K.M (rcb { K.S with b3 := K.neg } K.A K.E K.D))
      (.block (copyPt K.M.n K.A K.D)))

def generalStep (K : TCombCfg) (b3 : Nat) : Prog isa :=
  .seq (.block (decCounter :: K.digit ++ K.select))
    (.seq (.block (negYW K.M K.w K.neg K.zero K.E.y K.bits)) (K.generalSum b3))

def generalComb (K : TCombCfg) (b3 : Nat) : Prog isa :=
  .seq (.block K.init) (.loop (K.generalStep b3) (.nonzero .x .x19))

end VG.Impl.Weierstrass.AArch64.TCombCfg
