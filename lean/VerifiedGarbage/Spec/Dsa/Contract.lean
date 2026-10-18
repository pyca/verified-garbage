module

public import VerifiedGarbage.Spec.Dsa.Limb
public import VerifiedGarbage.TCB.Artifact

/-! # Initial DSA arithmetic contracts (trusted)
All arguments, including the selection mask, are secret. No memory is
accessed and no stack is used. Contracts cover every target; a future registration can supply
an x86-64 baseline implementation. -/

@[expose] public section

namespace VG.Spec.Dsa.Limb

def mulSig : Sig where
  params := [("a", .int .u64 false), ("b", .int .u64 false)]
  ret := some .u64

def mulLoContract {M : ISA} (A : Abi M) : Contract M :=
  mulSig.contract A (post := fun a b m m' r => r = mulLo a b ∧ m' = m)

def mulHiContract {M : ISA} (A : Abi M) : Contract M :=
  mulSig.contract A (post := fun a b m m' r => r = mulHi a b ∧ m' = m)

def selectSig : Sig where
  params := [("a", .int .u64 false), ("b", .int .u64 false), ("mask", .int .u64 false)]
  ret := some .u64

def selectContract {M : ISA} (A : Abi M) : Contract M :=
  selectSig.contract A (post := fun a b mask m m' r => r = select a b mask ∧ m' = m)

end VG.Spec.Dsa.Limb
