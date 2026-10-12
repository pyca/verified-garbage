module

public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.TCB.Artifact

/-! Trusted word selection contract. FFDH composes this and the existing
verified Montgomery primitive; Rust owns the schedule and domain checks. -/

@[expose] public section
namespace VG.Spec.Ffdh

def chooseSig : Sig where
  params := [("a", .int .u64 false), ("b", .int .u64 false), ("bit", .int .u64 false)]
  ret := some .u64

def chooseContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  chooseSig.contract A (post := fun a b bit m m' r => r = choose a b bit ∧ m' = m) (stack := stack)

def chooseApi : Api where
  module := "ffdh"
  name := "vg_ffdh_choose"
  sig := chooseSig
  contracts := some fun A stack => chooseContract A stack
  summary := "Returns `a` when the low bit of `bit` is zero and `b` otherwise. \
    Writes no memory. Contract: `VG.Spec.Ffdh.chooseContract`. Constant time: \
    none of the argument values may affect timing."
  safety := []
end VG.Spec.Ffdh
