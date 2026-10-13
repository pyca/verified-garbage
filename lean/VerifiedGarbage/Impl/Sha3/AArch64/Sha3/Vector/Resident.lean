module

public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.ResidentCore
public import VerifiedGarbage.Impl.Sha3.AArch64.Stream

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64
open VG.Impl.Sha3.AArch64 (mov Callee)

/-- An optional absorber for a fully proved permutation backend: `whole`
absorbs whole blocks, entered at an aligned position with at least one.
Nonaligned input uses that backend's ordinary streaming implementation. -/
def bulkPrefixWith (whole : Prog isa) : Prog isa :=
  .ite (.zero .x .x2)
    (.seq (.block (mov .x6 .x1 :: test))
      (.ite (.zero .x .x7)
        (.seq (.block [mov .x1 .x5])
          (.seq whole (.block [mov .x1 .x6])))
        (.block [])))
    (.block [])

/-- Absorb, with the whole blocks absorbed by `whole`. -/
def absorbWith (whole : Prog isa) (c : Callee) : Prog isa :=
  .seq (bulkPrefixWith whole) (Stream.absorbGenericWith c)

def bulkPrefix : Prog isa := bulkPrefixWith bulk

def absorb (c : Callee) : Prog isa := absorbWith bulk c

end VG.Impl.Sha3.AArch64.Sha3.Vector.Resident
