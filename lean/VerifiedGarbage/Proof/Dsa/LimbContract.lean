module
-- separate module: the contracts moved out of `Spec/Dsa/Limb.lean` and `Spec/Dsa/Contract.lean`, beside the other DSA contracts

public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# DSA big-integer arithmetic: 64-bit limb primitives

Not trusted: contracts that no `Api` has, so no Rust function, of building
blocks for a multi-limb Montgomery implementation, not DSA operations on
64-bit domains: the low and high halves of a 128-bit product and a bitwise
selection. All arguments, including the selection mask, are secret. No
memory is accessed and no stack is used.
-/

@[expose] public section

namespace VG.Proof.Dsa.Limb

/-- Low half of the unsigned 128-bit product. -/
def mulLo (a b : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (a.toNat * b.toNat)

/-- High half of the unsigned 128-bit product. -/
def mulHi (a b : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)

/-- Bitwise selection: mask=0 selects a; mask=all-ones selects b.
Other masks select independently in each bit; they are not booleans. -/
def select (a b mask : BitVec 64) : BitVec 64 := a ^^^ ((a ^^^ b) &&& mask)

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

end VG.Proof.Dsa.Limb
