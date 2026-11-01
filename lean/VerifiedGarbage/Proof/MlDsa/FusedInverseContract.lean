module

public import VerifiedGarbage.Proof.MlDsa.Contract

/-!
# ML-DSA: the contract of fused products and inverse transforms

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

Internal fused arithmetic interfaces. Inputs may use positive, noncanonical
representatives below 3q; outputs are canonical ordinary coefficients.
These specifications express composition of the existing field operations.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

/-- The bound produced by the positive forward transform. -/
def PositiveReduced (m : Mem) (p : Addr) : Prop :=
  ∀ i<n, (coeffAt m p i).toNat<3*q

def multiplyInverseSig : Sig where
  params := [("out",.array true .u32 256),("a",.array false .u32 256),
    ("b",.array false .u32 256),("scratch",.array true .u64 128)]

def multiplyInverseContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  multiplyInverseSig.contract A
    (pre := fun _out a b _scratch m => PositiveReduced m a ∧ PositiveReduced m b)
    (post := fun out a b _scratch m m' _ =>
      PolyIs m' out (nttInv (multiplyNTT (polyAt m a) (polyAt m b))))
    (writeArgs := true) (stack := stack)

/-- A matrix row's coefficientwise products accumulated in the NTT domain. -/
def dotNTT (f g : Nat → Poly) (count : Nat) : Poly :=
  ((List.range count).map fun j => multiplyNTT (f j) (g j)).foldl add zero

def dotInverseSig (count : Nat) : Sig where
  params := [("out",.array true .u32 256),("a",.array false .u32 (count*256)),
    ("b",.array false .u32 (count*256)),("scratch",.array true .u64 128)]

def dotInverseContract {M : ISA} (count : Nat) (A : Abi M) (stack : Nat := 0) : Contract M :=
  (dotInverseSig count).contract A
    (pre := fun _out a b _scratch m =>
      (∀ j<count, PositiveReduced m (a+BitVec.ofNat 64 (1024*j))) ∧
      (∀ j<count, PositiveReduced m (b+BitVec.ofNat 64 (1024*j))))
    (post := fun out a b _scratch m m' _ => PolyIs m' out
      (nttInv (dotNTT (fun j => polyAt m (a+BitVec.ofNat 64 (1024*j)))
        (fun j => polyAt m (b+BitVec.ofNat 64 (1024*j))) count)))
    (writeArgs := true) (stack := stack)

end VG.Proof.MlDsa
