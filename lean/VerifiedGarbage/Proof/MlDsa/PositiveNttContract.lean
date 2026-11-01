module

public import VerifiedGarbage.Proof.MlDsa.Contract

/-!
# ML-DSA: the contract of NTTs with positive representatives

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

Separate internal transform contracts. They retain the standard NTT field
value while explicitly allowing positive representatives below three times q.
The canonical `nttContract`, `Reduced`, and `PolyIs` contracts are unchanged.
-/

@[expose] public section

namespace VG.Proof.MlDsa

open VG.Spec VG.Spec.MlDsa

/-- Internal positive representatives, not canonical residues. -/
def PositivePolyIs (m : Mem) (p : Addr) (f : Poly) : Prop :=
  (∀ i<n, (coeffAt m p i).toNat<3*q) ∧ polyAt m p=f

def positiveNttSig : Sig where
  params := [("f",.array true .u32 256)]

def positiveNttContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  positiveNttSig.contract A
    (pre := fun f m => Reduced m f)
    (post := fun f m m' _ => PositivePolyIs m' f (ntt (polyAt m f)))
    (writeArgs := true) (stack := stack)

def positiveNttOutSig : Sig where
  params := [("out",.array true .u32 256),("f",.array false .u32 256)]

/-- Separate source and destination; callers needing exact aliasing use the
in-place helper. No initial destination contents are required. -/
def positiveNttOutContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  positiveNttOutSig.contract A
    (pre := fun _out f m => Reduced m f)
    (post := fun out f m m' _ => PositivePolyIs m' out (ntt (polyAt m f)))
    (writeArgs := true) (stack := stack)

end VG.Proof.MlDsa
