module

public import VerifiedGarbage.Proof.MlDsa.Arith.Montgomery

/-! # The two internal coefficient representations of ML-DSA products

These proof-local contracts express the existing ordinary and Montgomery
contracts uniformly. The public key/signature contracts do not change.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arith.Representation

open VG VG.Spec.MlDsa

def encode (mont : Bool) (f : Poly) : Poly :=
  if mont then Montgomery.scale montgomeryRInv f else f

def product (mont : Bool) (f g : Poly) : Poly := encode mont (multiplyNTT f g)
def accumulate (mont : Bool) (h f g : Poly) : Poly := add h (product mont f g)
def inverse (mont : Bool) (f : Poly) : Poly := if mont then montgomeryNttInv f else nttInv f

def productContract {M : ISA} (mont : Bool) (A : Abi M) (stack : Nat := 0) : Contract M :=
  mulSig.contract A
    (pre := fun _h f g m => Reduced m f ∧ Reduced m g)
    (post := fun h f g m m' _ => PolyIs m' h (product mont (polyAt m f) (polyAt m g)))
    (writeArgs := true) (stack := stack)

def accumulateContract {M : ISA} (mont : Bool) (A : Abi M) (stack : Nat := 0) : Contract M :=
  mulSig.contract A
    (pre := fun h f g m => Reduced m h ∧ Reduced m f ∧ Reduced m g)
    (post := fun h f g m m' _ => PolyIs m' h (accumulate mont (polyAt m h) (polyAt m f) (polyAt m g)))
    (writeArgs := true) (stack := stack)

def inverseContract {M : ISA} (mont : Bool) (A : Abi M) (stack : Nat := 0) : Contract M :=
  inPlaceContract A (inverse mont) stack

theorem inverse_encode (mont : Bool) (f : Poly) : inverse mont (encode mont f) = nttInv f := by
  cases mont
  · rfl
  · exact Montgomery.inv_cancel f

theorem encode_add (mont : Bool) (f g : Poly) : encode mont (add f g) = add (encode mont f) (encode mont g) := by
  cases mont
  · rfl
  · exact Montgomery.scale_add _ f g

theorem encode_sub (mont : Bool) (f g : Poly) : encode mont (sub f g) = sub (encode mont f) (encode mont g) := by
  cases mont
  · rfl
  · exact Montgomery.scale_sub _ f g

theorem inverse_product (mont : Bool) (f g : Poly) :
    inverse mont (product mont f g) = nttInv (multiplyNTT f g) := inverse_encode mont _

end VG.Proof.MlDsa.Arith.Representation
