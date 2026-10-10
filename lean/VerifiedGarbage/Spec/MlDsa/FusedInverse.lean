module

public import VerifiedGarbage.Spec.MlDsa.PositiveNtt

/-! Internal fused arithmetic interfaces. Inputs may use positive, noncanonical
representatives below 3q; outputs are canonical ordinary coefficients.
These specifications express composition of the existing field operations. -/

@[expose] public section

namespace VG.Spec.MlDsa

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

/-- A fixed-width row product followed by the ordinary inverse transform. -/
def dotInverseApi (count : Nat) : Api where
  module := "mldsa"
  name := s!"vg_mldsa_dot_inverse{count}"
  sig := dotInverseSig count
  writeArgs := true
  contracts := some fun A stack => dotInverseContract count A stack
  summary := "Writes the canonical inverse NTT of the sum of coefficientwise products " ++
    s!"of {count} pairs of polynomials. Each input family is contiguous. " ++
    "Timing depends only on pointers, as specified by `dotInverseContract`."
  safety := ["Every coefficient of both input families must be less than 25141251 (3q)."]

end VG.Spec.MlDsa
