module

public import VerifiedGarbage.Spec.MlDsa.ResponseLow
public import VerifiedGarbage.Spec.MlDsa.ResponseHint

@[expose] public section

namespace VG.Spec.MlDsa

/-- Polynomial j in a contiguous pair. -/
def pairPolyPtr (p : Addr) (j : Nat) : Addr := p+BitVec.ofNat 64 (1024*j)

/-- Compose the existing NTT product and inverse-transform specifications. -/
def pairedProduct (m : Mem) (challenge secret : Addr) (j : Nat) : Poly :=
  nttInv (multiplyNTT (polyAt m challenge) (polyAt m (pairPolyPtr secret j)))

def pairedProductsReduced (m : Mem) (challenge secret : Addr) : Prop :=
  PositiveReduced m challenge ∧ ∀j<2,PositiveReduced m (pairPolyPtr secret j)

def pairedZSig : Sig where
  params := [("challenge",.array false .u32 256),("secret",.array false .u32 512),
    ("y",.array true .u32 512),("unused",.int .u64 true),
    ("work",.array true .u64 272),("unused_gamma",.int .u32 false),("bound",.int .u32 false)]
  ret := some .u32

/-- Both response sums are written on every path. The unused scalar argument
has no memory footprint, so callers may pass the work-buffer address there. -/
def pairedZContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  pairedZSig.contract A
    (pre := fun c secret y _unused _work _gamma bound m =>
      pairedProductsReduced m c secret ∧ (∀j<2,Reduced m (pairPolyPtr y j)) ∧
      1≤bound.toNat ∧ bound.toNat≤524288)
    (post := fun c secret y _unused _work _gamma bound m m' r =>
      (∀j<2,CenteredReduced m' (pairPolyPtr y j) ∧
        signedPolyAt m' (pairPolyPtr y j)=add (polyAt m (pairPolyPtr y j)) (pairedProduct m c secret j)) ∧
      r=if normRq ((List.range 2).map fun j => add (polyAt m (pairPolyPtr y j)) (pairedProduct m c secret j))<bound.toNat then 1 else 0)
    (writeArgs := true) (stack := stack)

def pairedLowSig : Sig where
  params := [("challenge",.array false .u32 256),("secret",.array false .u32 512),
    ("w",.array true .u32 512),("low",.array true .u32 512),
    ("work",.array true .u64 272),("gamma2",.int .u32 true),("bound",.int .u32 false)]
  ret := some .u32

def pairedDifference (m : Mem) (c secret w : Addr) (j : Nat) : Poly :=
  sub (polyAt m (pairPolyPtr w j)) (pairedProduct m c secret j)

def pairedLowPoly (g : Nat) (f : Poly) : Poly := f.map fun x => ofInt (lowBits g x)

/-- Exact high and signed low parts are written even when either polynomial
fails its norm bound. No per-polynomial early return is permitted by timing. -/
def pairedLowContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  pairedLowSig.contract A
    (pre := fun c secret w _low _work gamma2 bound m =>
      pairedProductsReduced m c secret ∧ (∀j<2,Reduced m (pairPolyPtr w j)) ∧
      gamma2.toNat∈gamma2s ∧ 1≤bound.toNat ∧ bound.toNat≤524288)
    (post := fun c secret w low _work gamma2 bound m m' r =>
      (∀j<2,∀i<n,
        (coeffAt m' (pairPolyPtr w j) i).toNat=(highBits gamma2.toNat (pairedDifference m c secret w j)[i]!).toNat ∧
        (coeffAt m' (pairPolyPtr low j) i).toInt=lowBits gamma2.toNat (pairedDifference m c secret w j)[i]!) ∧
      r=if normRq ((List.range 2).map fun j => pairedLowPoly gamma2.toNat (pairedDifference m c secret w j))<bound.toNat then 1 else 0)
    (writeArgs := true) (stack := stack)

def pairedHintSig : Sig where
  params := [("challenge",.array false .u32 256),("secret",.array false .u32 512),
    ("low",.array true .u32 512),("high",.array false .u32 512),
    ("work",.array true .u64 272),("gamma2",.int .u32 true),("bound",.int .u32 false)]
  ret := some .u64

def pairedHintPoly (m : Mem) (c secret low high : Addr) (g j : Nat) : Vector Bool n :=
  Vector.ofFn fun i =>
    let ct := (pairedProduct m c secret j)[i.val]!
    makeHint g (-ct) (responseHintBase m (pairPolyPtr low j) (pairPolyPtr high j) g i.val+ct)

/-- Return the total hint count in low32 and strict norm success in high32.
All 512 hints are exact on both acceptance and rejection. -/
def pairedHintContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  pairedHintSig.contract A
    (pre := fun c secret low high _work gamma2 bound m =>
      pairedProductsReduced m c secret ∧ gamma2.toNat∈gamma2s ∧ bound=gamma2 ∧
      ∀j<2,ResponseDecomposed m (pairPolyPtr low j) (pairPolyPtr high j) gamma2.toNat)
    (post := fun c secret low high _work gamma2 _bound m m' r =>
      let hints := (List.range 2).map fun j => pairedHintPoly m c secret low high gamma2.toNat j
      HintIs m' low 2 hints ∧
      r=BitVec.ofNat 64 (hintOnes hints+
        if normRq ((List.range 2).map fun j => pairedProduct m c secret j)<gamma2.toNat then 4294967296 else 0))
    (writeArgs := true) (stack := stack)

end VG.Spec.MlDsa
