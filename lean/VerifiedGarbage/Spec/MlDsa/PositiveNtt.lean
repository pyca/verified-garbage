module

public import VerifiedGarbage.Spec.MlDsa.Poly

/-! Separate internal transform contracts. They retain the standard NTT field
value while explicitly allowing positive representatives below three times q.
The canonical `nttContract`, `Reduced`, and `PolyIs` contracts are unchanged. -/

@[expose] public section

namespace VG.Spec.MlDsa

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

def positiveNttApi : Api where
  module := "mldsa"
  name := "vg_mldsa_ntt_positive"
  sig := positiveNttSig
  writeArgs := true
  contracts := some fun A stack => positiveNttContract A stack
  summary := "Transforms a canonical polynomial in place to its NTT, with positive representatives below 3q."
  safety := ["Each input coefficient must be less than q = 8380417."]

def positiveNttOutApi : Api where
  module := "mldsa"
  name := "vg_mldsa_ntt_positive_from"
  sig := positiveNttOutSig
  writeArgs := true
  contracts := some fun A stack => positiveNttOutContract A stack
  summary := "Transforms a separate canonical input polynomial to its NTT, with positive representatives below 3q."
  safety := ["Each input coefficient must be less than q = 8380417."]

end VG.Spec.MlDsa
