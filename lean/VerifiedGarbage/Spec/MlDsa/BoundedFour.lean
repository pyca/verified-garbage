import VerifiedGarbage.Spec.MlDsa.Poly

namespace VG.Spec.MlDsa

/-- Four independent standard bounded samplers, with one shared public work bound. -/
def rejBoundedFour (η B : Nat) (m : Mem) (seed : Addr) : Option (List IPoly) :=
 (List.range 4).mapM fun i=>rejBoundedPoly η B (Spec.Sha3.bytesAt m (seed+BitVec.ofNat 64 (66*i)) 66)

/-- The existing scalar leakage, separately for each of the four seeds. -/
def rejBoundedFourLeak (η : Nat) (m : Mem) (seed : Addr) : List Nat :=
 (List.range 4).flatMap fun i=>rejBoundedLeak η (Spec.Sha3.bytesAt m (seed+BitVec.ofNat 64 (66*i)) 66)

/-- Eta is fixed by the entry point rather than passed in a register. -/
def rejBoundedFourSig : Sig where
 params := [("seeds",.array false .u8 264),("a",.array true .u32 1024),
   ("scratch",.array true .u64 1024)]
 ret := some .u32

/-- A reduced secret polynomial represented by coefficients in the eta interval. -/
def BoundedOutput (η : Nat) (m : Mem) (a : Addr) : Prop :=
 ∃x : IPoly,polyAt m a=toRq x ∧ ∀c∈x.toList,-(η:Int)≤c ∧ c≤η

/-- Joint execution preserves the scalar samplers' Outcome and rejection-bit
leakage. The return value is one exactly when all four samplers succeed. -/
def rejBoundedFourContract {M : ISA} (A : Abi M) (η : Nat) (stack : Nat := 0) : Contract M :=
 rejBoundedFourSig.contract A
  (pre := fun _seed _a _scratch _m=>η=2∨η=4)
  (post := fun seed a _scratch m m' r=>
    (∀i<4,Reduced m' (a+BitVec.ofNat 64 (1024*i))) ∧
    (∀i<4,BoundedOutput η m' (a+BitVec.ofNat 64 (1024*i))) ∧
    Outcome (fun b=>(rejBoundedFour η b.rejBounded m seed).map (List.map toRq)) r
      ((List.range 4).map fun i=>polyAt m' (a+BitVec.ofNat 64 (1024*i))))
  (writeArgs := true) (stack := stack)
  (leak := some fun seed _a _scratch m=>rejBoundedFourLeak η m seed)

def rejBoundedFourApi (η : Nat) : Api where
 module := "mldsa"
 name := "vg_mldsa_rej_bounded_poly4_eta"++toString η
 sig := rejBoundedFourSig
 writeArgs := true
 contracts := some fun A stack=>rejBoundedFourContract A η stack
 summary := "Samples four independent ML-DSA secret polynomials with the standard rejection-bit leakage."
 safety := ["This entry point fixes eta to 2 or 4."]

end VG.Spec.MlDsa
