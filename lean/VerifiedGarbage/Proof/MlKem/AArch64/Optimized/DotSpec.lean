module

public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Field
public import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlKem.Arith

/-! # Fused accumulators compute the existing K-PKE dot product -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.Spec.MlKem VG.Proof.MlKem

theorem polySum_dotK (offsets : Nat → Nat × Nat) (F G : (Nat × Nat) → Poly)
    (a b : Nat → Poly) {k : Nat}
    (hf : ∀ j<k, F (offsets j)=a j) (hg : ∀ j<k, G (offsets j)=b j) :
    Dot.polySum ((List.range k).map offsets) F G = KPke.dotK a b k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hrec := ih (fun j hj => hf j (by omega)) (fun j hj => hg j (by omega))
    unfold Dot.polySum at *
    rw [List.range_succ,List.map_append,List.foldl_append,List.map_cons,List.map_nil,
      List.foldl_cons,List.foldl_nil,hrec,hf k (by omega),hg k (by omega)]
    exact (KPke.foldK_succ zero_add_poly (fun j => multiplyNTTs (a j) (b j)) k).symm

end VG.Proof.MlKem.AArch64.Optimized
