import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackBody
import VerifiedGarbage.Proof.MlDsa.Arith.Mem

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open HighPack (packWidth)
open VG.Proof.MlDsa.Arith (polyRegion)

 theorem packed_frame {g : Nat} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {b a : Addr}
    (hb : ∀r∈rs,(polyRegion b).Disjoint r) (ha : ∀r∈rs,(polyRegion a).Disjoint r) :
    packed g m' b a=packed g m b a := by
  unfold packed
  apply congrArg (fun L=>simpleBitPack L ((q-1)/(2*g)-1))
  apply Vector.ext
  intro i hi
  simp only [fields,Vector.getElem_ofFn]
  rw [VG.Proof.MlDsa.Arith.coeffAt_frame hf ha hi,VG.Proof.MlDsa.Arith.coeffAt_frame hf hb hi]

 theorem packed_length {g : Nat} (hg : Round.IsG g) (m : Mem) (b a : Addr) :
    (packed g m b a).length=32*packWidth g := by
  have hw : bitlen ((q-1)/(2*g)-1)=packWidth g := by rcases hg with rfl|rfl <;> rfl
  rw [packed,VG.Proof.MlDsa.Pack.simpleBitPack_eq,hw]
  exact VG.Proof.MlDsa.Pack.pack_length _ _ (by simp)

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
