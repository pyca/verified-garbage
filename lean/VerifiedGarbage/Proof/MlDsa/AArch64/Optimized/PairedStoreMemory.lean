import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedStore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.SliceFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem writePair_split (v : Values) (base : Addr) (stride : Nat) (m : Mem) :
    writePair v base stride m=writeBank (v 1) (base+1024) stride (writeBank (v 0) base stride m) := by
  simp only [writePair,show List.finRange 2=[0,1] by rfl,List.foldl_cons,List.foldl_nil,
    Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.zero_add,Nat.mul_one,writeBank]
  simp only [BitVec.ofNat_add,BitVec.add_assoc,show (1024 : Addr)=1024#64 by rfl]

theorem writePair_frame (v : Values) (base : Addr) (stride : Nat)
    {m m₀ : Mem} {W : List Region} {r : Region} (hr : r∈W)
    (hc : ∀p:Fin 2,∀j:Fin 8,r.Contains (base+BitVec.ofNat 64 (1024*p.val+stride*j.val)) 16)
    (hf : Frame W m₀ m) : Frame W m₀ (writePair v base stride m) := by
  rw [writePair_split]
  refine writeBank_frame _ _ _ hr ?_ ?_
  · intro j
    simpa only [Fin.val_one,Nat.mul_one,BitVec.ofNat_add,BitVec.add_assoc,show (1024 : Addr)=1024#64 by rfl] using hc 1 j
  · refine writeBank_frame _ _ _ hr ?_ hf
    intro j
    simpa only [Fin.val_zero,Nat.mul_zero,Nat.zero_add] using hc 0 j

end VG.Proof.MlDsa.AArch64.Optimized.Paired
