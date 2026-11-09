module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Slice
public import VerifiedGarbage.Proof.Framework.Mem

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64

theorem writeBank_frame (values : Vector (BitVec 128) 8) (base : Addr) (stride : Nat)
    {W : List Region} {r : Region} (hr : r ∈ W)
    (hc : ∀ i : Fin 8, r.Contains (base+BitVec.ofNat 64 (stride*i.val)) 16)
    {m m' : Mem} (hf : Frame W m m') : Frame W m (writeBank values base stride m') := by
  have fold (is : List (Fin 8)) : ∀ m', Frame W m m' →
      Frame W m (is.foldl
        (fun m i => m.write (base+BitVec.ofNat 64 (stride*i.val)) 16 values[i.val]) m') := by
    induction is with
    | nil => intro m' h; exact h
    | cons i is ih =>
      intro m' h
      exact ih _ (h.write hr _ (hc i))
  exact fold _ m' hf

end VG.Proof.MlDsa.AArch64.Optimized
