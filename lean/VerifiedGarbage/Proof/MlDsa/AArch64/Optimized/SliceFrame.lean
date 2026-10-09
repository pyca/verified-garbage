import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Slice
import VerifiedGarbage.Proof.Framework.Mem

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

/-- An immutable table outside the output region remains readable after a slice. -/
theorem writeBank_read (values : Vector (BitVec 128) 8) (base : Addr) (stride : Nat)
    {r table : Region} (hc : ∀ i : Fin 8, r.Contains (base+BitVec.ofNat 64 (stride*i.val)) 16)
    (hd : table.Disjoint r) {m : Mem} {a : Addr} {n : Nat}
    (ha : table.Contains a n) (hn : n < 2^64) :
    (writeBank values base stride m).read a n = m.read a n := by
  have hf := writeBank_frame values base stride (W := [r]) (by simp) hc (Frame.refl [r] m)
  exact hf.read ha (by intro r' hr'; have he := List.mem_singleton.mp hr'; subst r'; exact hd) hn

end VG.Proof.MlDsa.AArch64.Optimized
