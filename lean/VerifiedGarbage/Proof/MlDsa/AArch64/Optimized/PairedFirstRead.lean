import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedStoreRead

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem writePair_slice_other (v : Values) (base : Addr) (m : Mem)
    {u k : Nat} (hu : u<8) (hk : k<8) (hne : k≠u) (poly : Fin 2) (j : Fin 8) :
    (writePair v (base+BitVec.ofNat 64 (128*u)) 16 m).read
      ((base+BitVec.ofNat 64 (128*k))+BitVec.ofNat 64 (1024*poly.val+16*j.val)) 16=
    m.read ((base+BitVec.ofNat 64 (128*k))+BitVec.ofNat 64 (1024*poly.val+16*j.val)) 16 := by
  rw [writePair_values]
  apply storeValues_read_other
  intro i _
  simp only [BitVec.add_assoc,←BitVec.ofNat_add]
  exact Offset.sep base (by omega) (by omega) (by omega)

/-- Every completed local slice contains the original-input product followed by
exactly the first five inverse layers, independent of later scratch writes. -/
theorem firstPass_read_written {m : Mem} {p a b : Addr} {n u : Nat}
    (hn : n≤8) (hu : u<n)
    (ha : (⟨a,1024⟩ : Region).Disjoint ⟨p,2048⟩)
    (hb : (⟨b,2048⟩ : Region).Disjoint ⟨p,2048⟩) (poly : Fin 2) (j : Fin 8) :
    (firstPassMem m p a b n).read
      ((p+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (1024*poly.val+16*j.val)) 16=
    (Inverse.fiveValues u (valuesAt m (a+BitVec.ofNat 64 (128*u))
      (b+BitVec.ofNat 64 (128*u)) poly))[j.val] := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : u=n
    · subst u
      rw [firstPassMem,writePair_read16,firstPass_valuesAt (by omega) ha hb]
    · rw [firstPassMem,writePair_slice_other _ _ _ (by omega) (by omega) he]
      exact ih (by omega) (by omega)
end VG.Proof.MlDsa.AArch64.Optimized.Paired
