import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstSource

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def storeValues {α : Type} (xs : List α) (addr : α → Addr) (values : α → BitVec 128) (m : Mem) : Mem :=
 xs.foldl (fun m i => m.write (addr i) 16 (values i)) m

theorem storeValues_read_other {α : Type} (xs : List α) (addr : α → Addr)
    (values : α → BitVec 128) (m : Mem) (a : Addr)
    (hs : ∀i∈xs,Mem.Sep a 16 (addr i) 16) :
    (storeValues xs addr values m).read a 16=m.read a 16 := by
  induction xs generalizing m with
  | nil => rfl
  | cons i xs ih =>
    change (storeValues xs addr values (m.write (addr i) 16 (values i))).read a 16=_
    rw [ih _ (fun j hj => hs j (List.mem_cons_of_mem _ hj)),Mem.read_write_sep (hs i (by simp)) (by decide)]

theorem storeValues_read_slot {α : Type} [DecidableEq α] (xs : List α) (addr : α → Addr)
    (values : α → BitVec 128) (m : Mem) (i : α) (hi : i∈xs)
    (hs : ∀j∈xs,j≠i → Mem.Sep (addr i) 16 (addr j) 16) :
    (storeValues xs addr values m).read (addr i) 16=values i := by
  induction xs generalizing m with
  | nil => simp at hi
  | cons j xs ih =>
    change (storeValues xs addr values (m.write (addr j) 16 (values j))).read _ 16=_
    by_cases ht : i∈xs
    · exact ih _ ht (fun k hk => hs k (List.mem_cons_of_mem _ hk))
    · have he : i=j := (List.mem_cons.mp hi).resolve_right ht
      subst j
      rw [storeValues_read_other _ _ _ _ _ (fun k hk => hs k (List.mem_cons_of_mem _ hk)
        (by intro he; subst k; exact ht hk))]
      simpa only [Mem.writeW,Mem.readW,BitVec.setWidth_eq] using
        Mem.readW_writeW_self m (addr i) 16 (values i) (by decide)

def pairIndices : List (Fin 2 × Fin 8) :=
 (List.finRange 2).flatMap fun p => (List.finRange 8).map fun j => (p,j)

theorem pairIndices_mem (i : Fin 2 × Fin 8) : i∈pairIndices := by
  simp only [pairIndices,List.mem_flatMap,List.mem_map,List.mem_finRange,true_and]
  exact ⟨i.1,i.2,rfl⟩

theorem writePair_values (v : Values) (base : Addr) (stride : Nat) (m : Mem) :
    writePair v base stride m=storeValues pairIndices
      (fun i => base+BitVec.ofNat 64 (1024*i.1.val+stride*i.2.val))
      (fun i => (v i.1)[i.2.val]) m := by
  simp only [writePair,storeValues,pairIndices,List.foldl_flatMap,List.foldl_map]

theorem pair16_sep (base : Addr) {i j : Fin 2 × Fin 8} (hne : j≠i) :
    Mem.Sep (base+BitVec.ofNat 64 (1024*i.1.val+16*i.2.val)) 16
      (base+BitVec.ofNat 64 (1024*j.1.val+16*j.2.val)) 16 := by
  have hd : j.1.val≠i.1.val ∨ j.2.val≠i.2.val := by
    by_contra h
    simp only [not_or,not_not] at h
    exact hne (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
  exact Offset.sep base (by omega) (by omega) (by omega)

/-- Each stored 16-byte first-pass vector is recovered exactly from its own bank. -/
theorem writePair_read16 (v : Values) (base : Addr) (m : Mem) (p : Fin 2) (j : Fin 8) :
    (writePair v base 16 m).read (base+BitVec.ofNat 64 (1024*p.val+16*j.val)) 16=(v p)[j.val] := by
  rw [writePair_values]
  exact storeValues_read_slot _ _ _ _ (p,j) (pairIndices_mem _) (fun _ _ hn => pair16_sep base hn)
end VG.Proof.MlDsa.AArch64.Optimized.Paired
