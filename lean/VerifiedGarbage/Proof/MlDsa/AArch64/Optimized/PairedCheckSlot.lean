import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckOutput

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def checkAddr (base : Addr) (i : Fin 2 × Fin 8) : Addr :=
  base+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)

theorem checkAddr_sep (base : Addr) {i j : Fin 2 × Fin 8} (hne : j≠i) :
    Mem.Sep (checkAddr base i) 16 (checkAddr base j) 16 := by
  have hd : j.1.val≠i.1.val ∨ j.2.val≠i.2.val := by
    by_contra h
    simp only [not_or,not_not] at h
    exact hne (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
  exact Offset.sep base (by omega) (by omega) (by omega)

/-- Every checked vector has exactly its prescribed output, using its original
inputs; arbitrary earlier and later disjoint stores cannot alter the result. -/
theorem checkRun_read_slot (hint : Bool) (v : Values) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) (js : List (Fin 2 × Fin 8)) (i : Fin 2 × Fin 8)
    (hi : i∈js) (hn : js.Nodup)
    (hs : ∀j∈js,j≠i → Mem.Sep (checkAddr out i) 16 (checkAddr out j) 16)
    (ha : ∀j∈js,Mem.Sep (checkAddr aux i) 16 (checkAddr out j) 16) :
    (checkRun hint v out aux c d js).mem.read (checkAddr out i) 16=
      checkOutput hint ((v i.1)[i.2.val]) (d.mem.read (checkAddr out i) 16)
        (d.mem.read (checkAddr aux i) 16) c := by
  induction js generalizing d with
  | nil => simp at hi
  | cons j js ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases he : j=i
    · subst j
      exact checkRun_head_output hint v out aux c d i js
        (fun j hj => hs j (List.mem_cons_of_mem _ hj) (by intro he; subst j; exact hn'.1 hj))
    · have hit : i∈js := (List.mem_cons.mp hi).resolve_left (Ne.symm he)
      simp only [checkRun]
      rw [ih _ hit hn'.2 (fun k hk => hs k (List.mem_cons_of_mem _ hk))
        (fun k hk => ha k (List.mem_cons_of_mem _ hk))]
      have ho : (checkStep hint ((v j.1)[j.2.val]) (checkAddr out j) (checkAddr aux j) c d).mem.read
          (checkAddr out i) 16=d.mem.read (checkAddr out i) 16 :=
        Mem.read_write_sep (hs j (by simp) he) (by decide)
      have haux : (checkStep hint ((v j.1)[j.2.val]) (checkAddr out j) (checkAddr aux j) c d).mem.read
          (checkAddr aux i) 16=d.mem.read (checkAddr aux i) 16 :=
        Mem.read_write_sep (ha j (by simp)) (by decide)
      simp only [checkAddr] at ho haux ⊢
      rw [ho,haux]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
