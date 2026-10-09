import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckSlot

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response

/-- The hint counter adds exactly the vector emitted by this check. -/
theorem checkStep_count (raw : BitVec 128) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) {e : Nat} (he : e<4) :
    vword (checkStep true raw out aux c d).count e=vword d.count e+
      vword (checkOutput true raw (d.mem.read out 16) (d.mem.read aux 16) c) e := by
  simp only [checkStep,checkOutput,ite_true,laneVector_word _ he]

def hintSum (v : Values) (out aux : Addr) (c : CheckConstants) (m : Mem) (e : Nat)
    (js : List (Fin 2 × Fin 8)) : BitVec 32 :=
  (js.map fun i => vword (checkOutput true ((v i.1)[i.2.val])
    (m.read (checkAddr out i) 16) (m.read (checkAddr aux i) 16) c) e).sum

/-- The count of a check sequence is the sum of its original-input outputs. -/
theorem checkRun_count (v : Values) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) (js : List (Fin 2 × Fin 8)) (hn : js.Nodup)
    (ha : ∀i∈js,∀j∈js,Mem.Sep (checkAddr aux i) 16 (checkAddr out j) 16)
    {e : Nat} (he : e<4) :
    vword (checkRun true v out aux c d js).count e=vword d.count e+hintSum v out aux c d.mem e js := by
  induction js generalizing d with
  | nil =>
    simp only [checkRun,hintSum,List.map_nil,List.sum_nil]
    exact (BitVec.add_zero _).symm
  | cons i js ih =>
    have hn' := List.nodup_cons.mp hn
    rw [checkRun,ih _ hn'.2 (fun j hj k hk => ha j (List.mem_cons_of_mem _ hj) k (List.mem_cons_of_mem _ hk)),
      checkStep_count _ _ _ _ _ he]
    have hread (j : Fin 2 × Fin 8) (hj : j∈js) :
        checkOutput true ((v j.1)[j.2.val])
          ((checkStep true ((v i.1)[i.2.val]) (checkAddr out i) (checkAddr aux i) c d).mem.read (checkAddr out j) 16)
          ((checkStep true ((v i.1)[i.2.val]) (checkAddr out i) (checkAddr aux i) c d).mem.read (checkAddr aux j) 16) c=
        checkOutput true ((v j.1)[j.2.val]) (d.mem.read (checkAddr out j) 16) (d.mem.read (checkAddr aux j) 16) c := by
      have ho := checkAddr_sep out (i:=j) (j:=i) (by intro h; subst i; exact hn'.1 hj)
      simp only [checkStep]
      rw [Mem.read_write_sep ho (by decide),Mem.read_write_sep (ha j (List.mem_cons_of_mem _ hj) i (by simp)) (by decide)]
    have hs : hintSum v out aux c
        (checkStep true ((v i.1)[i.2.val]) (checkAddr out i) (checkAddr aux i) c d).mem e js=
        hintSum v out aux c d.mem e js := by
      unfold hintSum
      apply congrArg (fun xs : List (BitVec 32) => xs.sum)
      apply List.map_congr_left
      intro j hj
      rw [hread j hj]
    simp only [checkAddr] at hs ⊢
    rw [hs]
    simp only [hintSum,List.map_cons,List.sum_cons,checkAddr,BitVec.add_assoc]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
