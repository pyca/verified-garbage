import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowRunHigh

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowRun_read_aux_other (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (i : LowIndex) (h : Fin 2)
    (hn : i∉is) (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowRun g v out aux c d is).mem.read (lowAddr aux i h) 16=d.mem.read (lowAddr aux i h) 16 := by
  apply lowRun_read_other
  intro j hj
  have hnij : i≠j := by intro he; subst j; exact hn hj
  have h0 := hd.symm.sep (lowAddr_contains_base aux i h) (lowAddr_contains_base out j 0)
  have h1 := hd.symm.sep (lowAddr_contains_base aux i h) (lowAddr_contains_base out j 1)
  have h2 := lowAddr_sep (h:=h) (k:=0) aux (Or.inl hnij)
  have h3 := lowAddr_sep (h:=h) (k:=1) aux (Or.inl hnij)
  simpa only [lowAddr,Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] using
    And.intro h0 (And.intro h1 (And.intro h2 h3))

theorem lowLowOutput_read_eq (g : Nat) {m m' : Mem} (out : Addr) (raw : BitVec 128) (c : LowConstants)
    (hm : m'.read out 16=m.read out 16) : lowLowOutput g m' out raw c=lowLowOutput g m out raw c := by
  simp only [lowLowOutput,lowInputValues,hm]

/-- Every pair's signed low output uses its original input, including rejection. -/
theorem lowRun_read_low (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (i : LowIndex) (h : Fin 2)
    (hi : i∈is) (hn : is.Nodup) (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowRun g v out aux c d is).mem.read (lowAddr aux i h) 16=
      lowLowOutput g d.mem (lowAddr out i h) (lowHalfValue v i h) c := by
  induction is generalizing d with
  | nil => simp at hi
  | cons j is ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases he : j=i
    · subst j
      rw [lowRun,lowRun_read_aux_other _ _ _ _ _ _ _ _ _ hn'.1 hd]
      exact lowPair_read_low _ _ _ _ _ _ _ _
    · have hit : i∈is := (List.mem_cons.mp hi).resolve_left (Ne.symm he)
      rw [lowRun,ih _ hit hn'.2]
      exact lowLowOutput_read_eq _ _ _ _ (lowPair_other_input g v out aux c d (Ne.symm he) h hd)

end VG.Proof.MlDsa.AArch64.Optimized.Paired
