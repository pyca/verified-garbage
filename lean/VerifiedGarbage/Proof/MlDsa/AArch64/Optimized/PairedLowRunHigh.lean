import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowHalfOutput

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowHighOutput_read_eq (g : Nat) {m m' : Mem} (out : Addr) (raw : BitVec 128)
    (hm : m'.read out 16=m.read out 16) : lowHighOutput g m' out raw=lowHighOutput g m out raw := by
  simp only [lowHighOutput,lowInputValues,hm]

/-- Every pair's high output uses its original input, regardless of its position. -/
theorem lowRun_read_high (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (i : LowIndex) (h : Fin 2)
    (hi : i∈is) (hn : is.Nodup) (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowRun g v out aux c d is).mem.read (lowAddr out i h) 16=
      lowHighOutput g d.mem (lowAddr out i h) (lowHalfValue v i h) := by
  induction is generalizing d with
  | nil => simp at hi
  | cons j is ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases he : j=i
    · subst j
      rw [lowRun,lowRun_read_slot_other _ _ _ _ _ _ _ _ _ hn'.1 hd]
      exact lowPair_read_high _ _ _ _ _ _ _ _ hd
    · have hit : i∈is := (List.mem_cons.mp hi).resolve_left (Ne.symm he)
      rw [lowRun,ih _ hit hn'.2]
      exact lowHighOutput_read_eq _ _ _ (lowPair_other_input g v out aux c d (Ne.symm he) h hd)

end VG.Proof.MlDsa.AArch64.Optimized.Paired
