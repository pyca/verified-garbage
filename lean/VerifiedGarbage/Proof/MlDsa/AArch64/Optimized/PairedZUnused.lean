import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPassOutput

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- The z check does not read or depend on its auxiliary argument. -/
theorem checkStep_z_aux (raw : BitVec 128) (out aux aux' : Addr)
    (c : CheckConstants) (d : CheckData) :
    checkStep false raw out aux c d=checkStep false raw out aux' c d := by
  simp only [checkStep,Bool.false_eq_true,ite_false]

theorem checkRun_z_aux (v : Values) (out aux aux' : Addr) (c : CheckConstants)
    (d : CheckData) (js : List (Fin 2 × Fin 8)) :
    checkRun false v out aux c d js=checkRun false v out aux' c d js := by
  induction js generalizing d with
  | nil => rfl
  | cons i js ih =>
    simp only [checkRun]
    rw [checkStep_z_aux _ _ _ (aux'+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)),ih]

theorem finalPass_z_aux (work out aux aux' : Addr) (c : CheckConstants)
    (d : CheckData) (n : Nat) :
    finalPassData false work out aux c d n=finalPassData false work out aux' c d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finalPassData,ih]
    exact checkRun_z_aux _ _ _ _ _ _ _

/-- Exact z output with an arbitrary unused auxiliary argument. -/
theorem finalPass_z_read_written (work out aux : Addr) (c : CheckConstants)
    (d : CheckData) {n k : Nat} (hn : n≤8) (hk : k<n) (i : Fin 2 × Fin 8)
    (hw : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩) :
    (finalPassData false work out aux c d n).mem.read (checkAddr (out+BitVec.ofNat 64 (16*k)) i) 16=
      checkOutput false ((Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*k)) 128 i.1))[i.2.val])
        (d.mem.read (checkAddr (out+BitVec.ofNat 64 (16*k)) i) 16) 0 c := by
  rw [finalPass_z_aux work out aux work]
  have h := finalPass_read_written false work out work c d hn hk i hw hw
  simpa only [checkOutput,Bool.false_eq_true,ite_false] using h

end VG.Proof.MlDsa.AArch64.Optimized.Paired
