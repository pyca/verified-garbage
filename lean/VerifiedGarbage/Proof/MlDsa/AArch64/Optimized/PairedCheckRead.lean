import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckSource

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- A check sequence preserves any untouched vector, independently of flags. -/
theorem checkRun_read_other (hint : Bool) (v : Values) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) (js : List (Fin 2 × Fin 8)) (a : Addr)
    (hs : ∀i∈js,Mem.Sep a 16 (out+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)) 16) :
    (checkRun hint v out aux c d js).mem.read a 16=d.mem.read a 16 := by
  induction js generalizing d with
  | nil => rfl
  | cons i js ih =>
    change (checkRun hint v out aux c (checkStep hint ((v i.1)[i.2.val])
      (out+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val))
      (aux+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)) c d) js).mem.read a 16=_
    rw [ih _ (fun j hj => hs j (List.mem_cons_of_mem _ hj))]
    exact Mem.read_write_sep (hs i (by simp)) (by decide)

/-- The z path preserves the hint count accumulator exactly. -/
theorem checkRun_z_count (v : Values) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) (js : List (Fin 2 × Fin 8)) :
    (checkRun false v out aux c d js).count=d.count := by
  induction js generalizing d with
  | nil => rfl
  | cons i js ih =>
    simp only [checkRun]
    exact ih _

theorem finalPass_z_count (work out aux : Addr) (c : CheckConstants) (d : CheckData) (u : Nat) :
    (finalPassData false work out aux c d u).count=d.count := by
  induction u with
  | zero => rfl
  | succ u ih => rw [finalPassData,checkRun_z_count,ih]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
