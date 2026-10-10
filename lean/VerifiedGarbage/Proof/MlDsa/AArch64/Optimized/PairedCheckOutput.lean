import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckSource

/-! ## From `PairedCheckRead.lean` -/

section

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

end

/-! ## From `PairedCheckOutput.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (laneVector reduceWord hintWord)

def checkOutput (hint : Bool) (raw low high : BitVec 128) (c : CheckConstants) : BitVec 128 :=
  laneVector fun e => if hint then
    hintWord (vword c.gamma e) (reduceWord (vword raw e)+vword low e) (vword high e)
    else reduceWord (vword raw e+vword low e)

theorem checkStep_read_self (hint : Bool) (raw : BitVec 128) (out aux : Addr)
    (c : CheckConstants) (d : CheckData) :
    (checkStep hint raw out aux c d).mem.read out 16=
      checkOutput hint raw (d.mem.read out 16) (d.mem.read aux 16) c := by
  have hm : (checkStep hint raw out aux c d).mem =
      d.mem.write out 16 (checkOutput hint raw (d.mem.read out 16) (d.mem.read aux 16) c) := by
    cases hint <;> simp only [checkStep,checkOutput,Bool.false_eq_true,ite_false,ite_true]
  rw [hm]
  exact Mem.readW_writeW_self d.mem out 16
    (checkOutput hint raw (d.mem.read out 16) (d.mem.read aux 16) c) (by decide)

/-- Once a vector is checked, the remaining distinct checks preserve its output. -/
theorem checkRun_head_output (hint : Bool) (v : Values) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) (i : Fin 2 × Fin 8) (js : List (Fin 2 × Fin 8))
    (hs : ∀j∈js,Mem.Sep (out+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)) 16
      (out+BitVec.ofNat 64 (1024*j.1.val+128*j.2.val)) 16) :
    (checkRun hint v out aux c d (i::js)).mem.read (out+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)) 16=
      checkOutput hint ((v i.1)[i.2.val])
        (d.mem.read (out+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)) 16)
        (d.mem.read (aux+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)) 16) c := by
  rw [checkRun,checkRun_read_other _ _ _ _ _ _ _ _ hs,checkStep_read_self]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
