import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckRead

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
