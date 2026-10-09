import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowReady

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.Round VG.Proof.MlDsa.AArch64.Round

def lowRun (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) : List LowIndex → CheckData
  | [] => d
  | i::is => lowRun g v out aux c (lowPairStep g (lowValue0 v i) (lowValue1 v i)
      (out+BitVec.ofNat 64 (lowOff i)) (out+BitVec.ofNat 64 (lowOff i+128))
      (aux+BitVec.ofNat 64 (lowOff i)) (aux+BitVec.ofNat 64 (lowOff i+128)) c d) is

def lowRunCode (g : Nat) (is : List LowIndex) : List Instr :=
  is.flatMap fun i => lowPairBlocks g (lowRaw0 i) (lowRaw1 i) (lowOff i)

theorem lowRun_ok {g : Nat} (hg : IsG g) (is : List LowIndex) (hn : is.Nodup)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values}
    (hv : LowPending s v is) (hc : LowReady g s)
    (hr : ∀i:LowIndex,
      InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (lowOff i+128)) 16 ∧
      InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (lowOff i)) 16 ∧
      InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (lowOff i+128)) 16)
    (k : ∀t,StepFrame lowRunRegs s t → dataAt t=lowRun g v (s.gpr .x15) (s.gpr .x16)
      (lowConstantsAt s) (dataAt s) is → WP isa (.block rest) t Q) :
    WP isa (.block (lowRunCode g is++rest)) s Q := by
  induction is generalizing s with
  | nil => exact k s ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl⟩ rfl
  | cons i is ih =>
    simp only [lowRunCode,List.flatMap_cons,List.append_assoc]
    have hh := lowPair_registers i.1.isLt i.2.isLt
    have ho := lowPair_offsets i.1.isLt i.2.isLt
    refine lowPairStep_ok hg hh.1 hh.2.1 hh.2.2 ⟨ho.1,ho.2.1⟩
      (hr i).1 (hr i).2.1 (hr i).2.2.1 (hr i).2.2.2.1 (hr i).2.2.2.2.1 (hr i).2.2.2.2.2
      hc.q hc.bias hc.c11 hc.c12 hc.c13 hc.c14 fun a ha hda => ?_
    have haf : StepFrame lowRunRegs s a := (StepFrame.ofKeep ha).mono (lowClobs_subset i)
    refine ih (List.nodup_cons.mp hn).2 (hv.next (List.nodup_cons.mp hn).1 ha) (hc.frame haf) ?_
      fun t ht hdt => ?_
    · simpa only [haf.rd,haf.wr,haf.gpr] using hr
    · refine k t ((haf.trans ht).mono (by simp)) ?_
      have hvi := hv i (by simp)
      simp only [lowRaw0,lowRaw1] at hvi
      rw [hdt,haf.gpr,lowConstantsAt_frame haf,hda,hvi.1,hvi.2]
      rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
