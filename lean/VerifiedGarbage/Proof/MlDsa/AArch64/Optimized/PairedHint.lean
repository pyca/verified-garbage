import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHintHead
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_strq wp_vop)
open VG.Proof.MlDsa.AArch64.Optimized.Response (laneVector laneVector_word reduceWord normMask)

def hintLane (raw : VReg) (off : Nat) : List Instr := hintHead raw off ++
  [.strq .v25 .x15 off,.vop (.add .s4 .v14 .v14 .v25)]

theorem hintLane_ok (raw : VReg) {s : State} {off : Nat} (ho : off%16=0 ∧ off<65536)
    (hl : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hh : InRegions (s.rd++s.wr) (s.gpr .x16+BitVec.ofNat 64 off) 16)
    (hw : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (hn : ∀e<4,vword (s.v .v12) e= -vword (s.v .v11) e)
    (hz : ∀e<4,vword (s.v .v13) e=0)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,StepFrame [.v14,.v24,.v25,.v26,.v27,.v28,.v30] s t →
      t.mem=s.mem.write (s.gpr .x15+BitVec.ofNat 64 off) 16 (laneVector (hintOutput s raw off)) →
      (∀e<4,vword (t.v .v14) e=vword (s.v .v14) e+hintOutput s raw off e) →
      (∀e<4,vword (t.v .v30) e=vword (s.v .v30) e |||
        normMask (reduceWord (vword (s.v raw) e)) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) t Q) : WP isa (.block (hintLane raw off++rest)) s Q := by
  unfold hintLane
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine hintHead_ok raw ho hl hh hq hc hn hz fun a ha hv hm => ?_
  have vv : a.v .v25=laneVector (hintOutput s raw off) := by
    apply vec_ext; intro e he; rw [laneVector_word _ he,hv e he]
  refine wp_strq ho rfl (by simpa only [ha.wr,ha.gpr] using hw) fun b hb => ?_
  refine wp_vop (d:=.v14) rfl fun t ht => ?_
  refine k t ?_ ?_ ?_ ?_
  · exact (((StepFrame.ofChg ha).trans (StepFrame.ofMem hb)).trans
      (StepFrame.ofChg ht.chg)).mono (by decide)
  · rw [ht.chg.mem,hb.mem,ha.mem,ha.gpr,vv]
  · intro e he
    rw [ht.v,VG.AArch64.vword_map2 _ _ _ he,hb.v,ha.get .v14 (by decide),hv e he]
  · intro e he
    rw [ht.get .v30 (by decide),hb.v,hm e he]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
