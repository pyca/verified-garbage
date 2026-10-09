import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop wp_ldrq wp_strq)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep laneVector laneVector_word reduceWord normMask)

def zInput (s : State) (raw : VReg) (off e : Nat) : BitVec 32 :=
  reduceWord (vword (s.v raw) e+vword (s.mem.read (s.gpr .x15+BitVec.ofNat 64 off) 16) e)
def zLane (raw : VReg) (off : Nat) : List Instr :=
  ([.ldrq .v27 .x15 off,.vop (.add .s4 .v24 raw .v27)] : List Instr) ++
  VG.Impl.MlDsa.AArch64.Optimized.Paired.reduce ++ [.strq .v24 .x15 off] ++
  VG.Impl.MlDsa.AArch64.Optimized.Paired.norm

theorem zLane_ok {s : State} (raw : VReg) (hne : raw≠.v27) {off : Nat}
    (ho : off%16=0 ∧ off<65536)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hw : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,StepKeep [.v24,.v25,.v27,.v30] s t →
      t.mem=s.mem.write (s.gpr .x15+BitVec.ofNat 64 off) 16 (laneVector (zInput s raw off)) →
      (∀e<4,vword (t.v .v30) e=vword (s.v .v30) e |||
        normMask (zInput s raw off e) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) t Q) : WP isa (.block (zLane raw off++rest)) s Q := by
  unfold zLane
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine wp_ldrq ho rfl hr fun a ha => wp_vop (d:=.v24) rfl fun b hb => ?_
  have hpre : VChg [.v27,.v24] s b := ha.chg.trans hb.chg
  refine reduce_ok (by intro e he; rw [hpre.get .v31 (by decide)]; exact hq e he)
    (by intro e he; rw [hpre.get .v8 (by decide)]; exact hc e he) fun c hcc hv => ?_
  have hh : VChg [.v24,.v25,.v27] s c := (hpre.trans hcc).mono (by decide)
  have hval : c.v .v24=laneVector (zInput s raw off) := by
    apply vec_ext
    intro e he
    rw [laneVector_word _ he,hv e he,hb.v,VG.AArch64.vword_map2 _ _ _ he,
      ha.get raw hne,ha.v]
    rfl
  refine wp_strq ho rfl (by simpa only [hh.wr,hh.gpr] using hw) fun d hd => ?_
  refine norm_ok fun t ht hn => ?_
  refine k t ?_ ?_ ?_
  · exact (((StepKeep.ofChg hh (by decide)).trans (StepKeep.ofMem hd)).trans
      (StepKeep.ofChg ht (by decide))).mono (by decide)
  · rw [ht.mem,hd.mem,hh.mem,hh.gpr,hval]
  · intro e he
    rw [hn e he,hd.v,hh.get .v30 (by decide),hh.get .v9 (by decide),
      hh.get .v10 (by decide),hval,laneVector_word _ he]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
