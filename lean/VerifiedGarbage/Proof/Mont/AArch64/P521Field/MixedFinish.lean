module

-- separate module: The checked mixed-add return/output/context composition costs 0.96s of proof versus 0.47s of imports; MixedFunction entry/ABI edits reuse this exit certificate.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedMux
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Block

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Ed25519.AArch64

def mixedTailCode : List Instr := ((mixedFnBlocks.drop 134).flatten.drop 9).take 124

theorem mixedTail_source : mixedTailCode=(mixedFnBlocks.flatten.drop 4297).take 124 := by
  have h := drop_flatten_prefix mixedFnBlocks 134 4288 9
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 124) h.symm

theorem mixedTail_split : mixedTailCode=mixedZeroCode++mixedMuxCode := by decide

theorem mixedTail_novec : ∀i∈mixedTailCode,vdstOf i=none := by
  have h : mixedTailCode.all (fun i => vdstOf i==none)=true := by decide
  simpa only [List.all_eq_true,beq_iff_eq] using h

theorem mixed_tail_arith {s : State} {pz pa pb po : Addr} {zin size cap room : Nat}
    (hz : Ptr s .x27 pz zin) (hp : Ptr s .x30 pa size) (hq : Ptr s .x28 pb cap) (ho : PtrW s .x26 po room)
    (hzsize : 216≤zin) (ha : 432≤size) (hb : 144≤cap) (hout : 216≤room)
    (stableZ : ∀m,Outside po 0 144 s.mem m → wordsVal m pa 360 9=wordsVal s.mem pa 360 9) :
    WP isa (.block mixedTailCode) s fun t =>
      wordsVal t.mem po 0 9=(if wordsVal s.mem pz 144 9=0 then wordsVal s.mem pb 0 9 else wordsVal s.mem pa 0 9) ∧
      wordsVal t.mem po 72 9=(if wordsVal s.mem pz 144 9=0 then wordsVal s.mem pb 72 9 else wordsVal s.mem pa 288 9) ∧
      wordsVal t.mem po 144 9=(if wordsVal s.mem pz 144 9=0 then 1 else wordsVal s.mem pa 360 9) ∧
      KeepRegs mixedMuxClob s t ∧ Outside po 0 216 s.mem t.mem := by
  rw [mixedTail_split,WP.block_append_iff]
  refine WP.mono (mixed_zero_ok hz hzsize) fun u ⟨zero,ku⟩ => ?_
  refine WP.mono (mixed_mux_ok (hp.of_keeps ku (by decide)) (hq.of_keeps ku (by decide))
    (ho.of_keepRegs (Keeps.regs ku) (by decide)) ha hb hout
    (by intro m hm; rw [ku.mem] at hm ⊢; exact stableZ m hm)) fun t ⟨x,y,z,_,kt,ot⟩ => ?_
  rw [zero,ku.mem] at x y z
  simp only [decide_eq_true_eq] at x y z
  exact ⟨x,y,z,((Keeps.regs ku).mono (by decide)).trans kt,by rw [ku.mem] at ot; exact ot⟩

theorem mixed_tail_ok {s : State} {pz pa pb po : Addr} {zin size cap room : Nat}
    (hz : Ptr s .x27 pz zin) (hp : Ptr s .x30 pa size) (hq : Ptr s .x28 pb cap) (ho : PtrW s .x26 po room)
    (hzsize : 216≤zin) (ha : 432≤size) (hb : 144≤cap) (hout : 216≤room)
    (stableZ : ∀m,Outside po 0 144 s.mem m → wordsVal m pa 360 9=wordsVal s.mem pa 360 9) :
    WP isa (.block mixedTailCode) s fun t =>
      wordsVal t.mem po 0 9=(if wordsVal s.mem pz 144 9=0 then wordsVal s.mem pb 0 9 else wordsVal s.mem pa 0 9) ∧
      wordsVal t.mem po 72 9=(if wordsVal s.mem pz 144 9=0 then wordsVal s.mem pb 72 9 else wordsVal s.mem pa 288 9) ∧
      wordsVal t.mem po 144 9=(if wordsVal s.mem pz 144 9=0 then 1 else wordsVal s.mem pa 360 9) ∧
      KeepRegs mixedMuxClob s t ∧ Outside po 0 216 s.mem t.mem ∧ t.v=s.v := by
  exact WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec mixedTail_novec
    (mixed_tail_arith hz hp hq ho hzsize ha hb hout stableZ))
    (fun t ⟨⟨x,y,z,k,o⟩,v⟩ => ⟨x,y,z,k,o,v⟩)

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (lane)

def mixedFinishCode : List Instr := ((mixedFnBlocks.drop 134).flatten.drop 9).take 136

def mixedFinishClob : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,
  .x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x30]

theorem mixedFinish_source : mixedFinishCode=(mixedFnBlocks.flatten.drop 4297).take 136 := by
  have h := drop_flatten_prefix mixedFnBlocks 134 4288 9
    (by rw [List.length_flatten]; lit_decide)
  simp only [Nat.reduceAdd] at h
  exact congrArg (List.take 136) h.symm

theorem mixedFinish_split : mixedFinishCode=mixedTailCode++mixedExit := by decide

theorem mixed_finish_ok {caller s : State} {pz pa pb po : Addr} {zin size cap room : Nat}
    (hz : Ptr s .x27 pz zin) (hp : Ptr s .x30 pa size) (hq : Ptr s .x28 pb cap) (ho : PtrW s .x26 po room)
    (hzsize : 216≤zin) (ha : 432≤size) (hb : 144≤cap) (hout : 216≤room)
    (stableZ : ∀m,Outside po 0 144 s.mem m → wordsVal m pa 360 9=wordsVal s.mem pa 360 9)
    (workspace : (s.v .v25).extractLsb' 0 64=caller.gpr .x0)
    (link : (s.v .v24).extractLsb' 0 64=caller.gpr .x30)
    (saved : ∀i (h : i<nativeSaved.length),lane s.v i=caller.gpr nativeSaved[i]) :
    WP isa (.block mixedFinishCode) s fun t =>
      wordsVal t.mem po 0 9=(if wordsVal s.mem pz 144 9=0 then wordsVal s.mem pb 0 9 else wordsVal s.mem pa 0 9) ∧
      wordsVal t.mem po 72 9=(if wordsVal s.mem pz 144 9=0 then wordsVal s.mem pb 72 9 else wordsVal s.mem pa 288 9) ∧
      wordsVal t.mem po 144 9=(if wordsVal s.mem pz 144 9=0 then 1 else wordsVal s.mem pa 360 9) ∧
      t.gpr .x0=caller.gpr .x0 ∧ t.gpr .x30=caller.gpr .x30 ∧
      (∀r∈nativeSaved,t.gpr r=caller.gpr r) ∧ KeepRegs mixedFinishClob s t ∧
      Outside po 0 216 s.mem t.mem ∧ t.v=s.v := by
  rw [mixedFinish_split,WP.block_append_iff]
  refine WP.mono (mixed_tail_ok hz hp hq ho hzsize ha hb hout stableZ) fun u ⟨x,y,z,k,o,v⟩ => ?_
  refine WP.mono (mixed_exit_restores caller u (by rw [v]; exact workspace)
    (by rw [v]; exact link) (by intro i hi; rw [v]; exact saved i hi))
    fun t ⟨base,lr,regs,kt,vt⟩ => ?_
  rw [←kt.mem] at x y z o
  exact ⟨x,y,z,base,lr,regs,(k.mono (by decide)).trans ((Keeps.regs kt).mono (by decide)),o,vt.trans v⟩

end VG.Proof.Mont.AArch64.P521Field
