import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedStage
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPackedRoot
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRun

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase

def stageRunRegs : List VReg := [.v28,.v29]++groupRegs

def stageRunCode (off : Fin 7 → Nat) (is : List (Fin 7)) : List Instr :=
  is.flatMap fun i => rootPair (off i)++groupCode (stagePairs i)

def stageRunValues (v : Vector (BitVec 128) 8) (z : Fin 7 → Nat → Int) :
    List (Fin 7) → Vector (BitVec 128) 8
  | [] => v
  | i::is => stageRunValues (Inverse.stageValues i.val v (z i)) z is

theorem stageRun_ok (is : List (Fin 7)) (off : Fin 7 → Nat) (z : Fin 7 → Nat → Int)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values}
    (hv : Banks s v) (hr : ∀i,RootReady s (off i) (z i))
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg stageRunRegs s t → Banks t (fun p => stageRunValues (v p) z is) →
      WP isa (.block rest) t Q) :
    WP isa (.block (stageRunCode off is++rest)) s Q := by
  induction is generalizing s v with
  | nil => exact k s (VChg.refl _ _) hv
  | cons i is ih =>
    simp only [stageRunCode,List.flatMap_cons,List.append_assoc]
    refine rootLoads_ok (off i) (hr i).align (hr i).limit (hr i).rootRead (hr i).recipRead
      fun a ha hz hb => ?_
    refine stage_ok i (hv.roots ha) (hr i).bound ?_ ?_ ?_ fun b hbb vb => ?_
    · rw [hz]; exact (hr i).root
    · rw [hb]; exact (hr i).recip
    · rw [ha.get .v31 (by decide)]; exact hq
    have hc : VChg stageRunRegs s b := ha.trans hbb
    refine ih vb (fun j => (hr j).chg hc) ?_ fun t ht vt => ?_
    · rw [hc.get .v31 (by decide)]; exact hq
    · exact k t ((hc.trans ht).mono (by simp)) vt

theorem stageRunValues_all (v : Vector (BitVec 128) 8) (z : Nat → Nat → Int) :
    stageRunValues v (fun i => z i.val) (List.finRange 7)=Inverse.runValues z 0 7 v := by
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
