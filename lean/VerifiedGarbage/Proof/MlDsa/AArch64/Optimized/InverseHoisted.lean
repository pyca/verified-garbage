import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseInitConst
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Loads

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def tailRootReg (j : Nat) : VReg := if j=0 then .v22 else .v23
def tailRecipReg (j : Nat) : VReg := if j=0 then .v28 else .v29

def Hoisted (s : State) : Prop := ∀ j : Fin 2, ∀ e<4,
  vword (s.v (tailRootReg j.val)) e=BitVec.ofInt 32 (VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (7-(4*j.val+e)) : Int) ∧
  vword (s.v (tailRecipReg j.val)) e=BitVec.ofInt 32 (reciprocal (VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (7-(4*j.val+e)) : Int))

def tailLoads : List (VReg × Nat) := [(.v22,0),(.v23,16),(.v28,32),(.v29,48)]
def tailLoadCode : List Instr := tailLoads.map fun p => Instr.ldrq p.1 .x1 p.2

theorem tailLoads_mem (j : Fin 2) :
    (tailRootReg j.val,16*j.val)∈tailLoads ∧ (tailRecipReg j.val,32+16*j.val)∈tailLoads := by
  revert j
  decide +kernel

theorem tailLoad_ok {s : State} {p : Addr} {rest : List Instr} {Q : State → Prop}
    (ht : InverseTable.Words s.mem p) (hx : s.gpr .x1=p+3840)
    (hr : ∀ off∈[0,16,32,48], InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (k : ∀ t, VChg [.v22,.v23,.v28,.v29] s t → Hoisted t → WP isa (.block rest) t Q) :
    WP isa (.block (tailLoadCode ++ rest)) s Q := by
  unfold tailLoadCode
  refine load_many_ok tailLoads .x1 (by decide) (by decide) ?_ fun t hc hv => ?_
  · intro a ha
    exact hr a.2 (by simpa only [tailLoads,List.map_cons,List.map_nil,Prod.snd,List.mem_cons,List.not_mem_nil,or_false] using
      List.mem_map_of_mem (f := Prod.snd) ha)
  · refine k t hc ?_
    intro j e he
    rw [hv _ (tailLoads_mem j).1,hv _ (tailLoads_mem j).2,hx]
    have h := nat_row (n := VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (7-(4*j.val+e)))
      (ht.tail (j := j.val) (e := e) j.isLt he)
    change vword (s.mem.read ((p+BitVec.ofNat 64 3840)+BitVec.ofNat 64 (16*j.val)) 16) e=_ ∧
      vword (s.mem.read ((p+BitVec.ofNat 64 3840)+BitVec.ofNat 64 (32+16*j.val)) 16) e=_
    rw [BitVec.add_assoc,← BitVec.ofNat_add,BitVec.add_assoc,← BitVec.ofNat_add]
    rw [show 3840+(32+16*j.val)=3872+16*j.val by omega]
    exact h

theorem Hoisted.frame {s t : State} {vs : List VReg} (h : Hoisted s) (hc : VChg vs s t)
    (hv : ∀ r∈[VReg.v22,.v23,.v28,.v29], r∉vs) : Hoisted t := by
  intro j e he
  have hr : tailRootReg j.val∈[VReg.v22,.v23,.v28,.v29] :=
    (show ∀ j : Fin 2, tailRootReg j.val∈[VReg.v22,.v23,.v28,.v29] by decide +kernel) j
  have hb : tailRecipReg j.val∈[VReg.v22,.v23,.v28,.v29] :=
    (show ∀ j : Fin 2, tailRecipReg j.val∈[VReg.v22,.v23,.v28,.v29] by decide +kernel) j
  rw [hc.get _ (hv _ hr),hc.get _ (hv _ hb)]
  exact h j e he


def sourceGroup (i : Nat) : Nat := if i<4 then 0 else 1
def sourceLane (i : Nat) : Nat := if i<4 then i else i-4

theorem hoisted_source_geometry (i : Fin 7) (hi : i.val<6) :
    sourceGroup i.val<2 ∧ sourceLane i.val<4 ∧
    finalRootReg i.val=tailRootReg (sourceGroup i.val) ∧
    finalRecipReg i.val=tailRecipReg (sourceGroup i.val) ∧
    finalRootLane i.val=sourceLane i.val ∧ finalRecipLane i.val=sourceLane i.val := by
  exact (show ∀ i : Fin 7, i.val<6 →
    sourceGroup i.val<2 ∧ sourceLane i.val<4 ∧
    finalRootReg i.val=tailRootReg (sourceGroup i.val) ∧
    finalRecipReg i.val=tailRecipReg (sourceGroup i.val) ∧
    finalRootLane i.val=sourceLane i.val ∧ finalRecipLane i.val=sourceLane i.val by decide +kernel) i hi

theorem hoisted_source_value (i : Nat) (hi : i<6) :
    finalZ i 0=(VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (7-(4*sourceGroup i+sourceLane i)) : Int) := by
  unfold finalZ finalValue sourceGroup sourceLane
  by_cases h : i<4
  · simp only [h,ite_true]
    rw [show 4*0+i=i by omega]
  · simp only [h,hi,ite_false,ite_true]
    rw [show 7-(4*1+(i-4))=3-(i-4) by omega]

theorem Hoisted.finalRoots {s : State} (h : Hoisted s)
    (hc : s.v .v30=scaleVector) (hq : ∀ e<4, vword (s.v .v31) e=8380417#32) : FinalRoots s := by
  have hs := scaleVector_folded hc
  have hpair (i : Fin 7) :
      vword (s.v (finalRootReg i.val)) (finalRootLane i.val)=BitVec.ofInt 32 (finalZ i.val 0) ∧
      vword (s.v (finalRecipReg i.val)) (finalRecipLane i.val)=BitVec.ofInt 32 (reciprocal (finalZ i.val 0)) := by
    by_cases hi : i.val<6
    · obtain ⟨hj,he,hr,hb,hl,hl'⟩ := hoisted_source_geometry i hi
      rw [hr,hb,hl,hl',hoisted_source_value i.val hi]
      exact h ⟨sourceGroup i.val,hj⟩ (sourceLane i.val) he
    · have he : i.val=6 := by omega
      simp only [he]
      exact hs
  exact ⟨fun i => (hpair i).1,fun i => (hpair i).2,hq⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
