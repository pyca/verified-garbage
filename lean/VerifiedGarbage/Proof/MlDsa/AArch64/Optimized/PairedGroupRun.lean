import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedGroupBank

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase

def groupRegs : List VReg := (List.range 16).map vr++[.v24,.v25,.v26,.v27]
def groupCode (ps : List (Fin 8 × Fin 8)) : List Instr := ps.flatMap fun (i,j) => batchPair i.val j.val

def groupValues (v : Vector (BitVec 128) 8) (z : Nat → Int) : List (Fin 8 × Fin 8) → Vector (BitVec 128) 8
  | [] => v
  | (i,j)::ps => groupValues (pairValues v i j z) z ps

theorem group_subset (i j : Fin 8) : groupClobs i j⊆groupRegs := by
  exact (show ∀i j:Fin 8,groupClobs i j⊆groupRegs by decide) i j

theorem groupRun_ok (ps : List (Fin 8 × Fin 8)) (hn : ∀p∈ps,p.1≠p.2)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values} {z : Nat → Int}
    (hv : Banks s v) (hz : ∀e<4,0≤z e ∧ z e<8380417)
    (hzw : ∀e<4,vword (s.v .v28) e=BitVec.ofInt 32 (z e))
    (hbw : ∀e<4,vword (s.v .v29) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg groupRegs s t → Banks t (fun p => groupValues (v p) z ps) →
      WP isa (.block rest) t Q) :
    WP isa (.block (groupCode ps++rest)) s Q := by
  induction ps generalizing s v with
  | nil => exact k s (VChg.refl _ _) hv
  | cons op ps ih =>
    simp only [groupCode,List.flatMap_cons,List.append_assoc]
    refine groupBank_ok op.1 op.2 (hn op (by simp)) hv hz hzw hbw hqw fun a ha va => ?_
    have hc : VChg groupRegs s a := ha.mono (group_subset _ _)
    refine ih (fun p hp => hn p (List.mem_cons_of_mem _ hp)) va ?_ ?_ ?_ fun t ht vt => ?_
    · rw [hc.get .v28 (by decide)]; exact hzw
    · rw [hc.get .v29 (by decide)]; exact hbw
    · rw [hc.get .v31 (by decide)]; exact hqw
    · exact k t ((hc.trans ht).mono (by simp)) vt

end VG.Proof.MlDsa.AArch64.Optimized.Paired
