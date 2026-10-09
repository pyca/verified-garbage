import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedGroup
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedState

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (PairRegs pairWrites)

def pairValues (v : Vector (BitVec 128) 8) (i j : Fin 8) (z : Nat → Int) : Vector (BitVec 128) 8 :=
  (v.set i.val (VArr.s4.map2 (fun _ a b => a+b) v[i.val] v[j.val])).set j.val
    (fastVector (VArr.s4.map2 (fun _ a b => a-b) v[i.val] v[j.val]) z)
def groupClobs (i j : Fin 8) : List VReg :=
  pairWrites (groupPairs i.val j.val)++(groupProducts j.val).map MulRegs.temp++
    (groupProducts j.val).map MulRegs.dest

theorem groupKeep (p : Fin 2) (i j k : Fin 8) (hki : k≠i) (hkj : k≠j) :
    (bankRegs p)[k.val]∉groupClobs i j := by
  have ht := bank_safe (j := 8*p.val+k.val) (by omega)
  have hn (q : Fin 2) (r : Fin 8) (hkr : k≠r) : vr (8*p.val+k.val)≠vr (8*q.val+r.val) := by
    intro h
    have he := bank_injective (by omega) (by omega) h
    apply hkr
    apply Fin.ext
    omega
  have h0i := hn 0 i hki
  have h0j := hn 0 j hkj
  have h1i := hn 1 i hki
  have h1j := hn 1 j hkj
  simp only [bankRegs,Vector.getElem_ofFn,groupClobs,pairWrites,groupPairs,groupProducts,
    PairRegs.writes,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_cons,List.map_nil,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
  grind only

theorem groupBank_ok (i j : Fin 8) (hij : i≠j)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values} {z : Nat → Int}
    (hv : Banks s v) (hz : ∀e<4,0≤z e ∧ z e<8380417)
    (hzw : ∀e<4,vword (s.v .v28) e=BitVec.ofInt 32 (z e))
    (hbw : ∀e<4,vword (s.v .v29) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg (groupClobs i j) s t → Banks t (fun p => pairValues (v p) i j z) →
      WP isa (.block rest) t Q) :
    WP isa (.block (batchPair i.val j.val++rest)) s Q := by
  rw [group_code]
  refine batch_ok _ _ (group_shape i j hij) hz hzw hbw hqw fun t hc ht => k t hc ?_
  intro p a
  have hp : ∃r∈groupPairs i.val j.val,r.left=(bankRegs p)[i.val] ∧ r.right=(bankRegs p)[j.val] := by
    have hp' : p=0 ∨ p=1 := by
      apply Or.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
      omega
    rcases hp' with rfl | rfl
    · exact ⟨⟨vr i.val,vr j.val,.v24⟩,by simp [groupPairs],by simp [bankRegs],by simp [bankRegs]⟩
    · exact ⟨⟨vr (8+i.val),vr (8+j.val),.v25⟩,by simp [groupPairs,Nat.add_comm],by simp [bankRegs],by simp [bankRegs]⟩
  obtain ⟨r,hr,hri,hrj⟩ := hp
  have hh := ht r hr
  rw [hri,hrj,hv p i,hv p j] at hh
  simp only [pairValues,Vector.getElem_set]
  by_cases haj : a=j
  · subst a
    simp only [ite_true]
    exact hh.2
  · have haj' : j.val≠a.val := fun h => haj (Fin.ext h).symm
    simp only [haj',ite_false]
    by_cases hai : a=i
    · subst a
      simp only [ite_true]
      exact hh.1
    · have hai' : i.val≠a.val := fun h => hai (Fin.ext h).symm
      simp only [hai',ite_false]
      rw [hc.get _ (groupKeep p i j a hai haj),hv p a]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
