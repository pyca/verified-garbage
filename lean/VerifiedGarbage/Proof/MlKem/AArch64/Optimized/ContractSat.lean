module
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Contracts
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.ConstsSat
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64

def addTables (s : State) : State :=
 {s with mem:=tableMem,syms:=tableSyms,rd:=s.rd++Abi.constRegions tableSyms constants}

theorem strip_addTables (s : State) : stripConsts constants (addTables s) =
 {s with mem:=tableMem,syms:=tableSyms} := by
 have hl : (Abi.constRegions tableSyms constants).length=constants.length := by
  simp only [Abi.constRegions,List.length_map]
 simp only [stripConsts,addTables,State.withRegions,List.length_append,hl,Nat.add_sub_cancel,List.take_left]

theorem keyGen768_sat : ∃s,keyGen768Contract.pre s := by
 refine ⟨addTables VG.Proof.MlKem.AArch64.KeyGen.sat,?_⟩
 unfold keyGen768Contract Spec.MlKem.keyGenContract constants
 apply pre_consts.mpr
 constructor
 · change (Spec.MlKem.keyGenContract abi 16).pre (stripConsts constants (addTables VG.Proof.MlKem.AArch64.KeyGen.sat))
   rw [strip_addTables]
   sig_pre [Spec.MlKem.keyGenSig,abi,argRegs]
   and_intros
   all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
 · change ConstsOk constants 16 (addTables VG.Proof.MlKem.AArch64.KeyGen.sat)
   refine ⟨?_,tableMem_held,?_⟩
   · rfl
   · intro r hr
     rw [constants_regions] at hr
     rcases hr with _|⟨_,_|⟨_,_|⟨_,_|h⟩⟩⟩
     all_goals first
      | contradiction
      | (refine ⟨by decide,?_,?_⟩
         · intro q hq
           change q∈VG.Proof.MlKem.AArch64.KeyGen.sat.wr at hq
           simp only [VG.Proof.MlKem.AArch64.KeyGen.sat,List.mem_cons,List.not_mem_nil,or_false] at hq
           rcases hq with rfl|rfl|rfl <;> exact Region.disjoint_of_sep (by decide)
         · intro q hq
           change q∈[below (0x100000:Addr) 16] at hq
           rw [List.mem_singleton.mp hq]
           exact Region.disjoint_of_sep (by decide))

theorem decaps768_sat : ∃s,decaps768Contract.pre s := by
 refine ⟨addTables VG.Proof.MlKem.AArch64.Decaps.sat,?_⟩
 unfold decaps768Contract Spec.MlKem.decapsContract constants
 apply pre_consts.mpr
 constructor
 · change (Spec.MlKem.decapsContract abi 16).pre (stripConsts constants (addTables VG.Proof.MlKem.AArch64.Decaps.sat))
   rw [strip_addTables]
   sig_pre [Spec.MlKem.decapsSig,abi,argRegs]
   and_intros
   all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
 · change ConstsOk constants 16 (addTables VG.Proof.MlKem.AArch64.Decaps.sat)
   refine ⟨?_,tableMem_held,?_⟩
   · rfl
   · intro r hr
     rw [constants_regions] at hr
     rcases hr with _|⟨_,_|⟨_,_|⟨_,_|h⟩⟩⟩
     all_goals first
      | contradiction
      | (refine ⟨by decide,?_,?_⟩
         · intro q hq
           change q∈VG.Proof.MlKem.AArch64.Decaps.sat.wr at hq
           simp only [VG.Proof.MlKem.AArch64.Decaps.sat,List.mem_cons,List.not_mem_nil,or_false] at hq
           rcases hq with rfl|rfl|rfl <;> exact Region.disjoint_of_sep (by decide)
         · intro q hq
           change q∈[below (0x100000:Addr) 16] at hq
           rw [List.mem_singleton.mp hq]
           exact Region.disjoint_of_sep (by decide))

theorem keyGen1024_sat : ∃s,keyGen1024Contract.pre s := by
 refine ⟨addTables VG.Proof.MlKem1024.AArch64.KeyGen.sat,?_⟩
 unfold keyGen1024Contract Spec.MlKem1024.keyGenContract constants
 apply pre_consts.mpr
 constructor
 · change (Spec.MlKem1024.keyGenContract abi 16).pre (stripConsts constants (addTables VG.Proof.MlKem1024.AArch64.KeyGen.sat))
   rw [strip_addTables]
   sig_pre [Spec.MlKem1024.keyGenSig,abi,argRegs]
   and_intros
   all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
 · change ConstsOk constants 16 (addTables VG.Proof.MlKem1024.AArch64.KeyGen.sat)
   refine ⟨?_,tableMem_held,?_⟩
   · rfl
   · intro r hr
     rw [constants_regions] at hr
     rcases hr with _|⟨_,_|⟨_,_|⟨_,_|h⟩⟩⟩
     all_goals first
      | contradiction
      | (refine ⟨by decide,?_,?_⟩
         · intro q hq
           change q∈VG.Proof.MlKem1024.AArch64.KeyGen.sat.wr at hq
           simp only [VG.Proof.MlKem1024.AArch64.KeyGen.sat,List.mem_cons,List.not_mem_nil,or_false] at hq
           rcases hq with rfl|rfl|rfl <;> exact Region.disjoint_of_sep (by decide)
         · intro q hq
           change q∈[below (0x100000:Addr) 16] at hq
           rw [List.mem_singleton.mp hq]
           exact Region.disjoint_of_sep (by decide))

theorem decaps1024_sat : ∃s,decaps1024Contract.pre s := by
 refine ⟨addTables VG.Proof.MlKem1024.AArch64.Decaps.sat,?_⟩
 unfold decaps1024Contract Spec.MlKem1024.decapsContract constants
 apply pre_consts.mpr
 constructor
 · change (Spec.MlKem1024.decapsContract abi 16).pre (stripConsts constants (addTables VG.Proof.MlKem1024.AArch64.Decaps.sat))
   rw [strip_addTables]
   sig_pre [Spec.MlKem1024.decapsSig,abi,argRegs]
   and_intros
   all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
 · change ConstsOk constants 16 (addTables VG.Proof.MlKem1024.AArch64.Decaps.sat)
   refine ⟨?_,tableMem_held,?_⟩
   · rfl
   · intro r hr
     rw [constants_regions] at hr
     rcases hr with _|⟨_,_|⟨_,_|⟨_,_|h⟩⟩⟩
     all_goals first
      | contradiction
      | (refine ⟨by decide,?_,?_⟩
         · intro q hq
           change q∈VG.Proof.MlKem1024.AArch64.Decaps.sat.wr at hq
           simp only [VG.Proof.MlKem1024.AArch64.Decaps.sat,List.mem_cons,List.not_mem_nil,or_false] at hq
           rcases hq with rfl|rfl|rfl <;> exact Region.disjoint_of_sep (by decide)
         · intro q hq
           change q∈[below (0x100000:Addr) 16] at hq
           rw [List.mem_singleton.mp hq]
           exact Region.disjoint_of_sep (by decide))
end VG.Proof.MlKem.AArch64.Optimized
