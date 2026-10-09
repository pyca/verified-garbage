import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedState
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Loads

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VMem)

def pairStores (stride : Nat) : List (VReg × Nat) :=
  (List.finRange 2).flatMap fun p => (List.finRange 8).map fun j =>
    ((bankRegs p)[j.val],1024*p.val+stride*j.val)

def writePair (v : Values) (base : Addr) (stride : Nat) (m : Mem) : Mem :=
  (List.finRange 2).foldl (fun m p => (List.finRange 8).foldl
    (fun m j => m.write (base+BitVec.ofNat 64 (1024*p.val+stride*j.val)) 16 ((v p)[j.val])) m) m

theorem writeSlice_pair {s : State} {v : Values} (hv : Banks s v) (base : Addr) (stride : Nat) :
    writeSlice (pairStores stride) base s.v s.mem=writePair v base stride s.mem := by
  simp only [writeSlice,pairStores,List.foldl_flatMap,List.foldl_map,writePair]
  congr 1
  funext m p
  congr 1
  funext m j
  rw [hv p j]

theorem pairStores_mem {stride : Nat} {r : VReg × Nat} : r∈pairStores stride ↔
    ∃p:Fin 2,∃j:Fin 8,r=((bankRegs p)[j.val],1024*p.val+stride*j.val) := by
  simp only [pairStores,List.mem_flatMap,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨p,j,hj⟩; exact ⟨p,j,hj.symm⟩
  · rintro ⟨p,j,rfl⟩; exact ⟨p,j,rfl⟩

theorem storePair_ok (stride : Nat) (base : Reg)
    (ho : ∀p:Fin 2,∀j:Fin 8,(1024*p.val+stride*j.val)%16=0 ∧ 1024*p.val+stride*j.val<65536)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values} (hv : Banks s v)
    (hr : ∀p:Fin 2,∀j:Fin 8,InRegions s.wr (s.gpr base+BitVec.ofNat 64 (1024*p.val+stride*j.val)) 16)
    (k : ∀t,VMem s t (writePair v (s.gpr base) stride s.mem) → WP isa (.block rest) t Q) :
    WP isa (.block ((pairStores stride).map (fun p => Instr.strq p.1 base p.2)++rest)) s Q := by
  refine store_many_ok _ _ ?_ ?_ fun t ht => k t ?_
  · intro r hr
    obtain ⟨p,j,rfl⟩ := pairStores_mem.mp hr
    exact ho p j
  · intro r hmem
    obtain ⟨p,j,rfl⟩ := pairStores_mem.mp hmem
    exact hr p j
  · rw [writeSlice_pair hv] at ht
    exact ht

end VG.Proof.MlDsa.AArch64.Optimized.Paired
