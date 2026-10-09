import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Loads
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterRun

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def bankLoads (regs : Vector VReg 8) (stride : Nat) : List (VReg × Nat) :=
  (List.finRange 8).map (fun i => (regs[i.val], stride*i.val))

def readBank (m : Mem) (base : Addr) (stride : Nat) : Vector (BitVec 128) 8 :=
  Vector.ofFn (fun i => m.read (base + BitVec.ofNat 64 (stride*i.val)) 16)

theorem bankLoads_mem {regs : Vector VReg 8} {stride : Nat} {p : VReg × Nat} :
    p ∈ bankLoads regs stride ↔ ∃ i : Fin 8, p = (regs[i.val],stride*i.val) := by
  simp only [bankLoads, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, hi.symm⟩
  · rintro ⟨i, hi⟩; exact ⟨i, hi.symm⟩

theorem loadBank_ok (regs : Vector VReg 8) (stride : Nat) (base : Reg)
    (hi : Function.Injective (fun i : Fin 8 => regs[i.val]))
    (ho : ∀ i : Fin 8, (stride*i.val)%16=0 ∧ stride*i.val<65536)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hr : ∀ i : Fin 8, InRegions (s.rd++s.wr)
      (s.gpr base + BitVec.ofNat 64 (stride*i.val)) 16)
    (k : ∀ t, VChg ((bankLoads regs stride).map Prod.fst) s t →
      Bank t regs (readBank s.mem (s.gpr base) stride) → WP isa (.block rest) t Q) :
    WP isa (.block ((bankLoads regs stride).map (fun p => Instr.ldrq p.1 base p.2) ++ rest)) s Q := by
  have hd : ((bankLoads regs stride).map Prod.fst).Nodup := by
    simp only [bankLoads, List.map_map, Function.comp_def]
    exact List.Pairwise.map (S := fun a b : VReg => a ≠ b) (fun i : Fin 8 => regs[i.val])
      (fun _ _ hne he => hne (hi he)) (List.nodup_finRange 8)
  refine load_many_ok _ _ hd ?_ ?_ fun t hc hv => k t hc ?_
  · intro p hp
    obtain ⟨i, rfl⟩ := bankLoads_mem.mp hp
    exact ho i
  · intro p hp
    obtain ⟨i, rfl⟩ := bankLoads_mem.mp hp
    exact hr i
  · intro i
    simpa only [readBank, Vector.getElem_ofFn] using hv _ (bankLoads_mem.mpr ⟨i,rfl⟩)

/-- Store values by logical bank index. Physical register renaming does not
change this memory function. -/
def writeBank (values : Vector (BitVec 128) 8) (base : Addr) (stride : Nat) (m : Mem) : Mem :=
  (List.finRange 8).foldl
    (fun m i => m.write (base + BitVec.ofNat 64 (stride*i.val)) 16 values[i.val]) m

theorem writeSlice_bank {s : State} {regs : Vector VReg 8} {values : Vector (BitVec 128) 8}
    (hb : Bank s regs values) (base : Addr) (stride : Nat) :
    writeSlice (bankLoads regs stride) base s.v s.mem = writeBank values base stride s.mem := by
  simp only [writeSlice, bankLoads, List.foldl_map, writeBank]
  congr 1
  funext m i
  rw [hb i]

theorem storeBank_ok (regs : Vector VReg 8) (stride : Nat) (base : Reg)
    (ho : ∀ i : Fin 8, (stride*i.val)%16=0 ∧ stride*i.val<65536)
    {s : State} {rest : List Instr} {Q : State → Prop} {values : Vector (BitVec 128) 8}
    (hb : Bank s regs values)
    (hr : ∀ i : Fin 8, InRegions s.wr
      (s.gpr base + BitVec.ofNat 64 (stride*i.val)) 16)
    (k : ∀ t, VMem s t (writeBank values (s.gpr base) stride s.mem) → WP isa (.block rest) t Q) :
    WP isa (.block ((bankLoads regs stride).map (fun p => Instr.strq p.1 base p.2) ++ rest)) s Q := by
  refine store_many_ok _ _ ?_ ?_ fun t hc => k t ?_
  · intro p hp
    obtain ⟨i,rfl⟩ := bankLoads_mem.mp hp
    exact ho i
  · intro p hp
    obtain ⟨i,rfl⟩ := bankLoads_mem.mp hp
    exact hr i
  · rw [writeSlice_bank hb] at hc
    exact hc

end VG.Proof.MlDsa.AArch64.Optimized
