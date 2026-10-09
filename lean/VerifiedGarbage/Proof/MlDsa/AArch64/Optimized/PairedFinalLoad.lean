import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedStore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalArithmetic

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def readPair (m : Mem) (base : Addr) (stride : Nat) : Values := fun p => Vector.ofFn fun j =>
  m.read (base+BitVec.ofNat 64 (1024*p.val+stride*j.val)) 16

def finalLoads : List Instr := (pairStores 128).map (fun p => Instr.ldrq p.1 .x2 p.2)

theorem finalLoads_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hr : ∀p:Fin 2,∀j:Fin 8,InRegions (s.rd++s.wr)
      (s.gpr .x2+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (k : ∀t,VChg ((pairStores 128).map Prod.fst) s t →
      Banks t (readPair s.mem (s.gpr .x2) 128) → WP isa (.block rest) t Q) :
    WP isa (.block (finalLoads++rest)) s Q := by
  refine load_many_ok _ _ (by decide) (by decide) ?_ fun t ht hv => k t ht ?_
  · intro r hm
    obtain ⟨p,j,rfl⟩ := pairStores_mem.mp hm
    exact hr p j
  · intro p j
    simp only [readPair,Vector.getElem_ofFn]
    exact hv _ (pairStores_mem.mpr ⟨p,j,rfl⟩)

theorem finalLoadArithmetic_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hr : ∀p:Fin 2,∀j:Fin 8,InRegions (s.rd++s.wr)
      (s.gpr .x2+BitVec.ofNat 64 (1024*p.val+128*j.val)) 16)
    (ht : ∀i:Fin 7,RootReady s (32*i.val) (Inverse.finalZ i.val))
    (hs : RootReady s 224 (fun _ => 16382))
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg stageRunRegs s t → Banks t (fun p =>
      Inverse.rawFinalValues (readPair s.mem (s.gpr .x2) 128 p)) → WP isa (.block rest) t Q) :
    WP isa (.block (finalLoads++finalArithmetic++rest)) s Q := by
  rw [List.append_assoc]
  refine finalLoads_ok hr fun a ha va => ?_
  refine finalArithmetic_ok va (fun i => (ht i).chg ha) (hs.chg ha) ?_ fun t hb vb => ?_
  · rw [ha.get .v31 (by decide)]; exact hq
  · exact k t ((ha.trans hb).mono (by decide)) vb

end VG.Proof.MlDsa.AArch64.Optimized.Paired
