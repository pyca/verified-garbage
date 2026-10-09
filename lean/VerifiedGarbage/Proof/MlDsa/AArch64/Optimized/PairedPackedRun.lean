import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPackedRoot
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePackedRun

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (PackedRoots packedOffset packedValues packedRunValues packedSteps)

def workRegs : List VReg := (List.range 16).map vr++[.v24,.v25,.v26,.v27,.v28,.v29]

theorem packedRoots_frame {s t : State} {z : Nat → Nat → Nat → Int}
    (h : PackedRoots s z) (hc : VChg workRegs s t) : PackedRoots t z := by
  refine ⟨?_,h.range,?_,?_,?_⟩
  · intro e he
    rw [hc.get .v31 (by decide)]
    exact h.q e he
  · simpa only [hc.rd,hc.wr,hc.gpr] using h.read
  · simpa only [hc.mem,hc.gpr] using h.root
  · simpa only [hc.mem,hc.gpr] using h.recip

def packedGroupCode (g : Fin 4) (len : Nat) : List Instr :=
  rootPair (packedOffset g.val len)++packedBothCode ⟨2*g.val,by omega⟩ ⟨2*g.val+1,by omega⟩ len

theorem packedRoot_subset (i j : Fin 8) : packedRootClobs i j⊆workRegs := by
  exact (show ∀i j:Fin 8,packedRootClobs i j⊆workRegs by decide) i j

theorem packedGroup_ok (g : Fin 4) (len : Nat) (hl : len=1 ∨ len=2)
    {s : State} {rest : List Instr} {Q : State → Prop}
    {v : Values} {z : Nat → Nat → Nat → Int}
    (hv : Banks s v) (hr : PackedRoots s z)
    (k : ∀t,VChg workRegs s t → PackedRoots t z →
      Banks t (fun p => packedValues (v p) ⟨2*g.val,by omega⟩ ⟨2*g.val+1,by omega⟩ len (z g.val len)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (packedGroupCode g len++rest)) s Q := by
  have ho : packedOffset g.val len%16=0 ∧ packedOffset g.val len+16<65536 := by
    rcases hl with rfl | rfl <;> simp [packedOffset] <;> omega
  have rr : RootReady s (packedOffset g.val len) (z g.val len) :=
    ⟨ho.1,ho.2,by simpa only [Nat.add_zero] using hr.read g.val g.isLt len hl 0 (Or.inl rfl),
      hr.read g.val g.isLt len hl 16 (Or.inr rfl),hr.range g.val g.isLt len hl,
      hr.root g.val g.isLt len hl,hr.recip g.val g.isLt len hl⟩
  unfold packedGroupCode
  refine packedRoot_ok _ _ len _ (by intro h; have hh := congrArg Fin.val h; change 2*g.val=2*g.val+1 at hh; omega)
    hv rr hr.q fun t ht hvt => ?_
  have hc : VChg workRegs s t := ht.mono (packedRoot_subset _ _)
  exact k t hc (packedRoots_frame hr hc) hvt

def packedCode (ps : List (Fin 4 × Nat)) : List Instr := ps.flatMap fun (g,len) => packedGroupCode g len

theorem packedRun_ok (ps : List (Fin 4 × Nat)) (hl : ∀p∈ps,p.2=1 ∨ p.2=2)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values} {z : Nat → Nat → Nat → Int}
    (hv : Banks s v) (hr : PackedRoots s z)
    (k : ∀t,VChg workRegs s t → PackedRoots t z →
      Banks t (fun p => packedRunValues (v p) z ps) → WP isa (.block rest) t Q) :
    WP isa (.block (packedCode ps++rest)) s Q := by
  induction ps generalizing s v with
  | nil => exact k s (VChg.refl _ _) hr hv
  | cons op ps ih =>
    simp only [packedCode,List.flatMap_cons,List.append_assoc]
    refine packedGroup_ok op.1 op.2 (hl op (by simp)) hv hr fun a ha ra va => ?_
    refine ih (fun p hp => hl p (List.mem_cons_of_mem _ hp)) va ra fun t ht rt vt => ?_
    exact k t ((ha.trans ht).mono (by simp)) rt vt

end VG.Proof.MlDsa.AArch64.Optimized.Paired
