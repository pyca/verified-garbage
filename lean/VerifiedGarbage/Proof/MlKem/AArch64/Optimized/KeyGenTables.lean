module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenRows
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Readonly gamma data through the fused key-generation rows -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay}

structure RowTable (P : KemLay) (s₀ s : State) : Prop where
  table : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA")
  read : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr)
  apart : ∀ i < P.k, ∀ r ∈ rowWrites P s₀ i, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r

theorem RowTable.frame {s₀ s t : State} {i : Nat} (hi : i < P.k)
    (h : RowTable P s₀ s) (hs : t.syms = s.syms)
    (hk : KB P s₀ s) (hk' : KB P s₀ t)
    (hf : Frame (rowWrites P s₀ i) s.mem t.mem) : RowTable P s₀ t := by
  refine ⟨?_,?_,?_⟩
  · rw [hs]
    intro j hj
    rw [←h.table j hj]
    exact hf.readW (r := ⟨s.syms "VG_MLKEM_GAMMA",512⟩)
      (contains_off (by omega) (by decide)) (h.apart i hi) (by decide)
  · simpa only [hs,hk'.rd,hk'.wr,←hk.rd,←hk.wr] using h.read
  · simpa only [hs] using h.apart

def RowsInv (P : KemLay) (s₀ : State) (mB : Mem) (v : BitVec 64) (i : Nat) (s : State) : Prop :=
  TL P s₀ mB v i s ∧ Errors P s₀ s ∧ RowTable P s₀ s

theorem rows_step {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB : Mem} {v : BitVec 64} {i : Nat} (hi : i < P.k) (h : RowsInv P s₀ mB v i s) :
    WP isa (Impl.MlKem.AArch64.Optimized.kgRow P i) s (RowsInv P s₀ mB v (i+1)) := by
  have ha : (polyRegion (s.gpr .x28+BitVec.ofNat 64 (TP P))).Disjoint
      ⟨s.syms "VG_MLKEM_GAMMA",512⟩ := by
    rw [h.1.c.kb.x28]
    exact (h.2.2.apart i hi _ (by simp [rowWrites])).symm
  refine WP.mono_syms (fused_row_ready hp hr hi h.1 h.2.1 h.2.2.table h.2.2.read ha) ?_
  intro t ht hs
  exact ⟨ht.1,ht.2.1,h.2.2.frame hi hs h.1.c.kb ht.1.c.kb ht.2.2⟩

theorem rows_ok {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB : Mem} {v : BitVec 64} (h : RowsInv P s₀ mB v 0 s) :
    WPs ((List.range P.k).map (Impl.MlKem.AArch64.Optimized.kgRow P)) s (RowsInv P s₀ mB v P.k) :=
  WPs.range (fun _ hi _ h => rows_step hp hr hi h) h

end VG.Proof.MlKem.AArch64.KeyGen
