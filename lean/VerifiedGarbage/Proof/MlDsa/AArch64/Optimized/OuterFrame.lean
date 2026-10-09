import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.OuterInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootTable

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64

structure HoistedTable (m : Mem) (p : Addr) (z : Nat → Int) : Prop where
  range : ∀ i < 8, 0 ≤ z (i+1) ∧ z (i+1) < 8380417
  roots : ∀ g < 4, ∀ e < 4,
    vword (m.read (p+BitVec.ofNat 64 (3840+16*g)) 16) e =
      if e%2=0 then BitVec.ofInt 32 (z (2*g+e/2+1))
      else BitVec.ofInt 32 (reciprocal (z (2*g+e/2+1)))

theorem HoistedTable.mem {s : State} {z : Nat → Int} (h : HoistedTable s.mem (s.gpr .x1) z)
    (hr : expandedRegion (s.gpr .x1) ∈ s.rd++s.wr)
    (hq : ∀ e < 4, vword (s.v .v16) e = 8380417#32) : HoistedMem s z := by
  refine ⟨h.range,hq,?_,h.roots⟩
  intro i
  exact ⟨_,hr,Offset.contains_base _ (by omega) (by omega)⟩

theorem outerPass_frame {m : Mem} {p : Addr} {r : Region} {z : Nat → Int} {N : Nat}
    (hcontains : ∀ u < N, ∀ i : Fin 8, r.Contains
      ((p+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16) :
    Frame [r] m (outerPassMem m p z N) := by
  induction N with
  | zero => exact Frame.refl _ _
  | succ N ih =>
    have hframe := ih (fun u hu i => hcontains u (by omega) i)
    simp only [outerPassMem,outerMemStep]
    exact writeBank_frame _ _ _ (by simp) (hcontains N (by omega)) hframe

def outputRegion (p : Addr) : Region := ⟨p,1024⟩

theorem outer_contains (p : Addr) {u : Nat} (hu : u<8) (i : Fin 8) :
    (outputRegion p).Contains ((p+BitVec.ofNat 64 (16*u))+BitVec.ofNat 64 (128*i.val)) 16 := by
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  exact Offset.contains_base p (by omega) (by omega)

theorem inner_output_contains (p : Addr) {u : Nat} (hu : u<8) (i : Fin 8) :
    (outputRegion p).Contains ((p+BitVec.ofNat 64 (128*u))+BitVec.ofNat 64 (16*i.val)) 16 := by
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  exact Offset.contains_base p (by omega) (by omega)

end VG.Proof.MlDsa.AArch64.Optimized
