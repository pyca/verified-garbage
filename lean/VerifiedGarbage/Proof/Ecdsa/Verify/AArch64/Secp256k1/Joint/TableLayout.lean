module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint.Inputs
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint.Moves

/-! The fifteen projective table entries fit beside the existing arithmetic workspace. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Ecdsa.Verify.AArch64.Secp256k1.Joint

abbrev resultWork : List (Nat × Nat) := (coordinates resultPt).map (·,32)

theorem resultWork_sub : ∀ w ∈ resultWork,w ∈ loopWork := by decide

theorem table_coord_bounds {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) :
    ∀ x ∈ coordinates (tablePt d),tableAt ≤ x ∧ x+32 ≤ 6720 ∧ x % 8 = 0 := by
  intro x hx
  change 5280 ≤ x ∧ x+32 ≤ 6720 ∧ x % 8 = 0
  simp only [coordinates,tablePt,tableAt,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact ⟨by omega,by omega,by omega⟩

theorem tableWork_cover {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) :
    ∀ w ∈ (coordinates (tablePt d)).map (·,32),
      ∃ w' ∈ arithmeticWork,w'.1 ≤ w.1 ∧ w.1+w.2 ≤ w'.1+w'.2 := by
  intro w hw
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hw
  have h := table_coord_bounds h1 h15 x hx
  exact ⟨(tableAt,1440),List.mem_append_right _ (by simp),h.1,h.2.1⟩

theorem Changes.table {base : Addr} {s t : State} (h : Changes base loopWork s t)
    (hs : Scr s base 8192) {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15)
    {P : VG.Spec.Weierstrass.Point C} (hp : PointAt base s (tablePt d) P) :
    PointAt base t (tablePt d) P := by
  refine h.point hs hp (fun x hx => Nat.le_trans (table_coord_bounds h1 h15 x hx).2.1 (by decide)) ?_
  intro x hx w hw
  have hb := (table_coord_bounds h1 h15 x hx).1
  have hh : ∀ w ∈ loopWork,w.1+w.2 ≤ tableAt := by decide
  exact Or.inr (Nat.le_trans (hh w hw) hb)

theorem earlier_table_apart {j d : Nat} (hj : 1 ≤ j) (hjd : j < d) :
    ∀ x ∈ coordinates (tablePt j),∀ w ∈ (coordinates (tablePt d)).map (·,32),
      x+32 ≤ w.1 ∨ w.1+w.2 ≤ x := by
  intro x hx w hw
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hw
  simp only [coordinates,tablePt,tableAt,List.mem_cons,List.not_mem_nil,or_false] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> exact Or.inl (by omega)
end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1.Joint
