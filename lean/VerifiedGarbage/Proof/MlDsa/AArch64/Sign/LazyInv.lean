import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inv
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation

/-! Working-space invariants for lazy forward transforms and centered products.
Canonical `Pl` and `Fam` remain unchanged for packed and public values. -/
namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr)
open VG.Proof.MlDsa.AArch64.Optimized

abbrev PosPl (s : State) (j : Nat) (f : Poly) : Prop := PosPolyIs s.mem (pa s (pS j)) f

def PosFam (s : State) (b m : Nat) (f : Nat → Poly) : Prop :=
  ∀ j<m, PosPl s (b+j) (f j)

abbrev SignedPl (s : State) (j : Nat) (f : Poly) (lo hi : Int) : Prop :=
  SignedPolyIs s.mem (pa s (pS j)) f lo hi

/-- Calls writing other slots preserve both lazy bounds and field values. -/
theorem keepPosPoly {S : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State}
    (L : Lay S rbs wbs s) {ws : List (Ptr × Nat)} {p : Ptr} {f : Poly}
    (hP : PPostB S s s' ws) (hc : keepB rbs wbs ws p 1024=true)
    (h : PosPolyIs s.mem (pa s p) f) : PosPolyIs s'.mem (pa s' p) f := by
  constructor
  · intro i hi
    rw [hP.pa (L.keepBs hc),VG.Proof.MlDsa.Arith.coeffAt_frame hP.frame (L.fdisj hc) hi]
    exact h.bound i hi
  · exact (L.keepPolyAt hP hc).trans h.value

theorem keepSignedPoly {S : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State}
    (L : Lay S rbs wbs s) {ws : List (Ptr × Nat)} {p : Ptr} {f : Poly} {lo hi : Int}
    (hP : PPostB S s s' ws) (hc : keepB rbs wbs ws p 1024=true)
    (h : SignedPolyIs s.mem (pa s p) f lo hi) : SignedPolyIs s'.mem (pa s' p) f lo hi := by
  apply h.congr
  intro i hi
  rw [hP.pa (L.keepBs hc)]
  exact VG.Proof.MlDsa.Arith.coeffAt_frame hP.frame (L.fdisj hc) hi

theorem PosFam.keep {S : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State}
    (L : Lay S rbs wbs s) {ws : List (Ptr × Nat)} {b m : Nat} {f : Nat → Poly}
    (hP : PPostB S s s' ws) (hc : famChk rbs wbs ws b m=true)
    (h : PosFam s b m f) : PosFam s' b m f :=
  fun j hj => keepPosPoly L hP (famChk_one hc hj) (h j hj)

theorem PosFam.of_canonical {s : State} {b m : Nat} {f : Nat → Poly}
    (h : Fam s b m f) : PosFam s b m f :=
  fun j hj => PosPolyIs.of_canonical (h j hj)

theorem PosPl.keep {S : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State}
    (L : Lay S rbs wbs s) {ws : List (Ptr × Nat)} {j : Nat} {f : Poly}
    (hP : PPostB S s s' ws) (hc : keepB rbs wbs ws (pS j) 1024=true)
    (h : PosPl s j f) : PosPl s' j f := keepPosPoly L hP hc h

theorem PosFam.congr {s : State} {b m : Nat} {f g : Nat → Poly}
    (h : PosFam s b m f) (he : ∀ j<m, f j=g j) : PosFam s b m g :=
  fun j hj => he j hj ▸ h j hj

theorem PosFam.split {s : State} {b m r : Nat} {f : Nat → Poly} (hr : r≤m) :
    PosFam s b m f ↔ PosFam s b r f ∧ PosFam s (b+r) (m-r) (fun j => f (r+j)) := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega),fun j hj => by
      rw [Nat.add_assoc]; exact h (r+j) (by omega)⟩
  · rintro ⟨h1,h2⟩ j hj
    by_cases he : j<r
    · exact h1 j he
    · have h := h2 (j-r) (by omega)
      simpa only [show b+r+(j-r)=b+j by omega,show r+(j-r)=j by omega] using h

/-- The already computed positive transforms extend by one slot. -/
theorem PosFam.snoc {s : State} {b m : Nat} {f : Nat → Poly}
    (h : PosFam s b m f) (ht : PosPl s (b+m) (f m)) : PosFam s b (m+1) f := by
  intro j hj
  rcases (by omega : j<m ∨ j=m) with hj | rfl
  · exact h j hj
  · exact ht

end VG.Proof.MlDsa.AArch64.Sign
