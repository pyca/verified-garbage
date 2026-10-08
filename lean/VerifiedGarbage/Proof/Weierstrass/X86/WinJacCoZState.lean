import VerifiedGarbage.Proof.Weierstrass.X86.WinJacCoZField
import VerifiedGarbage.Proof.Weierstrass.WinJacMath

/-! The shared-Z table invariant and its transfer to memory. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

/-- The affine base point in coordinates sharing the current table entry's Z. -/
structure SharedZ (K : JacWinCfg) (C : Curve) (base : Addr) (P : Point C) (s : State) : Prop where
  lt : ∀ x∈[K.D.x,K.D.y],wordsVal s.mem base x K.M.n<C.p
  point : InvJ C (tmv C K.M.n base s K.D.x) (tmv C K.M.n base s K.D.y)
    (tmv C K.M.n base s K.E.z) P

structure CoBuildInv (K : JacWinCfg) (C : Curve) (base : Addr) (size wk : Nat)
    (P : Point C) (s₀ : State) (m : Nat) (s : State) : Prop where
  inv : BuildInv K C base size wk P s₀ m s
  shared : SharedZ K C base P s

/-- Saving an entry changes neither the live entry nor its shared-Z base point. -/
theorem SharedZ.store {K : JacWinCfg} {C : Curve} {base : Addr} {size wk m : Nat}
    (hL : Layout K size wk) {s t : State} (hs : Scr s base size)
    (hu : Unch base (storeW K m) s.mem t.mem) {P : Point C} (h : SharedZ K C base P s) :
    SharedZ K C base P t := by
  have ex := store_slot hL hs (show K.D.x∈slots K by simp [slots,work]) hu
  have ey := store_slot hL hs (show K.D.y∈slots K by simp [slots,work]) hu
  have ez := store_slot hL hs (show K.E.z∈slots K by simp [slots,work]) hu
  refine ⟨?_,?_⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · rw [ex]; exact h.lt _ (by simp)
    · rw [ey]; exact h.lt _ (by simp)
  · simpa only [tmv,ex,ey,ez] using h.point

variable {C : Curve}

theorem zaddu_x (hC : Law C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn17 : 17 ≤ C.n) {m : Nat} (h2 : 2 ≤ m) (h15 : m ≤ 15) {X1 Y1 X2 Y2 Z : Fe C}
    (h1 : InvJ C X1 Y1 Z P) (hm : InvJ C X2 Y2 Z (mul m P)) (hz : Z ≠ 0) : X1 - X2 ≠ 0 := by
  intro hx
  obtain ⟨ne1, ne2⟩ := Window5.tbl_noexc hC hO hP hP0 hn17 h2 h15
  have hx' : X1 * (Z * Z) - X2 * (Z * Z) = 0 := by
    have e : X1 * (Z * Z) - X2 * (Z * Z) = (X1 - X2) * (Z * Z) := by grind
    rw [e, hx]; grind
  by_cases hy : Y1 * Z * (Z * Z) - Y2 * Z * (Z * Z) = 0
  · exact ne1 (hm.same hC h1 hz hz hx' hy)
  · exact ne2 (hm.opposite hC (hC.onCurve_mul hP m) hP h1 hz hz hx' hy)


theorem co_valid {K : JacWinCfg} {N : List FOp} {V : List Nat} {i : Nat}
    (hi : i∈N.map FOp.out) : coσ K i∈validAfter (N.map (FOp.rename (coσ K))) V := by
  rw [mem_validAfter]
  right
  obtain ⟨op,ho,rfl⟩ := List.mem_map.mp hi
  exact List.mem_map.mpr ⟨FOp.rename (coσ K) op,List.mem_map.mpr ⟨op,ho,rfl⟩,FOp.out_rename _ _⟩

theorem co_cached {K : JacWinCfg} {C : Curve} {base : Addr} {size : Nat} {Sl : Nat → Prop}
    (hn : K.M.n=4) {N : List FOp} {V : List Nat} {E r : Nat → Fe C} {t : State}
    (hi : Inv K.M base size C.p Sl (validAfter (N.map (FOp.rename (coσ K))) V) E t)
    (hv : ∀ i,E (coσ K i)=r i) (hout : ∀ i,12≤i → i≤16 → i∈N.map FOp.out)
    {Q : Point C} (hj : InvJ C (r 12) (r 13) (r 14) Q)
    (hz : r 14≠0) (h2 : r 15=r 14*r 14) (h3 : r 16=r 15*r 14) :
    Cached C base t (fun c => K.T+32*c) Q := by
  have e12 : E K.E.x=r 12 := hv 12
  have e13 : E K.E.y=r 13 := hv 13
  have e14 : E K.E.z=r 14 := hv 14
  have e15 : E K.z2=r 15 := hv 15
  have e16 : E K.z3=r 16 := hv 16
  apply Cached.of_inv hn hi
  · intro c hc
    have : c=0 ∨ c=1 ∨ c=2 ∨ c=3 ∨ c=4 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl
    · exact co_valid (hout 12 (by decide) (by decide))
    · exact co_valid (hout 13 (by decide) (by decide))
    · exact co_valid (hout 14 (by decide) (by decide))
    · exact co_valid (hout 15 (by decide) (by decide))
    · exact co_valid (hout 16 (by decide) (by decide))
  · rwa [e12,e13,e14]
  · rwa [e14]
  · rwa [e15,e14]
  · rwa [e16,e15,e14]

end VG.Proof.Weierstrass.X86.JWin
