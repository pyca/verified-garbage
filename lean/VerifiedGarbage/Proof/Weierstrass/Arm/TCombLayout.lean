module

public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
public import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP

/-! Workspace geometry shared by the comb setup and its addition loop. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Proof.Weierstrass.Arm.Point

/-- The accumulator and negation temporary lie below the point-call workspace. -/
structure Layout (K : TCombCfg) : Prop where
  n3 : 3≤K.L.M.n
  n6 : K.L.M.n≤6
  point : LadPt K.L
  low : ∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z,K.zero,K.neg],
    x+8*K.L.M.n≤Impl.Weierstrass.Point.oAt K.L.M.n
  apart : (K.L.R.x+8*K.L.M.n≤K.L.R.y ∨ K.L.R.y+8*K.L.M.n≤K.L.R.x) ∧
    (K.L.R.x+8*K.L.M.n≤K.L.R.z ∨ K.L.R.z+8*K.L.M.n≤K.L.R.x) ∧
    (K.L.R.y+8*K.L.M.n≤K.L.R.z ∨ K.L.R.z+8*K.L.M.n≤K.L.R.y)
  negApart : ∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z,K.zero],
    K.neg+8*K.L.M.n≤x ∨ x+8*K.L.M.n≤K.neg
  zeroApart : ∀ x ∈ [K.L.R.x,K.L.R.y,K.L.R.z],
    K.zero+8*K.L.M.n≤x ∨ x+8*K.L.M.n≤K.zero

/-- All writes, including point-call and field-call temporaries. -/
def writes (K : TCombCfg) : List (Nat × Nat) :=
  [(K.L.R.x,8*K.L.M.n),(K.L.R.y,8*K.L.M.n),(K.L.R.z,8*K.L.M.n),
   (K.neg,8*K.L.M.n),(Impl.Weierstrass.Point.oAt K.L.M.n,
     4096-Impl.Weierstrass.Point.oAt K.L.M.n)]

/-- Iterations preserve the curve parameters between `Q` and the call workspace. -/
def loopWrites (K : TCombCfg) : List (Nat × Nat) :=
  [(K.L.R.x,8*K.L.M.n),(K.L.R.y,8*K.L.M.n),(K.L.R.z,8*K.L.M.n),
   (K.neg,8*K.L.M.n),(Impl.Weierstrass.Point.oAt K.L.M.n,72*K.L.M.n),
   (Impl.Weierstrass.Point.ownAt K.L.M.n,4096-Impl.Weierstrass.Point.ownAt K.L.M.n)]

theorem Layout.loop_cover {K : TCombCfg} (h : Layout K) :
    ∀ r ∈ loopWrites K, ∃ t ∈ writes K,t.1≤r.1 ∧ r.1+r.2≤t.1+t.2 := by
  intro r hr
  simp only [loopWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨_,List.mem_cons_self ..,Nat.le_refl _,Nat.le_refl _⟩
  · exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_self ..),Nat.le_refl _,Nat.le_refl _⟩
  · exact ⟨_,by simp [writes],Nat.le_refl _,Nat.le_refl _⟩
  · exact ⟨_,by simp [writes],Nat.le_refl _,Nat.le_refl _⟩
  all_goals exact ⟨(Impl.Weierstrass.Point.oAt K.L.M.n,4096-Impl.Weierstrass.Point.oAt K.L.M.n),
    by simp [writes],lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)⟩

theorem Layout.q_cover {K : TCombCfg} (h : Layout K) :
    ∀ r ∈ [(K.Q.x,24*K.L.M.n)], ∃ t ∈ loopWrites K,t.1≤r.1 ∧ r.1+r.2≤t.1+t.2 := by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨(Impl.Weierstrass.Point.oAt K.L.M.n,72*K.L.M.n),by simp [loopWrites],?_⟩
  simp only [VG.Impl.Weierstrass.Arm.TCombCfg.Q,VG.Impl.Weierstrass.Arm.Point.ptAt]
  exact lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)

theorem Layout.sub_cover {K : TCombCfg} (h : Layout K) :
    ∀ r ∈ [(K.neg,8*K.L.M.n),(VG.Impl.Weierstrass.Arm.Mont.own K.L.M.n,64*K.L.M.n)],
      ∃ t ∈ loopWrites K,t.1≤r.1 ∧ r.1+r.2≤t.1+t.2 := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact ⟨(K.neg,8*K.L.M.n),by simp [loopWrites],Nat.le_refl _,Nat.le_refl _⟩
  · exact ⟨(Impl.Weierstrass.Point.ownAt K.L.M.n,4096-Impl.Weierstrass.Point.ownAt K.L.M.n),
      by simp [loopWrites],lay_cases K.L.M.n h.n3 h.n6 (by decide) (by decide) (by decide) (by decide)⟩

theorem Layout.bounded {K : TCombCfg} (h : Layout K) :
    ∀ r ∈ writes K, 0≤r.1 ∧ r.1+r.2≤4096 := by
  have hl := lay_nums h.n3 h.n6
  have low := h.low
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at low
  simp only [writes,List.mem_cons,List.not_mem_nil,or_false]
  intro r hr
  rcases hr with rfl|rfl|rfl|rfl|rfl <;> simp only [Nat.zero_le, true_and] <;> omega

end VG.Proof.Weierstrass.Arm.TComb
