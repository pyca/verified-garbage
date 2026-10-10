import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Production
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Timing
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowInvariant
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.Comb
import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian

/-! ## `JacWindowDoubleTiming` -/

section

/-! Relational timing of the five consecutive Jacobian doublings. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont

/-- Doubling has an exact shared environment transition. -/
theorem jacDoubleField_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl) (hnc : Mont.callOf M = none)
    (hm : UnitMod m (2^(64*M.n))) {S : RcbSlots} {p o : Pt} (hA : RcbApart S p p o)
    (hSl : ∀ x∈rcbW S o ++ rcbR S p p, Sl x)
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈rcbR S p p, x∈V)
    (hct : FieldCT (VG.Impl.P256.VerifyDouble.double M S p o)) :
    RelCT isa (FieldPair M base size m Sl V E) (VG.Impl.P256.VerifyDouble.double M S p o)
      (FieldPair M base size m Sl V (runOps (dblJMul S p o) E)) := by
  exact Forward.field_relCT Forward.Production.cases hL hAl hnc hm hA hSl hV hct

structure JacDoubleChecks (K : WinCfg) : Prop where
  rd : FieldCT (VG.Impl.P256.VerifyDouble.double K.M K.S K.R K.D)
  dr : FieldCT (VG.Impl.P256.VerifyDouble.double K.M K.S K.D K.R)
  copy : FieldCT (.block (copyPt K.M.n K.R K.D))

/-- Five public doubles preserve a common field environment. -/
theorem jacFive_relCT {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod m (2^(64*K.M.n))) (hc : JacDoubleChecks K)
    {E : Nat → Fin m} :
    RelCT isa (FieldPair K.M base size m (·∈jacWinSlots K) (jacLive K) E)
      (Jacobian.jacDoubles K 5)
      (fun s t => ∃ E', FieldPair K.M base size m (·∈jacWinSlots K) (jacLive K) E' s t) := by
  have old := hL.toWinLay hJ
  have hs (p o : Pt) (hp : p=K.R ∨ p=K.D) (ho : o=K.R ∨ o=K.D) :
      ∀ x∈rcbW K.S o ++ rcbR K.S p p, x∈jacWinSlots K := by
    intro x hx
    apply hL.old_slots x
    rcases hp with rfl | rfl <;> rcases ho with rfl | rfl <;>
      simp only [rcbW,rcbR,winSlots,winRo,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢ <;> grind
  have hv (p : Pt) (hp : p=K.R ∨ p=K.D) : ∀ x∈rcbR K.S p p, x∈jacLive K := by
    intro x hx
    rcases hp with rfl | rfl <;>
      simp only [rcbR,jacLive,winRo,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢ <;> grind
  have rd := fun (E : Nat → Fin m) => jacDoubleField_relCT (base := base) (E := E) hL.lay hAl (callOf_small (Nat.le_of_eq hL.n)) hm
    (old.rcbApart_D (Or.inl rfl)) (hs _ _ (Or.inl rfl) (Or.inr rfl)) (hv _ (Or.inl rfl)) hc.rd
  have dr := fun (E : Nat → Fin m) => jacDoubleField_relCT (base := base) (E := E) hL.lay hAl (callOf_small (Nat.le_of_eq hL.n)) hm
    hL.rcbApart_DR (hs _ _ (Or.inr rfl) (Or.inl rfl)) (hv _ (Or.inr rfl)) hc.dr
  change RelCT isa _ (.seq (VG.Impl.P256.VerifyDouble.double K.M K.S K.R K.D)
    (.seq (VG.Impl.P256.VerifyDouble.double K.M K.S K.D K.R)
    (.seq (VG.Impl.P256.VerifyDouble.double K.M K.S K.R K.D)
    (.seq (VG.Impl.P256.VerifyDouble.double K.M K.S K.D K.R)
    (.seq (VG.Impl.P256.VerifyDouble.double K.M K.S K.R K.D)
    (.seq (.block (copyPt 4 K.R K.D)) (.block []))))))) _
  apply RelCT.seq (rd E)
  apply RelCT.seq (dr _)
  apply RelCT.seq (rd _)
  apply RelCT.seq (dr _)
  apply RelCT.seq (rd _)
  rw [← hL.n]
  apply RelCT.seq (copyPoint_relCT hL.lay hAl (by
    intro x hx
    apply hL.old_slots x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [winSlots,winOther]) (by
    intro x hx
    simp only [jacLive,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind) hc.copy)
  intro s t ts tt s' t' hp es et
  have hs : s'=s ∧ ts=[] := by cases es with | block he => simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at he; exact ⟨he.1.symm,he.2.symm⟩
  have ht : t'=t ∧ tt=[] := by cases et with | block he => simp only [execBlock,Option.some.injEq,Prod.mk.injEq] at he; exact ⟨he.1.symm,he.2.symm⟩
  rcases hs with ⟨rfl,rfl⟩
  rcases ht with ⟨rfl,rfl⟩
  exact ⟨rfl,_,hp.sub (fun _ hx => List.mem_append_right _ hx)⟩

end VG.Proof.Weierstrass.AArch64

end

/-! ## `JacWindowFive` -/

section

/-! Five consecutive doublings with one Jacobian accumulator. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

/-- A double of a scalar multiple, retaining a fixed set of initialized slots. -/
theorem jacDoubleMultiple_ok {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl) (hnc : Mont.callOf M = none)
    (hm : UnitMod C.p (2^(64*M.n))) (hC : Law C) (ha : AM3 C)
    {S : RcbSlots} {p o : Pt} (hA : RcbApart S p p o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p p, Sl x)
    {V W : List Nat} (hW : ∀ x ∈ rcbW S o, x ∈ W)
    {E : Nat → Fe C} {s : State} (hI : Inv M base size C.p Sl V E s)
    (hV : ∀ x ∈ rcbR S p p, x ∈ V) {P : Point C} {e : Nat}
    (hP : onCurve C P = true) (hJ : InvJ C (E p.x) (E p.y) (E p.z) (mul e P)) :
    WP isa (VG.Impl.P256.VerifyDouble.double M S p o) s fun t =>
      ∃ E', ProgKeep M base W s t ∧ Inv M base size C.p Sl V E' t ∧
      InvJ C (E' o.x) (E' o.y) (E' o.z) (mul (2*e) P) := by
  refine WP.mono (Forward.double_ok Forward.Production.cases hL hAl hnc hm hC ha hA hSl hI hV (hC.onCurve_mul hP e) hJ)
    fun t ⟨hk,hi,hj⟩ => ⟨_,hk.mono hW,hi.sub (fun _ hx => List.mem_append_right _ hx),?_⟩
  rw [hC.add_mul_mul hP,show e+e=2*e by omega] at hj
  exact hj

/-- Five doublings, alternating work slots and copying only the final point. -/
theorem jacFive_ok {K : WinCfg} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hn : K.M.n=4)
    (hRD : RcbApart K.S K.R K.R K.D) (hDR : RcbApart K.S K.D K.D K.R)
    (hSl : ∀ x ∈ rcbW K.S K.D ++ rcbW K.S K.R ++ rcbR K.S K.R K.D, Sl x)
    {V : List Nat} (hV : ∀ x ∈ rcbR K.S K.R K.D, x ∈ V)
    {E : Nat → Fe C} {s : State} (hI : Inv K.M base size C.p Sl V E s)
    {P : Point C} {e : Nat} (hP : onCurve C P = true)
    (hJ : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) (mul e P)) :
    WP isa (Jacobian.jacDoubles K 5) s fun t =>
      ∃ E', ProgKeep K.M base (rcbW K.S K.D ++ rcbW K.S K.R) s t ∧
      Inv K.M base size C.p Sl V E' t ∧
      InvJ C (E' K.R.x) (E' K.R.y) (E' K.R.z) (mul (32*e) P) := by
  have hsr : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.R, Sl x := by
    intro x hx; apply hSl x
    simp only [rcbW,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have hsd : ∀ x ∈ rcbW K.S K.R ++ rcbR K.S K.D K.D, Sl x := by
    intro x hx; apply hSl x
    simp only [rcbW,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have hvr : ∀ x ∈ rcbR K.S K.R K.R, x ∈ V := by
    intro x hx; apply hV x
    simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have hvd : ∀ x ∈ rcbR K.S K.D K.D, x ∈ V := by
    intro x hx; apply hV x
    simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  change WP isa (.seq (VG.Impl.P256.VerifyDouble.double K.M K.S K.R K.D)
    (.seq (VG.Impl.P256.VerifyDouble.double K.M K.S K.D K.R)
    (.seq (VG.Impl.P256.VerifyDouble.double K.M K.S K.R K.D)
    (.seq (VG.Impl.P256.VerifyDouble.double K.M K.S K.D K.R)
    (.seq (VG.Impl.P256.VerifyDouble.double K.M K.S K.R K.D)
    (.seq (.block (copyPt 4 K.R K.D)) (.block []))))))) s _
  apply WP.seq
  refine WP.mono (jacDoubleMultiple_ok (W := rcbW K.S K.D ++ rcbW K.S K.R) hL hAl (callOf_small (Nat.le_of_eq hn)) hm hC ha hRD hsr
    (fun _ hx => List.mem_append_left _ hx) hI hvr hP hJ) fun s₁ ⟨e₁,k₁,i₁,j₁⟩ => ?_
  apply WP.seq
  refine WP.mono (jacDoubleMultiple_ok (W := rcbW K.S K.D ++ rcbW K.S K.R) hL hAl (callOf_small (Nat.le_of_eq hn)) hm hC ha hDR hsd
    (fun _ hx => List.mem_append_right _ hx) i₁ hvd hP j₁) fun s₂ ⟨e₂,k₂,i₂,j₂⟩ => ?_
  apply WP.seq
  refine WP.mono (jacDoubleMultiple_ok (W := rcbW K.S K.D ++ rcbW K.S K.R) hL hAl (callOf_small (Nat.le_of_eq hn)) hm hC ha hRD hsr
    (fun _ hx => List.mem_append_left _ hx) i₂ hvr hP j₂) fun s₃ ⟨e₃,k₃,i₃,j₃⟩ => ?_
  apply WP.seq
  refine WP.mono (jacDoubleMultiple_ok (W := rcbW K.S K.D ++ rcbW K.S K.R) hL hAl (callOf_small (Nat.le_of_eq hn)) hm hC ha hDR hsd
    (fun _ hx => List.mem_append_right _ hx) i₃ hvd hP j₃) fun s₄ ⟨e₄,k₄,i₄,j₄⟩ => ?_
  apply WP.seq
  refine WP.mono (jacDoubleMultiple_ok (W := rcbW K.S K.D ++ rcbW K.S K.R) hL hAl (callOf_small (Nat.le_of_eq hn)) hm hC ha hRD hsr
    (fun _ hx => List.mem_append_left _ hx) i₄ hvr hP j₄) fun s₅ ⟨e₅,k₅,i₅,j₅⟩ => ?_
  apply WP.seq
  rw [← hn]
  refine WP.mono (copyPoint_ok hL hAl hDR hsd i₅ hvd) fun t ⟨et,kt,it,hv⟩ => ?_
  apply WP.block_nil
  refine ⟨et,k₁.trans (k₂.trans (k₃.trans (k₄.trans (k₅.trans
    (kt.mono (fun _ hx => List.mem_append_right _ hx)))))),
    it.sub (fun _ hx => List.mem_append_right _ hx),?_⟩
  simp only [Prod.mk.injEq] at hv
  rw [hv.1,hv.2.1,hv.2.2]
  simpa only [show 2*(2*(2*(2*(2*e))))=32*e by omega] using j₅

end VG.Proof.Weierstrass.AArch64

end
