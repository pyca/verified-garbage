import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowInvariant

/-! Relational timing of the five consecutive Jacobian doublings. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont

/-- Doubling has an exact shared environment transition. -/
theorem jacDoubleField_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2^(64*M.n))) {S : RcbSlots} {p o : Pt} (hA : RcbApart S p p o)
    (hSl : ∀ x∈rcbW S o ++ rcbR S p p, Sl x)
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈rcbR S p p, x∈V)
    (hct : FieldCT (fprogB M (dblJMul S p o))) :
    RelCT isa (FieldPair M base size m Sl V E) (fprogB M (dblJMul S p o))
      (FieldPair M base size m Sl V (runOps (dblJMul S p o) E)) := by
  have he : dblJMul S p o = ofN (dblJChoiceN true) S p p o := dblJChoice_eq true S p o
  rw [he] at hct ⊢
  exact (ofN_relCT hL hAl hm (dblJChoiceN_ok true) hA hSl hV hct).mono
    (fun _ _ h => h) (fun _ _ h => h.sub (fun _ hx => List.mem_append_right _ hx))

structure JacDoubleChecks (K : WinCfg) : Prop where
  rd : FieldCT (fprogB K.M (dblJMul K.S K.R K.D))
  dr : FieldCT (fprogB K.M (dblJMul K.S K.D K.R))
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
  have rd := fun (E : Nat → Fin m) => jacDoubleField_relCT (base := base) (E := E) hL.lay hAl hm
    (old.rcbApart_D (Or.inl rfl)) (hs _ _ (Or.inl rfl) (Or.inr rfl)) (hv _ (Or.inl rfl)) hc.rd
  have dr := fun (E : Nat → Fin m) => jacDoubleField_relCT (base := base) (E := E) hL.lay hAl hm
    hL.rcbApart_DR (hs _ _ (Or.inr rfl) (Or.inl rfl)) (hv _ (Or.inr rfl)) hc.dr
  change RelCT isa _ (.seq (fprogB K.M (dblJMul K.S K.R K.D))
    (.seq (fprogB K.M (dblJMul K.S K.D K.R))
    (.seq (fprogB K.M (dblJMul K.S K.R K.D))
    (.seq (fprogB K.M (dblJMul K.S K.D K.R))
    (.seq (fprogB K.M (dblJMul K.S K.R K.D))
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
