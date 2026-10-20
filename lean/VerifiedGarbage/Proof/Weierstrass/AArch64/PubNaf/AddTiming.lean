module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Add
import VerifiedGarbage.Proof.Weierstrass.JacMul

/-!
# Timing of the additions and doublings whose products may be calls

Two runs from the same field values (`FieldPair`) leak the same trace and
end with the same values: `ofNB_relCT` (a numbered program), `jacAddB_relCT`
(the complete Jacobian addition, `jacAdd_relCT` for products that may be
calls), and `relCT_of_ct`, a piece of code constant time for some public
registers, from what each run satisfies.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

/-- A piece of code, constant time for the registers `G`, from two runs that
agree on them, and what each run satisfies. -/
theorem relCT_of_ct {P Q : State → State → Prop} {c : Prog isa} {G : List Reg}
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs G)) c)
    (hpub : ∀ s t, P s t → AArch64.Taint.Agree (Taint.ofRegs G) s t)
    (hw : ∀ s t, P s t → ∃ F₁ F₂ : State → Prop, WP isa c s F₁ ∧ WP isa c t F₂ ∧
      ∀ s' t', F₁ s' → F₂ t' → Q s' t') :
    RelCT isa P c Q := by
  intro s t ts tt s' t' hp es et
  obtain ⟨F₁, F₂, w₁, w₂, hq⟩ := hw s t hp
  obtain ⟨_, _, xs, fs⟩ := w₁
  obtain ⟨_, _, xt, ft⟩ := w₂
  obtain ⟨_, rfl⟩ := Exec.det es xs
  obtain ⟨_, rfl⟩ := Exec.det et xt
  exact ⟨hct _ _ _ _ _ _ trivial trivial (hpub s t hp) es et, hq _ _ fs ft⟩

/-- `ofN_relCT`, for products that may be calls. -/
theorem ofNB_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2^(64*M.n))) {N : List FOp} (hN : NumOk N)
    {S : RcbSlots} {p q o : Pt} (hA : RcbApart S p q o)
    (hSl : ∀ x∈rcbW S o ++ rcbR S p q, Sl x) (hLow : Low M (rcbW S o ++ rcbR S p q))
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈rcbR S p q, x∈V)
    (hct : FieldCT (fprogB M (ofN N S p q o))) :
    RelCT isa (FieldPair M base size m Sl V E) (fprogB M (ofN N S p q o))
      (FieldPair M base size m Sl ([o.x,o.y,o.z]++V) (runOps (ofN N S p q o) E)) := by
  apply fieldWP_relCT hct
  intro s hi
  exact WP.mono (ofN_ok hL hAl hm hN hA hSl hLow hi hV) fun _ ⟨hk,it,_⟩ => ⟨it,hk.sp⟩

/-- `jacAdd_relCT`, for products that may be calls and a modulus of other
than four words. -/
theorem jacAddB_relCT {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl) (hn4 : K.M.n ≠ 4)
    (hm : UnitMod m (2^(64*K.M.n))) {p q o : Pt} (hA : RcbApart K.S p q o)
    (hSl : ∀ x∈rcbW K.S o ++ rcbR K.S p q, Sl x) (hLow : Low K.M (rcbW K.S o ++ rcbR K.S p q))
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈rcbR K.S p q, x∈V)
    (hOne : K.one<m) (hc : JacAddChecks K p q o) :
    RelCT isa (FieldPair K.M base size m Sl V E) (Jacobian.jacAdd K p q o)
      (fun s t => ∃ E', FieldPair K.M base size m Sl ([o.x,o.y,o.z]++V) E' s t) := by
  have os : ∀ x∈[o.x,o.y,o.z], Sl x := by
    intro x hx; apply hSl x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbW]
  have pv : ∀ x∈[p.x,p.y,p.z], x∈V := by
    intro x hx; apply hV x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbR]
  have qv : ∀ x∈[q.x,q.y,q.z], x∈V := by
    intro x hx; apply hV x
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [rcbR]
  rw [Jacobian.jacAdd]
  apply fieldBranch_relCT hL hAl hm (pv _ (by simp)) (hc.zero _ (by simp))
  · intro _
    exact (copyPoint_relCT hL hAl os qv hc.copyQ).mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
  · intro _
    apply fieldBranch_relCT hL hAl hm (qv _ (by simp)) (hc.zero _ (by simp))
    · intro _
      exact (copyPoint_relCT hL hAl os pv hc.copyP).mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)
    · intro _
      have hh : RelCT isa (FieldPair K.M base size m Sl V E) (fprogB K.M (jacHead K.S p q))
          (FieldPair K.M base size m Sl (validAfter (jacHead K.S p q) V) (runOps (jacHead K.S p q) E)) := by
        apply fieldWP_relCT hc.head
        intro s hi
        exact WP.mono (jacHeadB_ok hL hAl hm hA hSl hLow hi hV) fun _ ⟨hk,it,_,_⟩ => ⟨it,hk.sp⟩
      apply RelCT.seq hh
      have oldV : ∀ x∈V, x∈validAfter (jacHead K.S p q) V :=
        fun x hx => (mem_validAfter _ _).mpr (Or.inl hx)
      have subV : ∀ x∈[o.x,o.y,o.z]++V, x∈[o.x,o.y,o.z]++validAfter (jacHead K.S p q) V := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_append_left _ hx
        · exact List.mem_append_right _ (oldV x hx)
      apply fieldBranch_relCT hL hAl hm (a:=K.S.t3) (by
        rw [mem_validAfter]; right; simp [jacHead,FOp.out]) (hc.zero _ (by simp))
      · intro _
        apply fieldBranch_relCT hL hAl hm (a:=K.S.t5) (by
          rw [mem_validAfter]; right; simp [jacHead,FOp.out]) (hc.zero _ (by simp))
        · intro _
          have hdA : RcbApart K.S p p o := ⟨hA.nodup,fun x hx => hA.apart x (rcbR_self_mem _ _ _ hx)⟩
          have hsub : ∀ x ∈ rcbW K.S o ++ rcbR K.S p p, x ∈ rcbW K.S o ++ rcbR K.S p q := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact List.mem_append_left _ hx
            · exact List.mem_append_right _ (rcbR_self_mem _ _ _ hx)
          have hv : ∀ x∈rcbR K.S p p, x∈validAfter (jacHead K.S p q) V :=
            fun x hx => oldV x (hV x (rcbR_self_mem _ _ _ hx))
          have e : dblJMul K.S p o = ofN (dblJChoiceN true) K.S p p o := dblJChoice_eq true K.S p o
          have hdc := hc.double
          rw [verifyDouble_eq hn4, e] at hdc
          rw [verifyDouble_eq hn4, e]
          have hd := ofNB_relCT (base := base) (E := runOps (jacHead K.S p q) E) hL hAl hm
            (dblJChoiceN_ok true) hdA (fun x hx => hSl x (hsub x hx)) (hLow.mono hsub) hv hdc
          exact hd.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
        · intro _
          exact (infinity_relCT hL hAl os hOne hc.infinity).mono
            (fun _ _ h => h) (fun _ _ h => ⟨_,h.sub subV⟩)
      · intro _
        have ht : RelCT isa
            (FieldPair K.M base size m Sl (validAfter (jacHead K.S p q) V) (runOps (jacHead K.S p q) E))
            (fprogB K.M (jacTail K.S p q o))
            (FieldPair K.M base size m Sl ([o.x,o.y,o.z]++V)
              (runOps (jacHead K.S p q ++ jacTail K.S p q o) E)) := by
          apply fieldWP_relCT hc.tail
          intro s hi
          exact WP.mono (jacTailB_ok hL hAl hm hA hSl hLow hi hV) fun _ ⟨hk,it,_⟩ => ⟨it,hk.sp⟩
        exact ht.mono (fun _ _ h => h) (fun _ _ h => ⟨_,h⟩)

end VG.Proof.Weierstrass.AArch64
