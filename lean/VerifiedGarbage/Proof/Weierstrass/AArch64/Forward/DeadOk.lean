import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk

/-! `deadStores` keeps every word a block leaves in memory: it drops a store
to a slot that a later store overwrites before any load reads it. Going
forward, the two runs agree on the registers, the carry and every slot but
those the rest of the block overwrites before reading (the `later` set
`deadStores` computes backwards). At the end that set is empty. -/

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.Forward

variable {size : Nat}

/-- `deadStores`'s state after the rest of the block, built backwards. -/
def deadR (is : List Instr) : List Nat × List Instr := is.foldr (fun i s => deadStep i s) ([],[])

theorem deadStores_eq_deadR (is : List Instr) : deadStores is=(deadR is).2 := by
  rw [deadStores_eq_dead,List.foldl_reverse]
  rfl

/-- Agreement but on the slots in `L`. -/
structure PAgree (L : List Nat) (e₁ e₂ : Env CVal) : Prop where
  reg : ∀ r,(e₁.reg r).map Prod.fst=(e₂.reg r).map Prod.fst
  slot : ∀ off,off∉L → (e₁.slot off).1=(e₂.slot off).1
  carry : e₁.carry.map Prod.snd=e₂.carry.map Prod.snd

theorem deadStep_scalar (op : Op) (d a b c : Reg) (s : List Nat × List Instr) :
    deadStep (op.instr d a b c) s=(s.1,op.instr d a b c :: s.2) := by
  cases op <;> rfl

theorem eval_cons {α : Type} {D : Dom α} {e e' : Env α} {i : Instr} (is : List Instr)
    (h : step D size e i=some e') : eval D size (i::is) e=eval D size is e' := by
  simp only [eval,h,Option.bind_some]

theorem dead_ok (is : List Instr) : ∀ {e₁ e₂ l : Env CVal},PAgree (deadR is).1 e₁ e₂ →
    eval concDom size is e₁=some l → ∃ r,eval concDom size (deadR is).2 e₂=some r ∧ PAgree [] l r := by
  induction is with
  | nil =>
    intro e₁ e₂ l h he
    cases he
    exact ⟨e₂,rfl,h⟩
  | cons i is ih =>
    intro e₁ e₂ l h he
    simp only [eval] at he
    cases h1 : step concDom size e₁ i with
    | none => rw [h1] at he; cases he
    | some e₁' =>
      rw [h1,Option.bind_some] at he
      obtain ⟨⟨v,hv⟩,hdec,hs⟩ := step_some h1
      change PAgree (deadStep i (deadR is)).1 e₁ e₂ at h
      change ∃ r,eval concDom size (deadStep i (deadR is)).2 e₂=some r ∧ _
      cases v with
      | load d off =>
        subst hv
        obtain ⟨hd0,ho1,ho2,ho3,rfl⟩ := load_some hs
        simp only [Decoded.instr,deadStep] at h ⊢
        rw [eval_cons _ (step_load hd0 ⟨ho1,ho2,ho3⟩)]
        refine ih (e₁ := e₁.setReg d (e₁.slot off)) ⟨fun r => ?_,fun o ho => ?_,h.carry⟩ he
        · simp only [Env.setReg]
          split
          · simpa using h.slot off (by simp)
          · exact h.reg r
        · by_cases hoe : o=off
          · subst hoe; exact h.slot o (by simp)
          · exact h.slot o (by simp [ho,hoe])
      | store r off =>
        subst hv
        obtain ⟨hoff,x,hx,rfl⟩ := store_some hs
        simp only [Decoded.instr,deadStep] at h ⊢
        split
        · rename_i hin
          refine ih (e₁ := e₁.setSlot off x) ⟨h.reg,fun o ho => ?_,h.carry⟩ he
          have hoe : o≠off := by rintro rfl; exact ho (by simpa using hin)
          simp only [Env.setSlot,hoe,ite_false]
          exact h.slot o (by simp [hoe,ho])
        · have hr := h.reg r
          rw [hx] at hr
          cases hy : e₂.reg r with
          | none => rw [hy] at hr; cases hr
          | some y =>
            rw [hy] at hr; simp only [Option.map_some,Option.some.injEq] at hr
            rw [eval_cons _ (step_store hoff hy)]
            refine ih (e₁ := e₁.setSlot off x) ⟨h.reg,fun o ho' => ?_,h.carry⟩ he
            simp only [Env.setSlot]
            split
            · exact hr
            · rename_i hoe
              exact h.slot o (by simp [hoe,ho'])
      | scalar op d' x y z =>
        subst hv
        simp only [Decoded.instr,deadStep_scalar] at h ⊢
        obtain ⟨u,rfl,hu⟩ := scalar_rename (e₁ := e₁) (e₂ := e₂) (op := op) (d' := d') (x := x) (y := y)
          (z := z) id (fun _ => h.reg d') (fun r _ => h.reg r) h.carry hs
        have hstep : step concDom size e₂ (op.instr d' x y z)=
            some {e₂.setReg d' u with carry:=if op.flags then some u else e₂.carry} := by
          exact (step_of_decode (v := .scalar op d' x y z) (congrArg (Option.map Subtype.val) hdec)).trans hu
        rw [eval_cons _ hstep]
        refine ih (e₁ := {e₁.setReg d' u with carry:=if op.flags then some u else e₁.carry})
          ⟨fun r => ?_,h.slot,?_⟩ he
        · simp only [Env.setReg]
          split
          · rfl
          · exact h.reg r
        · dsimp only
          split
          · rfl
          · exact h.carry

/-- `deadStores` from the same environment ends with the same words in every slot. -/
theorem deadStores_ok {is : List Instr} {e l : Env CVal} (he : eval concDom size is e=some l) :
    ∃ r,eval concDom size (deadStores is) e=some r ∧ ∀ off,(l.slot off).1=(r.slot off).1 := by
  rw [deadStores_eq_deadR]
  obtain ⟨r,hr,h⟩ := dead_ok is ⟨fun _ => rfl,fun _ _ => rfl,rfl⟩ he
  exact ⟨r,hr,fun off => h.slot off (by simp)⟩

end VG.Proof.Weierstrass.AArch64.Forward
