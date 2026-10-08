import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Data
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Domain
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Tree

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64

theorem Tree.lookup_insert {α : Type} (t : Tree α) (key query : Nat) (value : α) :
    (t.insert key value).lookup query = if query = key then some value else t.lookup query := by
  induction t with
  | empty => simp [insert, lookup, cond_eq_ite]
  | node k v left right ihl ihr =>
    by_cases hk : key = k <;> by_cases hq : query = k <;>
      by_cases he : query = key <;> by_cases hkl : key < k <;>
      by_cases hql : query < k <;>
      simp only [insert, lookup, cond_eq_ite, Nat.beq_eq, Nat.blt_eq, hk, hq, he, hkl, hql, ite_true, ite_false]
    all_goals first
      | simpa only [he, ite_true, ite_false] using ihl
      | simpa only [he, ite_true, ite_false] using ihr
      | exact (ite_eq_right (Ne.symm hk)).symm

namespace FastEnv
variable {α : Type}

theorem toEnv_ofEnv (e : Env α) : (ofEnv e).toEnv = e := by cases e; rfl

theorem toEnv_setReg (e : FastEnv α) (d : Reg) (v : α) :
    (e.setReg d v).toEnv = e.toEnv.setReg d v := by
  have inj (r : Reg) : r.ctorIdx = d.ctorIdx ↔ r = d := ⟨fun h => by
    rw [← Reg.ofNat_ctorIdx r, h, Reg.ofNat_ctorIdx], fun h => congrArg Reg.ctorIdx h⟩
  unfold setReg toEnv Env.setReg
  congr 1
  funext r
  rw [Tree.lookup_insert]
  by_cases h : r = d <;> simp [h, inj]

theorem toEnv_setSlot (e : FastEnv α) (off : Nat) (v : α) :
    (e.setSlot off v).toEnv = e.toEnv.setSlot off v := by
  unfold setSlot toEnv Env.setSlot
  congr 1
  funext j
  rw [Tree.lookup_insert]
  by_cases h : j = off <;> simp [h]

theorem toEnv_withCarry (e : FastEnv α) (c : Option α) :
    (e.withCarry c).toEnv = { e.toEnv with carry := c } := rfl

theorem decodedStep_eq (D : Dom α) (size : Nat) (e : FastEnv α) (i : Decoded) :
    (decodedStep D size e i).map toEnv = Forward.decodedStep D size e.toEnv i := by
  have hc : e.toEnv.carry = e.carry := rfl
  cases i <;> simp only [decodedStep, Forward.decodedStep]
  all_goals split <;>
    simp_all [bind, pure, Option.map_bind, Function.comp_def,
      toEnv_setReg, toEnv_setSlot, toEnv_withCarry]

theorem step_eq (D : Dom α) (size : Nat) (e : FastEnv α) (i : Instr) :
    (step D size e i).map toEnv = Forward.step D size e.toEnv i := by
  simp only [step, Forward.step, bind, Option.map_bind, Function.comp_def, decodedStep_eq]

theorem eval_eq (D : Dom α) (size : Nat) (is : List Instr) (e : FastEnv α) :
    (eval D size is e).map toEnv = Forward.eval D size is e.toEnv := by
  induction is generalizing e with
  | nil => rfl
  | cons i is ih =>
    simp only [eval, Option.map_bind, Function.comp_def, ih, Forward.eval]
    rw [← step_eq]
    simp only [Option.bind_map, Function.comp_def]

/-- Evaluation leaves the common initial functions fixed. -/
theorem decodedStep_initial {D : Dom α} {size : Nat} {e e' : FastEnv α} {i : Decoded}
    (h : decodedStep D size e i = some e') : e'.initial = e.initial := by
  cases i with
  | scalar op d a b c =>
    simp only [decodedStep] at h
    split at h
    · contradiction
    · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨va, _, vb, _, vc, _, vd, _, cf, _, vr, _, rfl⟩ := h
      rfl
  | load d j =>
    simp only [decodedStep] at h
    split at h
    · contradiction
    · cases h; rfl
  | store r j =>
    simp only [decodedStep] at h
    split at h
    · contradiction
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨v, _, rfl⟩ := h
      rfl

theorem step_initial {D : Dom α} {size : Nat} {e e' : FastEnv α} {i : Instr}
    (h : step D size e i = some e') : e'.initial = e.initial := by
  simp only [step, bind, Option.bind_eq_some_iff] at h
  obtain ⟨view, _, hv⟩ := h
  exact decodedStep_initial hv

theorem eval_initial {D : Dom α} {size : Nat} {is : List Instr} {e e' : FastEnv α}
    (h : eval D size is e = some e') : e'.initial = e.initial := by
  induction is generalizing e with
  | nil => cases h; rfl
  | cons i is ih =>
    simp only [eval, Option.bind_eq_some_iff] at h
    obtain ⟨mid, hs, ht⟩ := h
    exact (ih ht).trans (step_initial hs)

end FastEnv

theorem evalFast_eq {α : Type} (D : Dom α) (size : Nat) (is : List Instr) (e : Env α) :
    evalFast D size is e = eval D size is e := by
  rw [evalFast, FastEnv.eval_eq, FastEnv.toEnv_ofEnv]

theorem eval_of_data {α : Type} {D : Dom α} {size : Nat} {is : List Instr} {e : Env α}
    {d : Tree α × Tree α × Option α} (h : evalData D size is e = some d) :
    eval D size is e = some (fromData e d) := by
  obtain ⟨fe, he, hd⟩ := Option.map_eq_some_iff.mp h
  subst d
  rw [← evalFast_eq, evalFast, he, Option.map_some]
  have hi := FastEnv.eval_initial he
  change fe.initial = e at hi
  cases fe
  cases hi
  rfl

end VG.Proof.Weierstrass.AArch64.Forward
