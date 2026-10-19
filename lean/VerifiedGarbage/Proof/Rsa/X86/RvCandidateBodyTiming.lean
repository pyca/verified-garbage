module

public import VerifiedGarbage.Proof.Rsa.X86.RvCandidateSquareTiming

/-! # One candidate has a value-independent trace -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

abbrev CandidateData.y {g : Geo} {m eLen dLen : Nat} (C : CandidateData g m eLen dLen) : Nat :=
  Spec.Rsa.powMod (C.V sCand + 2) (C.AW wR) m

theorem CandidateData.exp_toSquare {g : Geo} {m eLen dLen : Nat}
    (C : CandidateData g m eLen dLen) {s : State} (h : C.Exp (8 * (dLen + eLen)) s) :
    C.SquareStart C.y s := by
  change KS _ _ _ _ _ _ _ _ _ at h ⊢
  refine h.mono ?_ ?_ ?_
  · intro j hj
    refine ⟨?_, ?_⟩
    · simp only [liveSq, liveM, liveExp, List.mem_cons, List.not_mem_nil, or_false] at *
      grind
    · simp only [liveSq, liveM, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [AE, upd, mY, mG, aNg, aO, mR2, mBase, aOne, aZ, aN,
          Nat.mod_eq_of_lt C.rb, VG.Proof.Bignum.powMod_eq]
  · intro j hj
    simp only [List.mem_singleton] at hj
    subst j
    exact ⟨by simp, upd_ne _ _ (by decide)⟩
  · intro d hd
    exact ⟨hd, by simp only [Nat.sub_self]⟩

theorem candBody_relCT {g : Geo} {m eLen dLen : Nat} (C D : CandidateData g m eLen dLen)
    (sp : C.s0.gpr .esp = D.s0.gpr .esp) :
    RelCT isa (fun s t => C.Start s ∧ D.Start t) (candBody g.n) (fun _ _ => True) := by
  intro s t tr ur sf tf hs es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 er =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 fr =>
      obtain ⟨eq1, cs, ds⟩ := candExp_relCT C D sp _ _ _ _ _ _ hs e1 f1
      cases er with
      | @seq _ _ _ x _ _ _ e2 e3 =>
        cases fr with
        | @seq _ _ _ y _ _ _ f2 f3 =>
          obtain ⟨eq2, cx, dx⟩ := candSquare_relCT C D sp C.y D.y
            (by rw [CandidateData.y, VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ (by have := C.large; omega))
            (by rw [CandidateData.y, VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ (by have := D.large; omega))
            _ _ _ _ _ _ ⟨C.exp_toSquare cs, D.exp_toSquare ds⟩ e2 f2
          have eq3 := (candNext_workspace.trace _ _ _ _ _ _ (ks_agree cx dx) e3 f3).1
          exact ⟨by rw [eq1, eq2, eq3], trivial⟩

end VG.Proof.Rsa.X86.Recover
