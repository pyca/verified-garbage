module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Resume
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Result

/-! # Successful initial rejection bypasses both continuation blocks -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem full_coeffs {m : Mem} {p : Addr} {L : List Zq}
    (h : Rej8.Scalar.Coeffs m p L) (hl : L.length=256) :
    CoeffsUpTo m p L.length (Sample.cv L) (fun _=>0) := by
  intro i hi
  have hh : i<L.length := by omega
  rw [ite_eq_left hh]
  exact h i hh

theorem fast_finish {A B : Spec.Sha3.State} {p a b c : Addr} {s : State}
    (h : Progress A B 3 p a b c s)
    (hf : (accepted A 3).length=256 ∧ (accepted B 3).length=256)
    (hs : s.gpr .x24=0 ∨ s.gpr .x24=1) : ResumePost A B p a b s s := by
  have ea := accepted_full hf.1 (by decide : 3≤5)
  have eb := accepted_full hf.2 (by decide : 3≤5)
  have ca := full_coeffs h.left hf.1
  have cb := full_coeffs h.right hf.2
  refine ⟨Keep.refl _ _,Frame.refl _ _,?_,?_,?_,?_,?_⟩
  · rw [ea]; exact ca
  · exact Sample.reduced_of_coeffs (w16 := false) ca
  · rw [eb]; exact cb
  · exact Sample.reduced_of_coeffs (w16 := false) cb
  · rw [ea,eb,ite_eq_left hf]
    rcases hs with hs|hs <;> rw [hs] <;> rfl

theorem finish_branch {A B : Spec.Sha3.State} {p a b c : Addr} {s : State}
    (step : ∀{t : State}{n : Nat}, n=3 ∨ n=4 → Progress A B n p a b c t →
      t.syms "VG_MLKEM_REJ_SHUFFLE"=c → WP isa Impl.MlKem.AArch64.Paired.extraStep t (Advanced A B (n+1) p a b c t))
    (h : Progress A B 3 p a b c s) (sy : s.syms "VG_MLKEM_REJ_SHUFFLE"=c)
    (hf : (s.gpr .x6).toNat=if (accepted A 3).length=256 ∧ (accepted B 3).length=256 then 1 else 0)
    (hs : s.gpr .x24=0 ∨ s.gpr .x24=1) :
    WP isa (.ite (.zero .x .x6) Impl.MlKem.AArch64.Paired.extraPair (.block [])) s
      (ResumePost A B p a b s) := by
  refine WP.ite (s.gpr .x6 == 0) (eval_zero _ _) (fun _=>resume_ok step h sy) (fun hz=>?_)
  have full : (accepted A 3).length=256 ∧ (accepted B 3).length=256 := by
    by_contra hh
    have he : s.gpr .x6=0 := BitVec.eq_of_toNat_eq (by rw [hf,ite_eq_right hh]; rfl)
    rw [he] at hz
    contradiction
  exact wp_nil (fast_finish h full hs)

end VG.Proof.MlKem.AArch64.Paired
