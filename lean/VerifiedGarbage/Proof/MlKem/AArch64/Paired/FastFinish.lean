module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Resume
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Semantics

/-! # Successful initial rejection bypasses both continuation blocks -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

theorem full_coeffs {w16 : Bool} {m : Mem} {p : Addr} {L : List Zq}
    (h : Rej8.Scalar.CoeffsW w16 m p L) (hl : L.length=256) :
    CoeffsUpToW w16 m p L.length (Sample.cvW w16 L) (fun _=>0) := by
  intro i hi
  have hh : i<L.length := by omega
  rw [ite_eq_left hh]
  exact h i hh

theorem fast_finish {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s : State}
    (h : ProgressW w16 A B 3 p a b c s)
    (hf : (accepted A 3).length=256 ∧ (accepted B 3).length=256)
    (hs : s.gpr .x24=0 ∨ s.gpr .x24=1) : ResumePostW w16 A B p a b s s := by
  have ea := accepted_full hf.1 (by decide : 3≤5)
  have eb := accepted_full hf.2 (by decide : 3≤5)
  have ca := full_coeffs h.left hf.1
  have cb := full_coeffs h.right hf.2
  refine ⟨Keep.refl _ _,Frame.refl _ _,?_,?_,?_,?_,?_⟩
  · rw [ea]; exact ca
  · exact Sample.reduced_of_coeffs ca
  · rw [eb]; exact cb
  · exact Sample.reduced_of_coeffs cb
  · rw [ea,eb,ite_eq_left hf]
    rcases hs with hs|hs <;> rw [hs] <;> rfl

theorem finish_branch {w16 : Bool} {A B : Spec.Sha3.State} {p a b c : Addr} {s : State}
    (step : ∀{t : State}{n : Nat}, n=3 ∨ n=4 → ProgressW w16 A B n p a b c t →
      t.syms "VG_MLKEM_REJ_SHUFFLE"=c → WP isa (Impl.MlKem.AArch64.Paired.extraStep w16) t (AdvancedW w16 A B (n+1) p a b c t))
    (h : ProgressW w16 A B 3 p a b c s) (sy : s.syms "VG_MLKEM_REJ_SHUFFLE"=c)
    (hf : (s.gpr .x6).toNat=if (accepted A 3).length=256 ∧ (accepted B 3).length=256 then 1 else 0)
    (hs : s.gpr .x24=0 ∨ s.gpr .x24=1) :
    WP isa (.ite (.zero .x .x6) (Impl.MlKem.AArch64.Paired.extraPair w16) (.block [])) s
      (ResumePostW w16 A B p a b s) := by
  refine WP.ite (s.gpr .x6 == 0) (eval_zero _ _) (fun _=>resume_ok step h sy) (fun hz=>?_)
  have full : (accepted A 3).length=256 ∧ (accepted B 3).length=256 := by
    by_contra hh
    have he : s.gpr .x6=0 := BitVec.eq_of_toNat_eq (by rw [hf,ite_eq_right hh]; rfl)
    rw [he] at hz
    contradiction
  exact wp_nil (fast_finish h full hs)

end VG.Proof.MlKem.AArch64.Paired
