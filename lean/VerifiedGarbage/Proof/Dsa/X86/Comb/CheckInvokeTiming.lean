module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.CheckInvoke
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.InvokeTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.InvokeInputs
import VerifiedGarbage.Proof.Dsa.X86.Comb.CheckingOperationTiming
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.InlineInvokeTiming
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.Basic
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.AllocatedArgs

/-! The internal checker receives only public domain values. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.Comb

theorem checkInvoke_ct : CheckInvokeCT checkInvoke := by
  intro s t tr ur sf tf ⟨s₀,t₀,A,B,Pub,Key,R,S,C,D⟩ E F
  let u := (allocated 4 s).withRegions (CheckCall.callRd s₀) (CheckCall.callWr s₀)
  let v := (allocated 4 t).withRegions (CheckCall.callRd t₀) (CheckCall.callWr t₀)
  have Au : CheckingABI u := allocated_checkingABI A R C
  have Bv : CheckingABI v := allocated_checkingABI B S D
  obtain ⟨rs,ws⟩ := CheckCall.call_covers A R
  obtain ⟨rt,wt⟩ := CheckCall.call_covers B S
  obtain ⟨uf,Eu⟩ := inlineInvoke_trace rs ws ((checkingOperation_spec Au).mono (fun _ _ => trivial)) E
  obtain ⟨vf,Ev⟩ := inlineInvoke_trace rt wt ((checkingOperation_spec Bv).mono (fun _ _ => trivial)) F
  have SP := esp_of_rf R.rf (pub_rBase Pub ▸ S.rf)
  have args (i : Nat) (hi : i<6) : arg u i=arg v i := by
    rw [check_allocated_args R C i hi,check_allocated_args S D i hi]
    interval_cases i <;> simp only [CheckCall.callVal] <;> exact pub_arg Pub _ (by decide)
  have KeyEq : (rInput s₀).key=(rInput t₀).key :=
    (List.map_injective_iff.mpr (fun _ _ h => BitVec.eq_of_toNat_eq h)) Key
  have Params : checkingParams u=checkingParams v := by
    rw [check_allocated_params A R C,check_allocated_params B S D,
      pub_arg Pub 5 (by decide),pub_arg Pub 6 (by decide),KeyEq]
  exact ⟨checkingOperation_agrees Au Bv args (by change s.gpr .esp-4=t.gpr .esp-4; rw [SP])
    (congrArg Spec.Dsa.Params.p Params) (congrArg Spec.Dsa.Params.q Params)
    (congrArg Spec.Dsa.Params.g Params) Eu Ev,trivial⟩

end VG.Proof.Dsa.X86.Comb
