module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.DeriveInvoke
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.InvokeTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.InvokeInputs
import VerifiedGarbage.Proof.Dsa.X86.Comb.DerivingOperationTiming
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.InlineInvokeTiming
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.Basic
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.AllocatedArgs

/-! The prevalidated internal body runs with public parameters and a secret scalar. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.Comb

theorem deriveInvoke_ct : DeriveInvokeCT deriveInvoke := by
  intro s t tr ur sf tf ⟨s₀,t₀,A,B,Pub,Key,R,S,C,D,_,OkS,OkT,Cs,Ct⟩ E F
  let u := (allocated 4 s).withRegions (callRd s₀) (callWr s₀)
  let v := (allocated 4 t).withRegions (callRd t₀) (callWr t₀)
  have Au : DerivingABI u := allocated_derivingABI A R C
  have Bv : DerivingABI v := allocated_derivingABI B S D
  have Vu := derive_allocated_valid A R C OkS
  have Vv := derive_allocated_valid B S D OkT
  have Cu := derive_allocated_context A R C Cs
  have Cv := derive_allocated_context B S D Ct
  obtain ⟨rs,ws⟩ := call_covers A R
  obtain ⟨rt,wt⟩ := call_covers B S
  obtain ⟨uf,Eu⟩ := inlineInvoke_trace rs ws ((derivingOperation_spec Au Vu Cu).mono (fun _ _ => trivial)) E
  obtain ⟨vf,Ev⟩ := inlineInvoke_trace rt wt ((derivingOperation_spec Bv Vv Cv).mono (fun _ _ => trivial)) F
  have SP := esp_of_rf R.rf (pub_rBase Pub ▸ S.rf)
  have args (i : Nat) (hi : i<9) : arg u i=arg v i := by
    rw [derive_allocated_args R C i hi,derive_allocated_args S D i hi]
    interval_cases i <;> simp only [callVal,SP] <;> exact pub_arg Pub _ (by decide)
  have KeyEq : (rInput s₀).key=(rInput t₀).key :=
    (List.map_injective_iff.mpr (fun _ _ h => BitVec.eq_of_toNat_eq h)) Key
  have Params : derivingParams u=derivingParams v := by
    rw [derive_allocated_params A R C,derive_allocated_params B S D,
      pub_arg Pub 5 (by decide),pub_arg Pub 6 (by decide),KeyEq]
  exact ⟨derivingOperation_agrees Au Bv args (by change s.gpr .esp-4=t.gpr .esp-4; rw [SP])
    (congrArg Spec.Dsa.Params.p Params) (congrArg Spec.Dsa.Params.q Params) Vu Vv Cu Cv Eu Ev,trivial⟩

end VG.Proof.Dsa.X86.Comb
