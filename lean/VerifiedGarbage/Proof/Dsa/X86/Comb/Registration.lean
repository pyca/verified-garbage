module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout

/-! Kernel-checked fixed-width instances and stack-safety for registration. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb

theorem supported_16_5 : Supported 16 5 := by unfold Supported; decide
theorem supported_32_5 : Supported 32 5 := by unfold Supported; decide
theorem supported_32_7 : Supported 32 7 := by unfold Supported; decide
theorem supported_32_8 : Supported 32 8 := by unfold Supported; decide
theorem supported_48_8 : Supported 48 8 := by unfold Supported; decide

theorem body_spSafe {n e : Nat} (h : Supported n e) (prepare : Bool) :
    (body prepare n e).all (fun i => !isa.writesSp i)=true := by
  cases prepare <;>
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide +kernel

end VG.Proof.Dsa.X86.Comb
