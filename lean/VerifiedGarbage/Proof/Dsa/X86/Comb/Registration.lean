module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout

/-! Kernel-checked fixed-width instances and stack-safety for registration. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb

theorem supported (n e : Nat) (h : Supported n e := by unfold Supported; decide) : Supported n e := h

theorem body_spSafe {n e : Nat} (h : Supported n e) (prepare : Bool) :
    (body prepare n e).all (fun i => !isa.writesSp i)=true := by
  cases prepare <;>
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide +kernel

end VG.Proof.Dsa.X86.Comb
