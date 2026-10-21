module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Invoke
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Context

/-! Domain checking establishes the scratch invariant consumed after sampling. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86

structure CheckInvoke (I : State → Mem → Prop) where
  code : Prog isa
  correct : ∀ {s₀ t : State}, KeyABI s₀ → Ready s₀ t → CheckCall.CallSlots s₀ t →
    WP isa code t fun u => Ready s₀ u ∧ Frame (CheckCall.callWrites s₀) t.mem u.mem ∧
      (∀ r∈calleeSaved, u.gpr r=t.gpr r) ∧
      u.gpr .eax=(if CheckCall.callResult s₀ t then 1 else 0) ∧
      (CheckCall.callResult s₀ t=true → I s₀ u.mem)

def CheckCall.CheckFn.invoke (F : CheckCall.CheckFn) : CheckInvoke (fun _ _ => True) where
  code := .call F.name F.code
  correct := fun A R C => WP.mono (CheckCall.call_ok F A R C) fun _ ⟨R,F,K,V⟩ =>
    ⟨R,F,K,V,fun _ => trivial⟩

end VG.Proof.Dsa.X86.KeyRandom
