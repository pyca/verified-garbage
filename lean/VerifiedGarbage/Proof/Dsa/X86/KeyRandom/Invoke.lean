module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Call
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Result

/-! Internal derivation may use a retained invariant established by domain checking.
The sampler's proof consumes the concrete invocation's correctness proof directly. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.Proof.Mont

/-- Scratch invariants survive writes to the sampler's 120-byte stack frame. -/
def StableScratch (I : State → Mem → Prop) : Prop :=
  ∀ {s₀ : State} {m m' : Mem} {rs : List (Nat × Nat)},
    Outs (rBase s₀) rs m m' → (∀ r∈rs, r.1+r.2≤120) → I s₀ m → I s₀ m'

structure DeriveInvoke (I : State → Mem → Prop) where
  code : Prog isa
  correct : ∀ {s₀ t : State}, KeyABI s₀ → Ready s₀ t → CallSlots s₀ t →
    checked s₀=true → I s₀ t.mem → WP isa code t fun u =>
      Ready s₀ u ∧ Frame (callWrites s₀) t.mem u.mem ∧
      (∀ r∈calleeSaved, u.gpr r=t.gpr r) ∧
      u.gpr .eax=BitVec.ofNat 32 (Spec.Dsa.signStatus (callResult s₀ t)) ∧
      Spec.Rsa.bytesAt u.mem (argumentPointer s₀ 0) (arg s₀ 1).toNat=
        (callResult s₀ t).getD (List.replicate (arg s₀ 1).toNat 0)

def DeriveFn.invoke (F : DeriveFn) : DeriveInvoke (fun _ _ => True) where
  code := .call F.name F.code
  correct := fun A R C _ _ => call_ok F A R C

end VG.Proof.Dsa.X86.KeyRandom
