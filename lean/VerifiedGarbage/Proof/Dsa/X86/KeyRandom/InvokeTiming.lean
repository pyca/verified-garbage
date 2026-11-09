module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Invoke
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallCT
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckInvoke
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CTDefs
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall

import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallResult
public import VerifiedGarbage.Proof.Dsa.Contract
/-! Relational timing for an internal derivation under its retained invariant. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/KeyRandom/CheckCallCT.lean`, which only this module imported.
section

/-! # Domain-checking calls share their public parameters and arguments -/

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom.CheckCall
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

/-- The public domain bytes of the entry. -/
abbrev keyLeak (s₀ : State) : List Nat :=
  (rInput s₀).key.map (·.toNat)

/-- Two runs about to call the callee alike. -/
def CallRel (t₁ t₂ : State) : Prop :=
  ∃ s₁ s₂, KeyABI s₁ ∧ KeyABI s₂ ∧ pubOf s₁ = pubOf s₂ ∧ keyLeak s₁ = keyLeak s₂ ∧
    Ready s₁ t₁ ∧ Ready s₂ t₂ ∧ CallSlots s₁ t₁ ∧ CallSlots s₂ t₂

end VG.Proof.Dsa.X86.KeyRandom.CheckCall
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86

def InvokeRel (I : State → Mem → Prop) (t₁ t₂ : State) : Prop :=
  ∃ s₁ s₂, KeyABI s₁ ∧ KeyABI s₂ ∧ pubOf s₁=pubOf s₂ ∧ keyLeak s₁=keyLeak s₂ ∧
    Ready s₁ t₁ ∧ Ready s₂ t₂ ∧ CallSlots s₁ t₁ ∧ CallSlots s₂ t₂ ∧
    Spec.Dsa.signStatus (callResult s₁ t₁)=Spec.Dsa.signStatus (callResult s₂ t₂) ∧
    checked s₁=true ∧ checked s₂=true ∧ I s₁ t₁.mem ∧ I s₂ t₂.mem

def DeriveInvokeCT {I : State → Mem → Prop} (F : DeriveInvoke I) : Prop :=
  RelCT isa (InvokeRel I) F.code (fun _ _ => True)

def CheckInvokeCT {I : State → Mem → Prop} (F : CheckInvoke I) : Prop :=
  RelCT isa CheckCall.CallRel F.code (fun _ _ => True)

theorem compare_mem (v : BitVec 32) (s : State) :
    WP isa (.block [.alu .cmp .eax (.imm v)]) s fun t => t.mem=s.mem :=
  wp_cmpS rfl fun _ F _ => WP.block_nil F.mem

end VG.Proof.Dsa.X86.KeyRandom
