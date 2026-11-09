module
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCall

import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCorrect
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.X86_64.Round

/-!
# ML-DSA on x86-64, `sign_message`: verified

Untrusted: everything here is checked by Lean. `signMessage n c p`, for any
signing function on `μ` `c` that `sign_message` can call (`SignFn`), is
verified against `signMessageContract p X86_64.abi 112`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa

/-- A state satisfying the precondition. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rcx => 0x3100 | .r9 => 0x3200 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x80009 then 0x40 else if a = 0x80012 then 0x01 else 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, 32⟩, ⟨0x80008, 16⟩]
  wr := [⟨0x4000, p.sigLen⟩, ⟨0x10000, mScrLen p⟩]

theorem signMessage_sat {p : Params} (hp : p ∈ params) : ∃ s, (signMessageContract p X86_64.abi 112).pre s := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · sig_implies_sat [signMessageContract, signMessageSig, X86_64.abi, X86_64.argRegs, List.range,
      List.range.loop] [signSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using signSat mlDsa44
  · sig_implies_sat [signMessageContract, signMessageSig, X86_64.abi, X86_64.argRegs, List.range,
      List.range.loop] [signSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using signSat mlDsa65
  · sig_implies_sat [signMessageContract, signMessageSig, X86_64.abi, X86_64.argRegs, List.range,
      List.range.loop] [signSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using signSat mlDsa87

theorem signMessage_verified {p : Params} {n : String} {c : Prog isa} (hS : SignFn p c) (hp : p ∈ params) :
    Verified X86_64.target (signMessage n c p 0) (signMessageContract p X86_64.abi 112) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := signMessage_wp (prep := false) hS hp (sPre_of h)
      ⟨t, s', he, ha, sPost_of hq⟩,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => signMessage_ct (prep := false) hS hp s₁ s₂ t₁ t₂ s₁' s₂'
      (sPre_of h₁) (sPre_of h₂) (sPub_of hpub) e₁ e₂,
    signMessage_sat hp⟩

/-- `sign_message_prepared`, given a state satisfying its precondition (which holds a prepared key). -/
theorem signMessagePrepared_verified {p : Params} {n : String} {c : Prog isa} (hS : SignFn p c)
    (hp : p ∈ params) (hsat : ∃ s, (preparedSignMessageContract p X86_64.abi 112).pre s) :
    Verified X86_64.target (signMessage n c p 1) (preparedSignMessageContract p X86_64.abi 112) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := signMessage_wp (prep := true) hS hp (sPreP_of h)
      ⟨t, s', he, ha, sPostP_of hq⟩,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => signMessage_ct (prep := true) hS hp s₁ s₂ t₁ t₂ s₁' s₂'
      (sPreP_of h₁) (sPreP_of h₂) (sPubP_of hpub) e₁ e₂,
    hsat⟩

end VG.Proof.MlDsa.X86_64.Message
