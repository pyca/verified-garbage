module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.SignCT
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Message.VerifyCT
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Message

/-!
# ML-DSA on PPC64LE, `sign_message` and `verify_message`: their contracts

`vg_mldsa*_sign_message` and `vg_mldsa*_verify_message` meet their contracts
with `S` bytes of stack, for any verified function on `μ` with at most `S`
bytes of stack (at least the 48 the sponge functions' frames take): by
correctness (`signMessage_wp`, `verifyMessage_wp`) and constant time
(`signMessage_ct`, `verifyMessage_ct`). The contracts' satisfiability (by
`msSat`, `mvSat`) is evaluated once `S` is known.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Message

open VG VG.PPC64LE
open VG.Impl.MlDsa.PPC64LE.Message
open VG.Proof.MlDsa.PPC64LE.KeyGen (Callee)
open VG.Spec.MlDsa

/-- A state that satisfies `signMessageContract`'s precondition. -/
def msSat (p : Params) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x8000 | .r6 => 0x9000 | .r8 => 0xA000 | .r9 => 0xB000 | .r10 => 0x20000
    | _ => 0
  lr := 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x8000, 0⟩, ⟨0x9000, 0⟩, ⟨0xA000, 32⟩]
  wr := [⟨0xB000, p.sigLen⟩, ⟨0x20000, messageScratchWords p * 8⟩]

/-- A state that satisfies `verifyMessageContract`'s precondition. -/
def mvSat (p : Params) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x8000 | .r6 => 0x9000 | .r8 => 0xA000 | .r9 => 0x20000 | _ => 0
  lr := 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x8000, 0⟩, ⟨0x9000, 0⟩, ⟨0xA000, p.sigLen⟩]
  wr := [⟨0x20000, messageScratchWords p * 8⟩]

/-- `vg_mldsa*_sign_message` of the parameter set `p`, calling the signing
function on `μ` `f`, named `n`, meets its contract with `S` bytes of stack. -/
theorem signMessage_verified {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {S : Nat}
    (h48 : 48 ≤ S) {f : Prog isa} (hf : Callee f (fun stk => signContract p PPC64LE.abi stk) S) (n : String)
    (hsat : (signMessageContract p PPC64LE.abi S).pre (msSat p)) :
    Verified PPC64LE.target (signMessage n f p) (signMessageContract p PPC64LE.abi S) := by
  have hF := mfacts hp3
  obtain ⟨k, rfl⟩ : ∃ k, S = k + 1 := ⟨S - 1, by omega⟩
  refine ⟨fun s hs => signMessage_wp hF h48 hf (Nat.le_refl _) (mspre_of hs),
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ⟨msSat p, hsat⟩⟩
  sig_pub [signMessageContract, signMessageSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hpub
  refine signMessage_ct hF h48 hf (Nat.le_refl _) s₁ s₂ t₁ t₂ s₁' s₂' (mspre_of h₁) (mspre_of h₂)
    ⟨hsp, hl, fun r hr => ?_⟩ e₁ e₂
  simp only [mArgs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h3, h4, h5, h6, h7, h8, h9, h10]

/-- `vg_mldsa*_verify_message` of the parameter set `p`, calling the
verification function on `μ` `f`, named `n`, meets its contract with `S`
bytes of stack. -/
theorem verifyMessage_verified {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {S : Nat}
    (h48 : 48 ≤ S) {f : Prog isa} (hf : Callee f (fun stk => verifyContract p PPC64LE.abi stk) S) (n : String)
    (hsat : (verifyMessageContract p PPC64LE.abi S).pre (mvSat p)) :
    Verified PPC64LE.target (verifyMessage n f p) (verifyMessageContract p PPC64LE.abi S) := by
  have hF := mfacts hp3
  obtain ⟨k, rfl⟩ : ∃ k, S = k + 1 := ⟨S - 1, by omega⟩
  refine ⟨fun s hs => verifyMessage_wp hF h48 hf (Nat.le_refl _) (mvpre_of hs),
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ⟨mvSat p, hsat⟩⟩
  sig_pub [verifyMessageContract, verifyMessageSig, PPC64LE.abi, PPC64LE.argRegs] at hpub
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9⟩ := hpub
  refine verifyMessage_ct hF h48 hf (Nat.le_refl _) s₁ s₂ t₁ t₂ s₁' s₂' (mvpre_of h₁) (mvpre_of h₂)
    ⟨hsp, hl, fun r hr => ?_⟩ e₁ e₂
  simp only [vArgs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h3, h4, h5, h6, h7, h8, h9]

end VG.Proof.MlDsa.PPC64LE.Message
