import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Gather.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.SealGather

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, AArch64: the function called

Untrusted: everything here is checked by Lean. `vg_chacha20_poly1305_seal_gather`
calls an implementation of `vg_chacha20_poly1305_seal` as an artifact
(`SealFn`), with its working space in a frame of its own, so what the proof
needs of it is its shared contract (`Spec.ChaCha20Poly1305.sealContract`,
with 768 bytes of stack): its precondition from the layout the call gives it
(`callPre`, `sealSpec_pre`), its postcondition (`sealSpec_post`) and its
public data (`sealSpec_pub`).
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64.Gather

open VG VG.AArch64
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt)

/-- An implementation of `vg_chacha20_poly1305_seal`, by its shared
contract, whose frames use at most the 768 bytes below the stack pointer that
the contract reserves. -/
structure SealFn where
  name : String
  code : Prog isa
  verified : Verified AArch64.target code (Spec.ChaCha20Poly1305.sealContract AArch64.abi 768)
  depth : 16 * code.aarch64Depth ≤ 768

/-- What a call of `vg_chacha20_poly1305_seal(key = x0, nonce = x1, aad = x2,
aad_len = x3, data = x4, len = x5, tag = x6)` needs. -/
def callPre (s : State) : Prop :=
  let key : Region := ⟨s.gpr .x0, 32⟩
  let nonce : Region := ⟨s.gpr .x1, 12⟩
  let aad : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let data : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let tag : Region := ⟨s.gpr .x6, 16⟩
  let stk : Region := ⟨s.sp - BitVec.ofNat 64 768, 768⟩
  s.rd = [key, nonce, aad] ∧ s.wr = [data, tag] ∧
    key.Disjoint data ∧ key.Disjoint tag ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    aad.Disjoint data ∧ aad.Disjoint tag ∧ data.Disjoint tag ∧
    stk.Disjoint key ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    (s.gpr .x0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 12 ≤ 2 ^ 64 ∧
    (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x6).toNat + 16 ≤ 2 ^ 64 ∧ 768 ≤ s.sp.toNat

theorem sealSpec_pre {s : State} (h : callPre s) :
    (Spec.ChaCha20Poly1305.sealContract AArch64.abi 768).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀⟩ := h
  sig_pre [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, AArch64.abi, AArch64.argRegs]
  sig_reduce [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, AArch64.abi,
    AArch64.argRegs, List.getD]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | trivial
    | omega
    | exact Region.Disjoint.symm ‹_›

theorem sealSpec_post {s s' : State} (h : (Spec.ChaCha20Poly1305.sealContract AArch64.abi 768).post s s') :
    encrypt (bytesAt s.mem (s.gpr .x0) 32) (bytesAt s.mem (s.gpr .x1) 12)
        (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) =
      (bytesAt s'.mem (s.gpr .x4) (s.gpr .x5).toNat, bytesAt s'.mem (s.gpr .x6) 16) := by
  sig_post [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
    Spec.ChaCha20Poly1305.sealPost, AArch64.abi, AArch64.argRegs] at h
  exact h

theorem sealSpec_pub {s₁ s₂ : State} (h : s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧
    s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.sp = s₂.sp) :
    (Spec.ChaCha20Poly1305.sealContract AArch64.abi 768).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := h
  sig_pub [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, AArch64.abi, AArch64.argRegs]
  sig_reduce [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, AArch64.abi, AArch64.argRegs]
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

end VG.Proof.ChaCha20Poly1305.AArch64.Gather
