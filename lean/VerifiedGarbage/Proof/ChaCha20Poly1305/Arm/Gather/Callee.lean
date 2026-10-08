import VerifiedGarbage.Proof.ChaCha20Poly1305.Arm.Gather.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Impl.ChaCha20Poly1305.Arm.SealGather

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, ARMv7: the function called

Untrusted: everything here is checked by Lean. `vg_chacha20_poly1305_seal_gather`
calls `vg_chacha20_poly1305_seal` as an artifact (`SealFn`), with its
working space in a frame of its own, so what the proof needs of it is its
shared contract (`Spec.ChaCha20Poly1305.sealContract`, with 664 bytes of
stack): its precondition from the layout the call gives it (`callPre`,
`sealSpec_pre`), its postcondition (`sealSpec_post`) and its public data
(`sealSpec_pub`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.Arm.Gather

open VG VG.Arm VG.Arm.FrameStack
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt)

/-- `vg_chacha20_poly1305_seal`, by its shared contract, whose frames use at
most the 664 bytes below the stack pointer that the contract reserves. -/
structure SealFn where
  name : String
  code : Prog isa
  verified : Verified Arm.target code (Spec.ChaCha20Poly1305.sealContract Arm.abi 664)
  depth : armStack code ≤ 664

/-- What a call of `vg_chacha20_poly1305_seal(key = r0, nonce = r1, aad = r2,
aad_len = r3, data = [sp], len = [sp + 4], tag = [sp + 8])` needs. -/
def callPre (s : State) : Prop :=
  let key : Region := ⟨State.addr (s.gpr .r0), 32⟩
  let nonce : Region := ⟨State.addr (s.gpr .r1), 12⟩
  let aad : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
  let tag : Region := ⟨State.addr (stackArg s 2), 16⟩
  let arg : Region := ⟨stackArgAddr s 0, 12⟩
  let stk : Region := ⟨State.addr s.sp - BitVec.ofNat 64 664, 664⟩
  s.rd = [key, nonce, aad, arg] ∧ s.wr = [data, tag] ∧
    key.Disjoint data ∧ key.Disjoint tag ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    aad.Disjoint data ∧ aad.Disjoint tag ∧ data.Disjoint tag ∧ data.Disjoint arg ∧ tag.Disjoint arg ∧
    stk.Disjoint key ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    stk.Disjoint arg ∧
    (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 12 ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
    (stackArg s 2).toNat + 16 ≤ 2 ^ 32 ∧ 664 ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32

/-- The shared contract's precondition, from the layout the call gives. -/
theorem sealSpec_pre {s : State} (h : callPre s) : (Spec.ChaCha20Poly1305.sealContract Arm.abi 664).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁,
    a₂₂, a₂₃, a₂₄⟩ := h
  sig_pre [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, List.append_eq]
  exact ⟨a₂₃, a₂₄, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀,
    a₂₁, a₂₂⟩

/-- Its postcondition. -/
theorem sealSpec_post {s s' : State} (h : (Spec.ChaCha20Poly1305.sealContract Arm.abi 664).post s s') :
    encrypt (bytesAt s.mem (State.addr (s.gpr .r0)) 32) (bytesAt s.mem (State.addr (s.gpr .r1)) 12)
        (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
        (bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat) =
      (bytesAt s'.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat,
        bytesAt s'.mem (State.addr (stackArg s 2)) 16) := by
  sig_post [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, Spec.ChaCha20Poly1305.sealPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, List.append_eq] at h
  exact h

/-- Its public data, from the arguments. -/
theorem sealSpec_pub {s₁ s₂ : State} (h : s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp ∧
    ∀ i < 3, stackArg s₁ i = stackArg s₂ i) : (Spec.ChaCha20Poly1305.sealContract Arm.abi 664).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩ := h
  sig_pub [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, List.append_eq]
  exact ⟨a₅, a₁, a₂, a₃, a₄, a₆ 0 (by decide), a₆ 1 (by decide), a₆ 2 (by decide)⟩

end VG.Proof.ChaCha20Poly1305.Arm.Gather
