import VerifiedGarbage.Proof.AesGcm.Arm.Gather.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Impl.AesGcm.Arm.SealGather
import VerifiedGarbage.Spec.Gcm.Contract

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, ARMv7: the function called

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather`
calls `vg_aes_gcm_seal` as an artifact (`SealFn`), with its working space in
a frame of its own, so what the proof needs of it is its shared contract
(`Spec.Gcm.sealContract`, with 2600 bytes of stack): its precondition from
the layout the call gives it (`callPre`, `sealSpec_pre`), its postcondition
(`sealSpec_post`) and its public data (`sealSpec_pub`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm.Gather

open VG VG.Arm VG.Arm.FrameStack
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith)

/-- `vg_aes_gcm_seal`, by its shared contract, whose frames use at most the
2600 bytes below the stack pointer that the contract reserves. -/
structure SealFn where
  name : String
  code : Prog isa
  verified : Verified Arm.target code (Spec.Gcm.sealContract Arm.abi 2600)
  depth : armStack code ≤ 2600

/-- What a call of `vg_aes_gcm_seal(ctx = r0, rounds = r1, nonce = r2,
nonce_len = r3, aad = [sp], aad_len = [sp + 4], data = [sp + 8],
len = [sp + 12], tag = [sp + 16])` needs. -/
def callPre (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
  let data : Region := ⟨State.addr (stackArg s 2), (stackArg s 3).toNat⟩
  let tag : Region := ⟨State.addr (stackArg s 4), 16⟩
  let arg : Region := ⟨stackArgAddr s 0, 20⟩
  let stk : Region := ⟨State.addr s.sp - BitVec.ofNat 64 2600, 2600⟩
  s.rd = [ctx, nonce, aad, arg] ∧ s.wr = [data, tag] ∧
    ctx.Disjoint data ∧ ctx.Disjoint tag ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    aad.Disjoint data ∧ aad.Disjoint tag ∧ data.Disjoint tag ∧ data.Disjoint arg ∧ tag.Disjoint arg ∧
    stk.Disjoint ctx ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    stk.Disjoint arg ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧ (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 32 ∧
    (stackArg s 4).toNat + 16 ≤ 2 ^ 32 ∧ 2600 ≤ s.sp.toNat ∧ s.sp.toNat + 20 ≤ 2 ^ 32 ∧
    ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)

/-- The shared contract's precondition, from the layout the call gives. -/
theorem sealSpec_pre {s : State} (h : callPre s) : (Spec.Gcm.sealContract Arm.abi 2600).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ a₂₃ a₂₄
  have a₂₅ := h
  clear h
  sig_pre [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, List.append_eq]
  exact ⟨a₂₃, a₂₄, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀,
    a₂₁, a₂₂, a₂₅⟩

/-- Its postcondition, for rounds of 10, 12 or 14. -/
theorem sealSpec_post {s s' : State} (h : (Spec.Gcm.sealContract Arm.abi 2600).post s s')
    (hR : (s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14) :
    encryptWith (ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (ctxH s.mem (State.addr (s.gpr .r0))) 16
        (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
        (bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat)
        (bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat) =
      (bytesAt s'.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat, bytesAt s'.mem (State.addr (stackArg s 4)) 16) := by
  sig_post [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPost, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, List.append_eq] at h
  exact h hR

/-- Its public data, from the arguments. -/
theorem sealSpec_pub {s₁ s₂ : State} (h : s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp ∧
    ∀ i < 5, stackArg s₁ i = stackArg s₂ i) : (Spec.Gcm.sealContract Arm.abi 2600).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩ := h
  sig_pub [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    List.append_eq]
  exact ⟨a₅, a₁, a₂, a₃, a₄, a₆ 0 (by decide), a₆ 1 (by decide), a₆ 2 (by decide), a₆ 3 (by decide),
    a₆ 4 (by decide)⟩
end VG.Proof.AesGcm.Arm.Gather
