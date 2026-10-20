module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.Depth
public import VerifiedGarbage.Impl.AesGcm.AArch64
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, AArch64: the function called

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather`
calls an implementation of `vg_aes_gcm_seal` as an artifact (`SealFn`), with
its working space in a frame of its own, so what the proof needs of it is
its contract: its precondition from the layout the call gives it
(`callPre`), its postcondition and its public data. For the shared contract
(`Spec.Gcm.sealContract`, with 2576 bytes of stack, `SealFn.plain`), they are
`sealSpec_pre`, `sealSpec_post` and `sealSpec_pub`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Gather

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith)

/-- What a call of `vg_aes_gcm_seal(ctx = x0, rounds = x1, nonce = x2,
nonce_len = x3, aad = x4, aad_len = x5, data = x6, len = x7, tag = [sp])`
needs, with the key context `C`. -/
def callPre (C : CtxSpec) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, C.len⟩
  let nonce : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  let aad : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  let data : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let arg : Region := ⟨stackArgAddr s 0, 8⟩
  let stk : Region := ⟨s.sp - BitVec.ofNat 64 2576, 2576⟩
  s.rd = [ctx, nonce, aad, arg] ∧ s.wr = [data, tag] ∧
    ctx.Disjoint data ∧ ctx.Disjoint tag ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    aad.Disjoint data ∧ aad.Disjoint tag ∧ data.Disjoint tag ∧ data.Disjoint arg ∧ tag.Disjoint arg ∧
    stk.Disjoint ctx ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    stk.Disjoint arg ∧
    (s.gpr .x0).toNat + C.len ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + 16 ≤ 2 ^ 64 ∧ 2576 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 64 ∧
    ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)

/-- An implementation of `vg_aes_gcm_seal` reading the key context `C`, by
its contract `k`, whose frames use at most the 2576 bytes below the stack
pointer that the contract reserves: `k` holds of a call as `callPre` lays it
out with `C.inv` of the context, and gives `seal`'s result. -/
structure SealFn (C : CtxSpec) where
  fn : Impl.AesGcm.AArch64.Fn
  k : Contract isa
  verified : Verified AArch64.target fn.code k
  depth : 16 * fn.code.aarch64Depth ≤ 2576
  pre : ∀ s, callPre C s → C.inv s.mem (s.gpr .x0) → k.pre s
  post : ∀ s s', k.post s s' → ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14) →
    encryptWith (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxH s.mem (s.gpr .x0)) 16
        (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
        (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) =
      (bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat, bytesAt s'.mem (stackArg s 0) 16)
  pub : ∀ s₁ s₂, s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧
    s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧
    stackArg s₁ 0 = stackArg s₂ 0 → k.pub s₁ s₂

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

theorem sealSpec_pre {s : State} (h : callPre .plain s) : (Spec.Gcm.sealContract AArch64.abi 2576).pre s := by
  sig_split h
  rename_i a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂ a₂₃ a₂₄
  have a₂₅ := h
  clear h
  sig_pre [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, AArch64.abi, AArch64.argRegs,
    stackArgs_one, List.append_eq]
  sig_reduce [Spec.Gcm.sealContract, Spec.Gcm.sealSig, AArch64.abi, AArch64.argRegs, List.getD]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | trivial
    | omega
    | exact Region.Disjoint.symm ‹_›

theorem sealSpec_post {s s' : State} (h : (Spec.Gcm.sealContract AArch64.abi 2576).post s s')
    (hR : (s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14) :
    encryptWith (ctxCiph s.mem (s.gpr .x0) (s.gpr .x1).toNat) (ctxH s.mem (s.gpr .x0)) 16
        (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
        (bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) =
      (bytesAt s'.mem (s.gpr .x6) (s.gpr .x7).toNat, bytesAt s'.mem (stackArg s 0) 16) := by
  sig_post [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPost, AArch64.abi, AArch64.argRegs,
    stackArgs_one, List.append_eq] at h
  exact h hR

theorem sealSpec_pub {s₁ s₂ : State} (h : s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧
    s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧
    stackArg s₁ 0 = stackArg s₂ 0) : (Spec.Gcm.sealContract AArch64.abi 2576).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀⟩ := h
  sig_pub [Spec.Gcm.sealContract, Spec.Gcm.sealSig, AArch64.abi, AArch64.argRegs, stackArgs_one, List.append_eq]
  sig_reduce [Spec.Gcm.sealContract, Spec.Gcm.sealSig, AArch64.abi, AArch64.argRegs]
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-- An implementation of `vg_aes_gcm_seal`, by its shared contract
(`Spec.Gcm.sealContract`, with 2576 bytes of stack). -/
def SealFn.plain (fn : Impl.AesGcm.AArch64.Fn)
    (verified : Verified AArch64.target fn.code (Spec.Gcm.sealContract AArch64.abi 2576))
    (depth : 16 * fn.code.aarch64Depth ≤ 2576) : SealFn .plain where
  fn := fn
  k := Spec.Gcm.sealContract AArch64.abi 2576
  verified := verified
  depth := depth
  pre _ h _ := sealSpec_pre h
  post _ _ h hR := sealSpec_post h hR
  pub _ _ h := sealSpec_pub h

end VG.Proof.AesGcm.AArch64.Gather
