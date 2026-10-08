import VerifiedGarbage.Proof.AesGcm.X86.Gather.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Impl.AesGcm.X86.SealGather
import VerifiedGarbage.Spec.Gcm.Contract

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86: the function called

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather`
calls an instance of `vg_aes_gcm_seal` as an artifact (`SealFn`), with its
working space in a frame of its own, so what the proof needs of it is its
shared contract (`Spec.Gcm.sealContract`, with 2632 bytes of stack): its
precondition from the layout the call gives it (`callPre`, `sealSpec_pre`),
its postcondition (`sealSpec_post`) and its public data (`sealSpec_pub`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86.Gather

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith)

/-- An instance of `vg_aes_gcm_seal`, by its shared contract, which never
writes `esp` and whose calls and frames use at most the 2632 bytes below the
stack pointer that the contract reserves. -/
structure SealFn where
  name : String
  code : Prog isa
  verified : Verified X86.target code (Spec.Gcm.sealContract X86.abi 2632)
  noSp : NoSp code
  depth : stackUse code ≤ 2632

theorem sw32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt x.isLt]

/-- What a call of `vg_aes_gcm_seal(ctx, rounds, nonce, nonce_len, aad,
aad_len, data, len, tag)` needs. -/
def callPre (s : State) : Prop :=
  let ctx : Region := ⟨w64 (arg s 0), 256⟩
  let nonce : Region := ⟨w64 (arg s 2), (arg s 3).toNat⟩
  let aad : Region := ⟨w64 (arg s 4), (arg s 5).toNat⟩
  let data : Region := ⟨w64 (arg s 6), (arg s 7).toNat⟩
  let tag : Region := ⟨w64 (arg s 8), 16⟩
  let args : Region := ⟨argAddr s 0, 36⟩
  let ret : Region := ⟨w64 (s.gpr .esp), 4⟩
  let stk : Region := ⟨w64 (s.gpr .esp) - BitVec.ofNat 64 2632, 2632⟩
  2632 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 + 36 ≤ 2 ^ 32 ∧
    s.rd = [ctx, nonce, aad] ∧ s.wr = [data, tag, args] ∧
    ctx.Disjoint data ∧ ctx.Disjoint tag ∧ ctx.Disjoint args ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    nonce.Disjoint args ∧ aad.Disjoint data ∧ aad.Disjoint tag ∧ aad.Disjoint args ∧ data.Disjoint tag ∧
    data.Disjoint args ∧ tag.Disjoint args ∧
    ret.Disjoint ctx ∧ ret.Disjoint nonce ∧ ret.Disjoint aad ∧ ret.Disjoint data ∧ ret.Disjoint tag ∧
    ret.Disjoint args ∧
    stk.Disjoint ctx ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    stk.Disjoint args ∧
    (arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
    (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32 ∧
    (arg s 8).toNat + 16 ≤ 2 ^ 32 ∧
    ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)

/-- The shared contract's precondition, from the layout the call gives. -/
theorem sealSpec_pre {s : State} (h : callPre s) : (Spec.Gcm.sealContract X86.abi 2632).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁,
    a₂₂, a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂, a₃₃, a₃₄⟩ := h
  sig_pre [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, X86.abi, argVal, ↓reduceIte,
    Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32,
    toNat_w64]
  exact ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂,
    a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂, a₃₃, a₃₄⟩

/-- Its postcondition, for rounds of 10, 12 or 14. -/
theorem sealSpec_post {s s' : State} (h : (Spec.Gcm.sealContract X86.abi 2632).post s s')
    (hR : (arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14) :
    encryptWith (ctxCiph s.mem (w64 (arg s 0)) (arg s 1).toNat) (ctxH s.mem (w64 (arg s 0))) 16
        (bytesAt s.mem (w64 (arg s 2)) (arg s 3).toNat) (bytesAt s.mem (w64 (arg s 6)) (arg s 7).toNat)
        (bytesAt s.mem (w64 (arg s 4)) (arg s 5).toNat) =
      (bytesAt s'.mem (w64 (arg s 6)) (arg s 7).toNat, bytesAt s'.mem (w64 (arg s 8)) 16) := by
  sig_post [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPost, X86.abi, argVal, ↓reduceIte,
    Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32,
    toNat_w64] at h
  exact h hR

/-- Its public data, from the arguments. -/
theorem sealSpec_pub {s₁ s₂ : State} (h : s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 9, arg s₁ i = arg s₂ i) :
    (Spec.Gcm.sealContract X86.abi 2632).pub s₁ s₂ := by
  obtain ⟨a₁, a₂⟩ := h
  sig_pub [Spec.Gcm.sealContract, Spec.Gcm.sealSig, X86.abi, argVal, ↓reduceIte, Nat.reduceEqDiff, argBytes,
    Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32, toNat_w64]
  exact ⟨a₁, a₂ 0 (by decide), a₂ 1 (by decide), a₂ 2 (by decide), a₂ 3 (by decide), a₂ 4 (by decide),
    a₂ 5 (by decide), a₂ 6 (by decide), a₂ 7 (by decide), a₂ 8 (by decide)⟩

end VG.Proof.AesGcm.X86.Gather
