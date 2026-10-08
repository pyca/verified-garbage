import VerifiedGarbage.Proof.ChaCha20Poly1305.X86.Gather.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86.SealGather
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86: the function called

Untrusted: everything here is checked by Lean. `vg_chacha20_poly1305_seal_gather`
calls an instance of `vg_chacha20_poly1305_seal` as an artifact (`SealFn`),
with its working space in a frame of its own, so what the proof needs of it
is its shared contract (`Spec.ChaCha20Poly1305.sealContract`, with 772 bytes
of stack): its precondition from the layout the call gives it (`callPre`,
`sealSpec_pre`), its postcondition (`sealSpec_post`) and its public data
(`sealSpec_pub`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86.Gather

open VG VG.X86
open VG.Proof.AesGcm.X86 (w64 toNat_w64)
open VG.Proof.AesGcm.X86.Gather (sw32)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt)

/-- An instance of `vg_chacha20_poly1305_seal`, by its shared contract, which
never writes `esp` and whose calls and frames use at most the 772 bytes
below the stack pointer that the contract reserves. -/
structure SealFn where
  name : String
  code : Prog isa
  verified : Verified X86.target code (Spec.ChaCha20Poly1305.sealContract X86.abi 772)
  noSp : NoSp code
  depth : stackUse code ≤ 772

/-- What a call of `vg_chacha20_poly1305_seal(key, nonce, aad, aad_len, data,
len, tag)` needs. -/
def callPre (s : State) : Prop :=
  let key : Region := ⟨w64 (arg s 0), 32⟩
  let nonce : Region := ⟨w64 (arg s 1), 12⟩
  let aad : Region := ⟨w64 (arg s 2), (arg s 3).toNat⟩
  let data : Region := ⟨w64 (arg s 4), (arg s 5).toNat⟩
  let tag : Region := ⟨w64 (arg s 6), 16⟩
  let args : Region := ⟨argAddr s 0, 28⟩
  let ret : Region := ⟨w64 (s.gpr .esp), 4⟩
  let stk : Region := ⟨w64 (s.gpr .esp) - BitVec.ofNat 64 772, 772⟩
  772 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 + 28 ≤ 2 ^ 32 ∧
    s.rd = [key, nonce, aad] ∧ s.wr = [data, tag, args] ∧
    key.Disjoint data ∧ key.Disjoint tag ∧ key.Disjoint args ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    nonce.Disjoint args ∧ aad.Disjoint data ∧ aad.Disjoint tag ∧ aad.Disjoint args ∧ data.Disjoint tag ∧
    data.Disjoint args ∧ tag.Disjoint args ∧
    ret.Disjoint key ∧ ret.Disjoint nonce ∧ ret.Disjoint aad ∧ ret.Disjoint data ∧ ret.Disjoint tag ∧
    ret.Disjoint args ∧
    stk.Disjoint key ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    stk.Disjoint args ∧
    (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 12 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧
    (arg s 6).toNat + 16 ≤ 2 ^ 32

/-- The shared contract's precondition, from the layout the call gives. -/
theorem sealSpec_pre {s : State} (h : callPre s) : (Spec.ChaCha20Poly1305.sealContract X86.abi 772).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁,
    a₂₂, a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂, a₃₃⟩ := h
  sig_pre [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, X86.abi, argVal, ↓reduceIte,
    Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32,
    toNat_w64]
  exact ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂,
    a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂, a₃₃⟩

/-- Its postcondition. -/
theorem sealSpec_post {s s' : State} (h : (Spec.ChaCha20Poly1305.sealContract X86.abi 772).post s s') :
    encrypt (bytesAt s.mem (w64 (arg s 0)) 32) (bytesAt s.mem (w64 (arg s 1)) 12)
        (bytesAt s.mem (w64 (arg s 2)) (arg s 3).toNat) (bytesAt s.mem (w64 (arg s 4)) (arg s 5).toNat) =
      (bytesAt s'.mem (w64 (arg s 4)) (arg s 5).toNat, bytesAt s'.mem (w64 (arg s 6)) 16) := by
  sig_post [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, Spec.ChaCha20Poly1305.sealPost,
    X86.abi, argVal, ↓reduceIte, Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil,
    Nat.reduceAdd, Nat.reduceMul, sw32, toNat_w64] at h
  exact h

/-- Its public data, from the arguments. -/
theorem sealSpec_pub {s₁ s₂ : State} (h : s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 7, arg s₁ i = arg s₂ i) :
    (Spec.ChaCha20Poly1305.sealContract X86.abi 772).pub s₁ s₂ := by
  obtain ⟨a₁, a₂⟩ := h
  sig_pub [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, X86.abi, argVal, ↓reduceIte,
    Nat.reduceEqDiff, argBytes, Nat.reduceDiv, List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul, sw32,
    toNat_w64]
  exact ⟨a₁, a₂ 0 (by decide), a₂ 1 (by decide), a₂ 2 (by decide), a₂ 3 (by decide), a₂ 4 (by decide),
    a₂ 5 (by decide), a₂ 6 (by decide)⟩

end VG.Proof.ChaCha20Poly1305.X86.Gather
