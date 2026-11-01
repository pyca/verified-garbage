module

public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: the function called

Untrusted: everything here is checked by Lean. `vg_chacha20_poly1305_seal_gather`
calls an instance of `vg_chacha20_poly1305_seal_split` as an artifact
(`SealSplitFn`), with its working space in a frame of its own, so what the
proof needs of it is its shared contract
(`Proof.ChaCha20Poly1305.sealSplitContract`, with 1800 bytes of stack): its
precondition from the layout the call gives it (`callPre`,
`sealSplitSpec_pre`), its postcondition (`sealSplitSpec_post`) and its
public data (`sealSplitSpec_pub`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather

open VG VG.X86_64
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt)

/-- An instance of `vg_chacha20_poly1305_seal_split`, by its shared
contract, which writes `rsp` only in its frames, whose frames and calls use
at most the 1800 bytes below the stack pointer that the contract reserves. -/
structure SealSplitFn where
  name : String
  code : Prog isa
  verified : Verified X86_64.target code (Proof.ChaCha20Poly1305.sealSplitContract X86_64.abi 1800)
  sp : SpSafe code
  depth : code.x86_64Depth ≤ 1800

/-- What a call of `vg_chacha20_poly1305_seal_split(key = rdi, nonce = rsi,
aad = rdx, aad_len = rcx, src = r8, src_len = r9, dst = [rsp + 8],
len = [rsp + 16], tag = [rsp + 24])` needs. -/
def callPre (s : State) : Prop :=
  let key : Region := ⟨s.gpr .rdi, 32⟩
  let nonce : Region := ⟨s.gpr .rsi, 12⟩
  let aad : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let src : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let data : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let tag : Region := ⟨stackArg s 2, 16⟩
  let args : Region := ⟨stackArgAddr s 0, 24⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  let stk : Region := below (s.gpr .rsp) 1800
  1800 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64 ∧
    s.rd = [key, nonce, aad, src, args] ∧ s.wr = [data, tag] ∧
    key.Disjoint data ∧ key.Disjoint tag ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    aad.Disjoint data ∧ aad.Disjoint tag ∧ src.Disjoint data ∧ src.Disjoint tag ∧
    data.Disjoint tag ∧ data.Disjoint args ∧ tag.Disjoint args ∧
    ret.Disjoint key ∧ ret.Disjoint nonce ∧ ret.Disjoint aad ∧ ret.Disjoint src ∧ ret.Disjoint data ∧
    ret.Disjoint tag ∧ ret.Disjoint args ∧
    stk.Disjoint key ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint src ∧ stk.Disjoint data ∧
    stk.Disjoint tag ∧ stk.Disjoint args ∧
    (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 12 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧ (stackArg s 2).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat ≤ (stackArg s 1).toNat

theorem sealSplitSpec_pre {s : State} (h : callPre s) :
    (Proof.ChaCha20Poly1305.sealSplitContract X86_64.abi 1800).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁,
    a₂₂, a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂, a₃₃, a₃₄, a₃₅, a₃₆⟩ := h
  sig_pre [Proof.ChaCha20Poly1305.sealSplitContract, Proof.ChaCha20Poly1305.sealSplitSig,
    Proof.ChaCha20Poly1305.sealSplitPre, X86_64.abi, X86_64.argRegs]
  sig_reduce [Proof.ChaCha20Poly1305.sealSplitContract, Proof.ChaCha20Poly1305.sealSplitSig,
    Proof.ChaCha20Poly1305.sealSplitPre, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below]
  sig_and_intros
  all_goals simp only [X86_64.stackArg, X86_64.stackArgAddr, VG.X86_64.below, Nat.mul_one] at *
  all_goals first
    | with_reducible assumption
    | trivial
    | omega
    | exact Region.Disjoint.symm ‹_›

theorem sealSplitSpec_post {s s' : State}
    (h : (Proof.ChaCha20Poly1305.sealSplitContract X86_64.abi 1800).post s s')
    (hl : (s.gpr .r9).toNat ≤ (stackArg s 1).toNat) :
    encrypt (bytesAt s.mem (s.gpr .rdi) 32) (bytesAt s.mem (s.gpr .rsi) 12)
        (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat ++
          (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat).drop (s.gpr .r9).toNat) =
      (bytesAt s'.mem (stackArg s 0) (stackArg s 1).toNat, bytesAt s'.mem (stackArg s 2) 16) := by
  sig_post [Proof.ChaCha20Poly1305.sealSplitContract, Proof.ChaCha20Poly1305.sealSplitSig,
    Proof.ChaCha20Poly1305.sealSplitPost, X86_64.abi, X86_64.argRegs] at h
  sig_reduce [Proof.ChaCha20Poly1305.sealSplitContract, Proof.ChaCha20Poly1305.sealSplitSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  exact h hl

theorem sealSplitSpec_pub {s₁ s₂ : State} (h : s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2) :
    (Proof.ChaCha20Poly1305.sealSplitContract X86_64.abi 1800).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀⟩ := h
  sig_pub [Proof.ChaCha20Poly1305.sealSplitContract, Proof.ChaCha20Poly1305.sealSplitSig, X86_64.abi,
    X86_64.argRegs]
  sig_reduce [Proof.ChaCha20Poly1305.sealSplitContract, Proof.ChaCha20Poly1305.sealSplitSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop]
  simp only [X86_64.stackArg, X86_64.stackArgAddr] at a₈ a₉ a₁₀
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

end VG.Proof.ChaCha20Poly1305.X86_64.Gather
