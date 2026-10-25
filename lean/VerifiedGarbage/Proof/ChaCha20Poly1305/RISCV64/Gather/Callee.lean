module

public import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Impl.ChaCha20Poly1305.RISCV64.SealGather
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, RISC-V: the function called

Untrusted: everything here is checked by Lean. `vg_chacha20_poly1305_seal_gather`
calls `vg_chacha20_poly1305_seal`, with its working space in a frame of its
own, by its shared contract (`Spec.ChaCha20Poly1305.sealContract`, with 624
bytes of stack, which its frame uses: `seal_sdepth`): its precondition from
the layout the call gives it (`callPre`, `sealSpec_pre`), its postcondition
(`sealSpec_post`) and its public data (`sealSpec_pub`). As on PPC64LE
(`Proof/ChaCha20Poly1305/PPC64LE/Gather/Callee.lean`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.RISCV64.Gather

open VG VG.RISCV64
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt)

/-- The frame of `vg_chacha20_poly1305_seal` uses the 624 bytes of stack its
contract reserves. -/
theorem seal_sdepth : sdepth Impl.ChaCha20Poly1305.RISCV64.SealGather.sealCode = 624 := by
  decide +kernel

/-- What a call of `vg_chacha20_poly1305_seal(key = a0, nonce = a1, aad = a2,
aad_len = a3, data = a4, len = a5, tag = a6)` needs. -/
def callPre (s : State) : Prop :=
  let key : Region := ⟨s.gpr .a0, 32⟩
  let nonce : Region := ⟨s.gpr .a1, 12⟩
  let aad : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  let data : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let tag : Region := ⟨s.gpr .a6, 16⟩
  let stk : Region := ⟨s.sp - BitVec.ofNat 64 624, 624⟩
  s.rd = [key, nonce, aad] ∧ s.wr = [data, tag] ∧
    key.Disjoint data ∧ key.Disjoint tag ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    aad.Disjoint data ∧ aad.Disjoint tag ∧ data.Disjoint tag ∧
    stk.Disjoint key ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    (s.gpr .a0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 12 ≤ 2 ^ 64 ∧
    (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a6).toNat + 16 ≤ 2 ^ 64 ∧ s.sp.toNat % 16 = 0 ∧ 624 ≤ s.sp.toNat

theorem sealSpec_pre {s : State} (h : callPre s) :
    (Spec.ChaCha20Poly1305.sealContract RISCV64.abi 624).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁⟩ := h
  sig_pre [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, RISCV64.abi, RISCV64.argRegs]
  sig_reduce [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, RISCV64.abi,
    RISCV64.argRegs, List.getD]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | trivial
    | omega
    | exact Region.Disjoint.symm ‹_›

theorem sealSpec_post {s s' : State} (h : (Spec.ChaCha20Poly1305.sealContract RISCV64.abi 624).post s s') :
    encrypt (bytesAt s.mem (s.gpr .a0) 32) (bytesAt s.mem (s.gpr .a1) 12)
        (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) =
      (bytesAt s'.mem (s.gpr .a4) (s.gpr .a5).toNat, bytesAt s'.mem (s.gpr .a6) 16) := by
  sig_post [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
    Spec.ChaCha20Poly1305.sealPost, RISCV64.abi, RISCV64.argRegs] at h
  exact h

theorem sealSpec_pub {s₁ s₂ : State} (h : s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧
    s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.sp = s₂.sp) :
    (Spec.ChaCha20Poly1305.sealContract RISCV64.abi 624).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := h
  sig_pub [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, RISCV64.abi, RISCV64.argRegs]
  sig_reduce [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, RISCV64.abi, RISCV64.argRegs]
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

end VG.Proof.ChaCha20Poly1305.RISCV64.Gather
