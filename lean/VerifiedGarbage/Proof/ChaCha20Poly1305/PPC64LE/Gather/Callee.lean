module

public import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Impl.ChaCha20Poly1305.PPC64LE.SealGather
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, PPC64LE: the function called

Untrusted: everything here is checked by Lean. `vg_chacha20_poly1305_seal_gather`
calls `vg_chacha20_poly1305_seal`, with its working space in a frame of its
own, by its shared contract (`Spec.ChaCha20Poly1305.sealContract`, with 848
bytes of stack, which its frames use: `seal_sdepth`): its precondition from
the layout the call gives it (`callPre`, `sealSpec_pre`), its postcondition
(`sealSpec_post`) and its public data (`sealSpec_pub`). As on AArch64
(`Proof/ChaCha20Poly1305/AArch64/Gather/Callee.lean`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.PPC64LE.Gather

open VG VG.PPC64LE
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt)

/-- The frames of `vg_chacha20_poly1305_seal` use the 848 bytes of stack its
contract reserves. -/
theorem seal_sdepth : sdepth Impl.ChaCha20Poly1305.PPC64LE.SealGather.sealCode = 848 := by
  decide +kernel

/-- What a call of `vg_chacha20_poly1305_seal(key = r3, nonce = r4, aad = r5,
aad_len = r6, data = r7, len = r8, tag = r9)` needs. -/
def callPre (s : State) : Prop :=
  let key : Region := ⟨s.gpr .r3, 32⟩
  let nonce : Region := ⟨s.gpr .r4, 12⟩
  let aad : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
  let data : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
  let tag : Region := ⟨s.gpr .r9, 16⟩
  let stk : Region := ⟨s.sp - BitVec.ofNat 64 848, 848⟩
  s.rd = [key, nonce, aad] ∧ s.wr = [data, tag] ∧
    key.Disjoint data ∧ key.Disjoint tag ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    aad.Disjoint data ∧ aad.Disjoint tag ∧ data.Disjoint tag ∧
    stk.Disjoint key ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    (s.gpr .r3).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 12 ≤ 2 ^ 64 ∧
    (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + 16 ≤ 2 ^ 64 ∧ 848 ≤ s.sp.toNat

theorem sealSpec_pre {s : State} (h : callPre s) :
    (Spec.ChaCha20Poly1305.sealContract PPC64LE.abi 848).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀⟩ := h
  sig_pre [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, PPC64LE.abi, PPC64LE.argRegs]
  sig_reduce [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, PPC64LE.abi,
    PPC64LE.argRegs, List.getD]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | trivial
    | omega
    | exact Region.Disjoint.symm ‹_›

theorem sealSpec_post {s s' : State} (h : (Spec.ChaCha20Poly1305.sealContract PPC64LE.abi 848).post s s') :
    encrypt (bytesAt s.mem (s.gpr .r3) 32) (bytesAt s.mem (s.gpr .r4) 12)
        (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) =
      (bytesAt s'.mem (s.gpr .r7) (s.gpr .r8).toNat, bytesAt s'.mem (s.gpr .r9) 16) := by
  sig_post [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
    Spec.ChaCha20Poly1305.sealPost, PPC64LE.abi, PPC64LE.argRegs] at h
  exact h

theorem sealSpec_pub {s₁ s₂ : State} (h : s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.sp = s₂.sp) :
    (Spec.ChaCha20Poly1305.sealContract PPC64LE.abi 848).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := h
  sig_pub [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, PPC64LE.abi, PPC64LE.argRegs]
  sig_reduce [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig, PPC64LE.abi, PPC64LE.argRegs]
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

end VG.Proof.ChaCha20Poly1305.PPC64LE.Gather
