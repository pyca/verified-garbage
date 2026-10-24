module

public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealGather
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# AES-GCM encryption out of place, from a list of slices, PPC64LE: the function called

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather`
calls `vg_aes_gcm_seal`, with its working space in a frame of its own, by
its shared contract (`Spec.Gcm.sealContract`, with 2672 bytes of stack,
which its frame uses: `seal_sdepth`): its precondition from the layout the
call gives it (`callPre`: its stack argument `tag` in our frame,
`sealSpec_pre`), its postcondition (`sealSpec_post`) and its public data
(`sealSpec_pub`). As for ChaCha20-Poly1305
(`Proof/ChaCha20Poly1305/PPC64LE/Gather/Callee.lean`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE.Gather

open VG VG.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith)

/-- The frame of `vg_aes_gcm_seal` uses the 2672 bytes of stack its
contract reserves. -/
theorem seal_sdepth : sdepth Impl.AesGcm.PPC64LE.SealGather.sealCode = 2672 := by
  decide +kernel

/-- What a call of `vg_aes_gcm_seal(ctx = r3, rounds = r4, nonce = r5,
nonce_len = r6, aad = r7, aad_len = r8, data = r9, len = r10, tag)` needs,
`tag` its stack argument. -/
def callPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .r3, 256⟩
  let nonce : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
  let aad : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
  let data : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let arg : Region := ⟨stackArgAddr s 0, 8⟩
  let stk : Region := ⟨s.sp - BitVec.ofNat 64 2672, 2672⟩
  s.rd = [ctx, nonce, aad, arg] ∧ s.wr = [data, tag] ∧
    ctx.Disjoint data ∧ ctx.Disjoint tag ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    aad.Disjoint data ∧ aad.Disjoint tag ∧ data.Disjoint tag ∧ data.Disjoint arg ∧ tag.Disjoint arg ∧
    stk.Disjoint ctx ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    stk.Disjoint arg ∧
    (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + 16 ≤ 2 ^ 64 ∧ 2672 ≤ s.sp.toNat ∧ s.sp.toNat + 104 ≤ 2 ^ 64 ∧
    ((s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14)

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

theorem sealSpec_pre {s : State} (h : callPre s) : (Spec.Gcm.sealContract PPC64LE.abi 2672).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂,
    a₂₃, a₂₄, a₂₅⟩ := h
  sig_pre [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, PPC64LE.abi, PPC64LE.argRegs, stackArgs_one]
  sig_reduce [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, PPC64LE.abi, PPC64LE.argRegs, List.getD,
    stackArgs_one]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | trivial
    | omega
    | exact Region.Disjoint.symm ‹_›

theorem sealSpec_post {s s' : State} (h : (Spec.Gcm.sealContract PPC64LE.abi 2672).post s s')
    (hR : (s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14) :
    encryptWith (ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat) (ctxH s.mem (s.gpr .r3)) 16
        (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat)
        (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) =
      (bytesAt s'.mem (s.gpr .r9) (s.gpr .r10).toNat, bytesAt s'.mem (stackArg s 0) 16) := by
  sig_post [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPost, PPC64LE.abi, PPC64LE.argRegs,
    stackArgs_one] at h
  exact h hR

theorem sealSpec_pub {s₁ s₂ : State} (h : s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ s₁.sp = s₂.sp ∧
    stackArg s₁ 0 = stackArg s₂ 0) :
    (Spec.Gcm.sealContract PPC64LE.abi 2672).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀⟩ := h
  sig_pub [Spec.Gcm.sealContract, Spec.Gcm.sealSig, PPC64LE.abi, PPC64LE.argRegs, stackArgs_one]
  sig_reduce [Spec.Gcm.sealContract, Spec.Gcm.sealSig, PPC64LE.abi, PPC64LE.argRegs, stackArgs_one]
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

end VG.Proof.AesGcm.PPC64LE.Gather
