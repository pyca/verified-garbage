module

public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Impl.AesGcm.RISCV64.SealGather
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit

/-!
# AES-GCM encryption out of place, from a list of slices, RISCV64: the function called

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather`
calls `vg_aes_gcm_seal`, with its working space in a frame of its own, by
its shared contract (`Spec.Gcm.sealContract`, with 4624 bytes of stack,
which its frame uses: `seal_sdepth`): its precondition from the layout the
call gives it (`callPre`: its stack argument `tag` in our frame,
`sealSpec_pre`), its postcondition (`sealSpec_post`) and its public data
(`sealSpec_pub`). As for ChaCha20-Poly1305
(`Proof/ChaCha20Poly1305/RISCV64/Gather/Callee.lean`), and as on RISCV64
(`Proof/AesGcm/RISCV64/Gather/Callee.lean`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64.Gather

open VG VG.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith)

/-- The frame of `vg_aes_gcm_seal` uses the 4624 bytes of stack its
contract reserves. -/
theorem seal_sdepth : sdepth Impl.AesGcm.RISCV64.SealGather.sealCode = 4624 := by
  decide +kernel

/-- What a call of `vg_aes_gcm_seal(ctx = a0, rounds = a1, nonce = a2,
nonce_len = a3, aad = a4, aad_len = a5, data = a6, len = a7, tag)` needs,
`tag` its stack argument. -/
def callPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .a0, 256⟩
  let nonce : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  let aad : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let data : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let arg : Region := ⟨stackArgAddr s 0, 8⟩
  let stk : Region := ⟨s.sp - BitVec.ofNat 64 4624, 4624⟩
  s.rd = [ctx, nonce, aad, arg] ∧ s.wr = [data, tag] ∧
    ctx.Disjoint data ∧ ctx.Disjoint tag ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    aad.Disjoint data ∧ aad.Disjoint tag ∧ data.Disjoint tag ∧ data.Disjoint arg ∧ tag.Disjoint arg ∧
    stk.Disjoint ctx ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint data ∧ stk.Disjoint tag ∧
    stk.Disjoint arg ∧
    (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + 16 ≤ 2 ^ 64 ∧ s.sp.toNat % 16 = 0 ∧ 4624 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 64 ∧
    ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14) ∧ (s.gpr .a0).toNat % 8 = 0

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

theorem sealSpec_pre {s : State} (h : callPre s) : (Spec.Gcm.sealContract RISCV64.abi 4624).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂,
    a₂₃, a₂₄, a₂₅, a₂₆, a₂₇⟩ := h
  sig_pre [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, RISCV64.abi, RISCV64.argRegs, stackArgs_one, List.range, List.range.loop]
  sig_reduce [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPre, RISCV64.abi, RISCV64.argRegs, List.getD,
    stackArgs_one, List.range, List.range.loop]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | trivial
    | omega
    | exact Region.Disjoint.symm ‹_›

theorem sealSpec_post {s s' : State} (h : (Spec.Gcm.sealContract RISCV64.abi 4624).post s s')
    (hR : (s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14) :
    encryptWith (ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat) (ctxH s.mem (s.gpr .a0)) 16
        (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
        (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) =
      (bytesAt s'.mem (s.gpr .a6) (s.gpr .a7).toNat, bytesAt s'.mem (stackArg s 0) 16) := by
  sig_post [Spec.Gcm.sealContract, Spec.Gcm.sealSig, Spec.Gcm.sealPost, RISCV64.abi, RISCV64.argRegs,
    stackArgs_one, List.range, List.range.loop] at h
  exact h hR

theorem sealSpec_pub {s₁ s₂ : State} (h : s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧
    s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ s₁.sp = s₂.sp ∧
    stackArg s₁ 0 = stackArg s₂ 0) :
    (Spec.Gcm.sealContract RISCV64.abi 4624).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀⟩ := h
  sig_pub [Spec.Gcm.sealContract, Spec.Gcm.sealSig, RISCV64.abi, RISCV64.argRegs, stackArgs_one, List.range, List.range.loop]
  sig_reduce [Spec.Gcm.sealContract, Spec.Gcm.sealSig, RISCV64.abi, RISCV64.argRegs, stackArgs_one, List.range, List.range.loop]
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

end VG.Proof.AesGcm.RISCV64.Gather
