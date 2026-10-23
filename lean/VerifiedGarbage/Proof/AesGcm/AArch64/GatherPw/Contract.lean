module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Gather.Contract
public import VerifiedGarbage.Spec.Gcm.Powers8

/-!
# AES-GCM out of place from a list of slices, with the powers, AArch64: the contract

Untrusted: everything here is checked by Lean. The contract the proof of
`vg_aes_gcm_seal_gather_with_powers` is written against, which the shared
one (`Spec.Gcm.sealGatherWithPowersContract`, with the 2624 bytes of stack
below the stack pointer that its frame and its call use) implies
(`GatherPw/Verified.lean`): `vg_aes_gcm_seal_gather`'s arguments
(`Gather/Contract.lean`), and the powers `pw = [sp + 24]`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.GatherPw

open VG VG.AArch64 VG.Proof.AesGcm.AArch64.Gather
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith gathered gatheredLen)

section
variable (s : State)

/-- The powers. -/
abbrev Pw : Addr := stackArg s 3

/-- The key context, the powers, the stack arguments and the stack below the
stack pointer. -/
abbrev ctxR : Region := ⟨K s, 256⟩
abbrev pwR : Region := ⟨Pw s, 128⟩
abbrev argsR : Region := ⟨stackArgAddr s 0, 32⟩
abbrev stackR : Region := ⟨s.sp - BitVec.ofNat 64 2624, 2624⟩

end

/-- What the code of `vg_aes_gcm_seal_gather_with_powers` needs, of the
regions. -/
def gatherPre (s : State) : Prop :=
  s.rd = [ctxR s, nR s, aR s, pwR s, dsR s] ++ lsR s ++ [argsR s] ∧ s.wr = [dR s, tgR s] ∧
    (ctxR s).Disjoint (dR s) ∧ (ctxR s).Disjoint (tgR s) ∧ (nR s).Disjoint (dR s) ∧
    (nR s).Disjoint (tgR s) ∧ (aR s).Disjoint (dR s) ∧ (aR s).Disjoint (tgR s) ∧
    (dsR s).Disjoint (dR s) ∧ (dsR s).Disjoint (tgR s) ∧
    (∀ r ∈ lsR s, r.Disjoint (dR s) ∧ r.Disjoint (tgR s)) ∧
    (pwR s).Disjoint (dR s) ∧ (pwR s).Disjoint (tgR s) ∧
    (dR s).Disjoint (tgR s) ∧ (dR s).Disjoint (argsR s) ∧ (tgR s).Disjoint (argsR s) ∧
    (stackR s).Disjoint (ctxR s) ∧ (stackR s).Disjoint (nR s) ∧ (stackR s).Disjoint (aR s) ∧
    (stackR s).Disjoint (dsR s) ∧ (∀ r ∈ lsR s, (stackR s).Disjoint r) ∧ (stackR s).Disjoint (pwR s) ∧
    (stackR s).Disjoint (argsR s) ∧ (stackR s).Disjoint (dR s) ∧ (stackR s).Disjoint (tgR s) ∧
    (K s).toNat + 256 ≤ 2 ^ 64 ∧ (Nn s).toNat + NL s ≤ 2 ^ 64 ∧ (Ad s).toNat + AL s ≤ 2 ^ 64 ∧
    (Src s).toNat + Cnt s * 16 ≤ 2 ^ 64 ∧ (∀ r ∈ lsR s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (Pw s).toNat + 128 ≤ 2 ^ 64 ∧ (Dst s).toNat + L s ≤ 2 ^ 64 ∧ (Tg s).toNat + 16 ≤ 2 ^ 64 ∧
    2624 ≤ s.sp.toNat ∧ s.sp.toNat + 32 ≤ 2 ^ 64 ∧
    ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14) ∧ gl s (Cnt s) = L s

/-- What two runs agree on: the arguments and the descriptors. -/
def gatherPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
    stackArg s₁ 3 = stackArg s₂ 3 ∧
    ∀ i < Cnt s₁ * 16, s₁.mem (Src s₁ + BitVec.ofNat 64 i) = s₂.mem (Src s₁ + BitVec.ofNat 64 i)

/-- `vg_aes_gcm_seal_gather_with_powers`: `gatherPost`, given the powers of
the key context's hash subkey. -/
def gatherAArch64 : Contract isa where
  pre s := gatherPre s ∧ Spec.Gcm.Powers8Repr s.mem (Pw s) (ctxH s.mem (K s))
  post := gatherPost
  pub := gatherPub

end VG.Proof.AesGcm.AArch64.GatherPw
