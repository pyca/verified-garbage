module

public import VerifiedGarbage.Spec.Gcm.OutOfPlace
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, AArch64: the contract

Untrusted: everything here is checked by Lean. The contract the proof of
`vg_aes_gcm_seal_gather` is written against, which the shared one
(`Spec.Gcm.sealGatherContract`, with the 2592 bytes of stack below the stack
pointer that its frame and its call use) implies (`Gather/Verified.lean`):
`(ctx = x0, rounds = x1, nonce = x2, nonce_len = x3, aad = x4, aad_len = x5,
src = x6, src_count = x7, dst = [sp], len = [sp + 8], tag = [sp + 16])`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Gather

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith gathered gatheredLen)

/-- The key context the function reads and passes to the call of
`vg_aes_gcm_seal`: its length, at least the 256 bytes of the AES key schedule
and the hash subkey, and what it holds beyond them, which depends only on
its bytes. -/
structure CtxSpec where
  len : Nat
  le : 256 ≤ len
  inv : Mem → Addr → Prop
  congr : ∀ {m m' : Mem} {p : Addr}, (∀ i < len, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) →
    inv m p → inv m' p

/-- The key context of `vg_aes_gcm_seal`: its 256 bytes. -/
abbrev CtxSpec.plain : CtxSpec := ⟨256, Nat.le_refl _, fun _ _ => True, fun _ h => h⟩

section
variable (s : State)

/-- The arguments. -/
abbrev K : Addr := s.gpr .x0
abbrev Nn : Addr := s.gpr .x2
abbrev NL : Nat := (s.gpr .x3).toNat
abbrev Ad : Addr := s.gpr .x4
abbrev AL : Nat := (s.gpr .x5).toNat
abbrev Src : Addr := s.gpr .x6
abbrev Cnt : Nat := (s.gpr .x7).toNat
abbrev Dst : Addr := stackArg s 0
abbrev L : Nat := (stackArg s 1).toNat
abbrev Tg : Addr := stackArg s 2

/-- The regions: the nonce, the additional data, the
descriptors, the slices they list, the output, the tag, the stack arguments
and the stack below the stack pointer. -/
abbrev nR : Region := ⟨Nn s, NL s⟩
abbrev aR : Region := ⟨Ad s, AL s⟩
abbrev dsR : Region := ⟨Src s, Cnt s * 16⟩
abbrev lsR : List Region := Sig.listed 64 s.mem .u8 (Src s) (Cnt s)
abbrev dR : Region := ⟨Dst s, L s⟩
abbrev tgR : Region := ⟨Tg s, 16⟩
abbrev argR : Region := ⟨stackArgAddr s 0, 24⟩
abbrev stkR : Region := ⟨s.sp - BitVec.ofNat 64 2592, 2592⟩

/-- The total length of the first `i` slices, and their bytes. -/
abbrev gl (i : Nat) : Nat := gatheredLen 64 s.mem (Src s) i
abbrev pt (i : Nat) : List Byte := gathered 64 s.mem (Src s) i

end

/-- The key context. -/
abbrev kR (C : CtxSpec) (s : State) : Region := ⟨K s, C.len⟩

/-- What the code of `vg_aes_gcm_seal_gather` needs, of the regions. -/
def gatherPre (C : CtxSpec) (s : State) : Prop :=
  s.rd = [kR C s, nR s, aR s, dsR s] ++ lsR s ++ [argR s] ∧ s.wr = [dR s, tgR s] ∧
    (kR C s).Disjoint (dR s) ∧ (kR C s).Disjoint (tgR s) ∧ (nR s).Disjoint (dR s) ∧
    (nR s).Disjoint (tgR s) ∧ (aR s).Disjoint (dR s) ∧ (aR s).Disjoint (tgR s) ∧
    (dsR s).Disjoint (dR s) ∧ (dsR s).Disjoint (tgR s) ∧
    (∀ r ∈ lsR s, r.Disjoint (dR s) ∧ r.Disjoint (tgR s)) ∧
    (dR s).Disjoint (tgR s) ∧ (dR s).Disjoint (argR s) ∧ (tgR s).Disjoint (argR s) ∧
    (stkR s).Disjoint (kR C s) ∧ (stkR s).Disjoint (nR s) ∧ (stkR s).Disjoint (aR s) ∧
    (stkR s).Disjoint (dsR s) ∧ (∀ r ∈ lsR s, (stkR s).Disjoint r) ∧ (stkR s).Disjoint (argR s) ∧
    (stkR s).Disjoint (dR s) ∧ (stkR s).Disjoint (tgR s) ∧
    (K s).toNat + C.len ≤ 2 ^ 64 ∧ (Nn s).toNat + NL s ≤ 2 ^ 64 ∧ (Ad s).toNat + AL s ≤ 2 ^ 64 ∧
    (Src s).toNat + Cnt s * 16 ≤ 2 ^ 64 ∧ (∀ r ∈ lsR s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (Dst s).toNat + L s ≤ 2 ^ 64 ∧ (Tg s).toNat + 16 ≤ 2 ^ 64 ∧
    2592 ≤ s.sp.toNat ∧ s.sp.toNat + 24 ≤ 2 ^ 64 ∧
    ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14) ∧ gl s (Cnt s) = L s

/-- What two runs agree on: the arguments and the descriptors. -/
def gatherPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
    ∀ i < Cnt s₁ * 16, s₁.mem (Src s₁ + BitVec.ofNat 64 i) = s₂.mem (Src s₁ + BitVec.ofNat 64 i)

/-- What `vg_aes_gcm_seal_gather` leaves: `sealGatherPost`. -/
def gatherPost (s s' : State) : Prop :=
  encryptWith (ctxCiph s.mem (K s) (s.gpr .x1).toNat) (ctxH s.mem (K s)) 16 (bytesAt s.mem (Nn s) (NL s))
      (pt s (Cnt s)) (bytesAt s.mem (Ad s) (AL s)) =
    (bytesAt s'.mem (Dst s) (L s), bytesAt s'.mem (Tg s) 16)

/-- `vg_aes_gcm_seal_gather`, with the key context `C`. -/
def gatherAArch64 (C : CtxSpec) : Contract isa where
  pre s := gatherPre C s ∧ C.inv s.mem (K s)
  post := gatherPost
  pub := gatherPub

end VG.Proof.AesGcm.AArch64.Gather
