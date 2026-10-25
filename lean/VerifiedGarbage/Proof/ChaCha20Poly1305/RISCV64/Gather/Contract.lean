module

public import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, RISC-V: the contract

Untrusted: everything here is checked by Lean. The contract the proof of
`vg_chacha20_poly1305_seal_gather` is written against, which the shared one
(`Spec.ChaCha20Poly1305.sealGatherContract`, with the 640 bytes of stack
below the stack pointer that its frame and its call use) implies
(`Gather/Verified.lean`): `(key = a0, nonce = a1, aad = a2, aad_len = a3,
src = a4, src_count = a5, dst = a6, len = a7, tag)`, `tag` the first
argument in memory (`stackArg s 0`). As on PPC64LE
(`Proof/ChaCha20Poly1305/PPC64LE/Gather/Contract.lean`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.RISCV64.Gather

open VG VG.RISCV64
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt gathered gatheredLen pMax)

section
variable (s : State)

/-- The arguments. -/
abbrev K : Addr := s.gpr .a0
abbrev Nn : Addr := s.gpr .a1
abbrev Ad : Addr := s.gpr .a2
abbrev AL : Nat := (s.gpr .a3).toNat
abbrev Src : Addr := s.gpr .a4
abbrev Cnt : Nat := (s.gpr .a5).toNat
abbrev Dst : Addr := s.gpr .a6
abbrev L : Nat := (s.gpr .a7).toNat
abbrev Tg : Addr := stackArg s 0

/-- The regions: the key, the nonce, the additional data, the descriptors,
the slices they list, the output, the tag, the stack argument and the stack
below the stack pointer. -/
abbrev kR : Region := ⟨K s, 32⟩
abbrev nR : Region := ⟨Nn s, 12⟩
abbrev aR : Region := ⟨Ad s, AL s⟩
abbrev dsR : Region := ⟨Src s, Cnt s * 16⟩
abbrev lsR : List Region := Sig.listed 64 s.mem .u8 (Src s) (Cnt s)
abbrev dR : Region := ⟨Dst s, L s⟩
abbrev tgR : Region := ⟨Tg s, 16⟩
abbrev argR : Region := ⟨stackArgAddr s 0, 8⟩
abbrev stkR : Region := ⟨s.sp - BitVec.ofNat 64 640, 640⟩

/-- The total length of the first `i` slices, and their bytes. -/
abbrev gl (i : Nat) : Nat := gatheredLen 64 s.mem (Src s) i
abbrev pt (i : Nat) : List Byte := gathered 64 s.mem (Src s) i

end

/-- What the code of `vg_chacha20_poly1305_seal_gather` needs. -/
def gatherPre (s : State) : Prop :=
  s.rd = [kR s, nR s, aR s, dsR s] ++ lsR s ++ [argR s] ∧ s.wr = [dR s, tgR s] ∧
    (kR s).Disjoint (dR s) ∧ (kR s).Disjoint (tgR s) ∧ (nR s).Disjoint (dR s) ∧
    (nR s).Disjoint (tgR s) ∧ (aR s).Disjoint (dR s) ∧ (aR s).Disjoint (tgR s) ∧
    (dsR s).Disjoint (dR s) ∧ (dsR s).Disjoint (tgR s) ∧
    (∀ r ∈ lsR s, r.Disjoint (dR s) ∧ r.Disjoint (tgR s)) ∧
    (dR s).Disjoint (tgR s) ∧ (dR s).Disjoint (argR s) ∧ (tgR s).Disjoint (argR s) ∧
    (stkR s).Disjoint (kR s) ∧ (stkR s).Disjoint (nR s) ∧ (stkR s).Disjoint (aR s) ∧
    (stkR s).Disjoint (dsR s) ∧ (∀ r ∈ lsR s, (stkR s).Disjoint r) ∧ (stkR s).Disjoint (argR s) ∧
    (stkR s).Disjoint (dR s) ∧ (stkR s).Disjoint (tgR s) ∧
    (K s).toNat + 32 ≤ 2 ^ 64 ∧ (Nn s).toNat + 12 ≤ 2 ^ 64 ∧ (Ad s).toNat + AL s ≤ 2 ^ 64 ∧
    (Src s).toNat + Cnt s * 16 ≤ 2 ^ 64 ∧ (∀ r ∈ lsR s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (Dst s).toNat + L s ≤ 2 ^ 64 ∧ (Tg s).toNat + 16 ≤ 2 ^ 64 ∧
    s.sp.toNat % 16 = 0 ∧ 640 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 64 ∧ gl s (Cnt s) = L s ∧ L s ≤ pMax

/-- What two runs agree on: the arguments and the descriptors. -/
def gatherPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ s₁.sp = s₂.sp ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    ∀ i < Cnt s₁ * 16, s₁.mem (Src s₁ + BitVec.ofNat 64 i) = s₂.mem (Src s₁ + BitVec.ofNat 64 i)

/-- What `vg_chacha20_poly1305_seal_gather` leaves: `sealGatherPost`. -/
def gatherPost (s s' : State) : Prop :=
  encrypt (bytesAt s.mem (K s) 32) (bytesAt s.mem (Nn s) 12) (bytesAt s.mem (Ad s) (AL s)) (pt s (Cnt s)) =
    (bytesAt s'.mem (Dst s) (L s), bytesAt s'.mem (Tg s) 16)

/-- `vg_chacha20_poly1305_seal_gather`. -/
def gatherRISCV64 : Contract isa where
  pre := gatherPre
  post := gatherPost
  pub := gatherPub

end VG.Proof.ChaCha20Poly1305.RISCV64.Gather
