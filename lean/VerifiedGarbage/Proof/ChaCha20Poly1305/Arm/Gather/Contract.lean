import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, ARMv7: the contract

Untrusted: everything here is checked by Lean. The contract the proof of
`vg_chacha20_poly1305_seal_gather` is written against, which the shared one
(`Spec.ChaCha20Poly1305.sealGatherContract`, with the 696 bytes of stack
below the stack pointer that its frame and its call use) implies
(`Gather/Verified.lean`): `(key = r0, nonce = r1, aad = r2, aad_len = r3,
src = [sp], src_count = [sp + 4], dst = [sp + 8], len = [sp + 12],
tag = [sp + 16])`. Addresses are 32-bit, as memory takes them through
`State.addr`.
-/

namespace VG.Proof.ChaCha20Poly1305.Arm.Gather

open VG VG.Arm
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt gathered gatheredLen pMax)

section
variable (s : State)

/-- The arguments. -/
abbrev K : BitVec 32 := s.gpr .r0
abbrev Nn : BitVec 32 := s.gpr .r1
abbrev Ad : BitVec 32 := s.gpr .r2
abbrev AL : Nat := (s.gpr .r3).toNat
abbrev Src : BitVec 32 := stackArg s 0
abbrev Cnt : Nat := (stackArg s 1).toNat
abbrev Dst : BitVec 32 := stackArg s 2
abbrev L : Nat := (stackArg s 3).toNat
abbrev Tg : BitVec 32 := stackArg s 4

/-- The regions: the key, the nonce, the additional data, the descriptors,
the slices they list, the output, the tag, the stack arguments and the stack
below the stack pointer. -/
abbrev kR : Region := ⟨State.addr (K s), 32⟩
abbrev nR : Region := ⟨State.addr (Nn s), 12⟩
abbrev aR : Region := ⟨State.addr (Ad s), AL s⟩
abbrev dsR : Region := ⟨State.addr (Src s), Cnt s * 8⟩
abbrev lsR : List Region := Sig.listed 32 s.mem .u8 (State.addr (Src s)) (Cnt s)
abbrev dR : Region := ⟨State.addr (Dst s), L s⟩
abbrev tgR : Region := ⟨State.addr (Tg s), 16⟩
abbrev argR : Region := ⟨stackArgAddr s 0, 20⟩
abbrev stkR : Region := ⟨State.addr s.sp - BitVec.ofNat 64 696, 696⟩

/-- The total length of the first `i` slices, and their bytes. -/
abbrev gl (i : Nat) : Nat := gatheredLen 32 s.mem (State.addr (Src s)) i
abbrev pt (i : Nat) : List Byte := gathered 32 s.mem (State.addr (Src s)) i

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
    (K s).toNat + 32 ≤ 2 ^ 32 ∧ (Nn s).toNat + 12 ≤ 2 ^ 32 ∧ (Ad s).toNat + AL s ≤ 2 ^ 32 ∧
    (Src s).toNat + Cnt s * 8 ≤ 2 ^ 32 ∧ (∀ r ∈ lsR s, r.base.toNat + r.len ≤ 2 ^ 32) ∧
    (Dst s).toNat + L s ≤ 2 ^ 32 ∧ (Tg s).toNat + 16 ≤ 2 ^ 32 ∧
    696 ≤ s.sp.toNat ∧ s.sp.toNat + 20 ≤ 2 ^ 32 ∧ gl s (Cnt s) = L s ∧ L s ≤ pMax

/-- What two runs agree on: the arguments and the descriptors. -/
def gatherPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp ∧ (∀ i < 5, stackArg s₁ i = stackArg s₂ i) ∧
    ∀ i < Cnt s₁ * 8,
      s₁.mem (State.addr (Src s₁) + BitVec.ofNat 64 i) = s₂.mem (State.addr (Src s₁) + BitVec.ofNat 64 i)

/-- What `vg_chacha20_poly1305_seal_gather` leaves: `sealGatherPost`. -/
def gatherPost (s s' : State) : Prop :=
  encrypt (bytesAt s.mem (State.addr (K s)) 32) (bytesAt s.mem (State.addr (Nn s)) 12)
      (bytesAt s.mem (State.addr (Ad s)) (AL s)) (pt s (Cnt s)) =
    (bytesAt s'.mem (State.addr (Dst s)) (L s), bytesAt s'.mem (State.addr (Tg s)) 16)

/-- `vg_chacha20_poly1305_seal_gather`. -/
def gatherArm : Contract isa where
  pre := gatherPre
  post := gatherPost
  pub := gatherPub

end VG.Proof.ChaCha20Poly1305.Arm.Gather
