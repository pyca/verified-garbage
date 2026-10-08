import VerifiedGarbage.Spec.ChaCha20Poly1305.OutOfPlace
import VerifiedGarbage.Proof.AesGcm.X86.Gather.Loop
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86: the contract

Untrusted: everything here is checked by Lean. The contract the proof of
`vg_chacha20_poly1305_seal_gather` is written against, which the shared one
(`Spec.ChaCha20Poly1305.sealGatherContract`, with the 824 bytes of stack
below the stack pointer that its frame and its call use) implies
(`Gather/Verified.lean`): cdecl, `(key, nonce, aad, aad_len, src, src_count,
dst, len, tag)` at `[esp + 4]` on, which the function may overwrite.
-/

namespace VG.Proof.ChaCha20Poly1305.X86.Gather

open VG VG.X86
open VG.Proof.AesGcm.X86 (w64)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt gathered gatheredLen pMax)

section
variable (s : State)

/-- The arguments. -/
abbrev K : BitVec 32 := arg s 0
abbrev Nn : BitVec 32 := arg s 1
abbrev Ad : BitVec 32 := arg s 2
abbrev AL : Nat := (arg s 3).toNat
abbrev Src : BitVec 32 := arg s 4
abbrev Cnt : Nat := (arg s 5).toNat
abbrev Dst : BitVec 32 := arg s 6
abbrev L : Nat := (arg s 7).toNat
abbrev Tg : BitVec 32 := arg s 8

/-- The regions: the key, the nonce, the additional data, the descriptors,
the slices they list, the output, the tag, the arguments, the return address
and the stack below it. -/
abbrev kR : Region := ⟨w64 (K s), 32⟩
abbrev nR : Region := ⟨w64 (Nn s), 12⟩
abbrev aR : Region := ⟨w64 (Ad s), AL s⟩
abbrev dsR : Region := ⟨w64 (Src s), Cnt s * 8⟩
abbrev lsR : List Region := Sig.listed 32 s.mem .u8 (w64 (Src s)) (Cnt s)
abbrev dR : Region := ⟨w64 (Dst s), L s⟩
abbrev tgR : Region := ⟨w64 (Tg s), 16⟩
abbrev argR : Region := ⟨argAddr s 0, 36⟩
abbrev retR : Region := ⟨w64 (s.gpr .esp), 4⟩
abbrev stkR : Region := ⟨w64 (s.gpr .esp) - BitVec.ofNat 64 824, 824⟩

/-- The total length of the first `i` slices, and their bytes. -/
abbrev gl (i : Nat) : Nat := gatheredLen 32 s.mem (w64 (Src s)) i
abbrev pt (i : Nat) : List Byte := gathered 32 s.mem (w64 (Src s)) i

end

/-- What the code of `vg_chacha20_poly1305_seal_gather` needs. -/
def gatherPre (s : State) : Prop :=
  s.rd = [kR s, nR s, aR s, dsR s] ++ lsR s ∧ s.wr = [dR s, tgR s, argR s] ∧
    (kR s).Disjoint (dR s) ∧ (kR s).Disjoint (tgR s) ∧ (kR s).Disjoint (argR s) ∧
    (nR s).Disjoint (dR s) ∧ (nR s).Disjoint (tgR s) ∧ (nR s).Disjoint (argR s) ∧
    (aR s).Disjoint (dR s) ∧ (aR s).Disjoint (tgR s) ∧ (aR s).Disjoint (argR s) ∧
    (dR s).Disjoint (tgR s) ∧ (dR s).Disjoint (dsR s) ∧ (∀ r ∈ lsR s, (dR s).Disjoint r) ∧
    (dR s).Disjoint (argR s) ∧ (tgR s).Disjoint (dsR s) ∧ (∀ r ∈ lsR s, (tgR s).Disjoint r) ∧
    (tgR s).Disjoint (argR s) ∧ (dsR s).Disjoint (argR s) ∧ (∀ r ∈ lsR s, r.Disjoint (argR s)) ∧
    (retR s).Disjoint (kR s) ∧ (retR s).Disjoint (nR s) ∧ (retR s).Disjoint (aR s) ∧
    (retR s).Disjoint (dR s) ∧ (retR s).Disjoint (tgR s) ∧ (retR s).Disjoint (dsR s) ∧
    (∀ r ∈ lsR s, (retR s).Disjoint r) ∧ (retR s).Disjoint (argR s) ∧
    (stkR s).Disjoint (kR s) ∧ (stkR s).Disjoint (nR s) ∧ (stkR s).Disjoint (aR s) ∧
    (stkR s).Disjoint (dR s) ∧ (stkR s).Disjoint (tgR s) ∧ (stkR s).Disjoint (dsR s) ∧
    (∀ r ∈ lsR s, (stkR s).Disjoint r) ∧ (stkR s).Disjoint (argR s) ∧
    (K s).toNat + 32 ≤ 2 ^ 32 ∧ (Nn s).toNat + 12 ≤ 2 ^ 32 ∧ (Ad s).toNat + AL s ≤ 2 ^ 32 ∧
    (Dst s).toNat + L s ≤ 2 ^ 32 ∧ (Tg s).toNat + 16 ≤ 2 ^ 32 ∧
    (Src s).toNat + Cnt s * 8 ≤ 2 ^ 32 ∧ (∀ r ∈ lsR s, r.base.toNat + r.len ≤ 2 ^ 32) ∧
    824 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 40 ≤ 2 ^ 32 ∧ gl s (Cnt s) = L s ∧ L s ≤ pMax

/-- What two runs agree on: the stack pointer, the arguments and the descriptors. -/
def gatherPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 9, arg s₁ i = arg s₂ i) ∧
    ∀ i < Cnt s₁ * 8, s₁.mem (w64 (Src s₁) + BitVec.ofNat 64 i) = s₂.mem (w64 (Src s₁) + BitVec.ofNat 64 i)

/-- What `vg_chacha20_poly1305_seal_gather` leaves: `sealGatherPost`. -/
def gatherPost (s s' : State) : Prop :=
  encrypt (bytesAt s.mem (w64 (K s)) 32) (bytesAt s.mem (w64 (Nn s)) 12) (bytesAt s.mem (w64 (Ad s)) (AL s))
      (pt s (Cnt s)) =
    (bytesAt s'.mem (w64 (Dst s)) (L s), bytesAt s'.mem (w64 (Tg s)) 16)

/-- `vg_chacha20_poly1305_seal_gather`. -/
def gatherX86 : Contract isa where
  pre := gatherPre
  post := gatherPost
  pub := gatherPub

end VG.Proof.ChaCha20Poly1305.X86.Gather
