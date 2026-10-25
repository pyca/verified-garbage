module

public import VerifiedGarbage.Spec.ChaCha20Poly1305
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# ChaCha20-Poly1305: the RISC-V contracts

The contracts the proofs are written against; the artifacts are emitted with
the shared contracts with the working space as an argument
(`Proof/ChaCha20Poly1305/Scratch.lean`), which imply these.

`seal` and `open` take `(key = a0, nonce = a1, aad = a2, aad_len = a3,
data = a4, len = a5, tag = a6, work = a7)`: `work` (616 bytes) and `data`
may be read and written, `key`, `nonce` and `aad` read, and `tag` written
(`seal`) or read (`open`). The regions written overlap none of the others;
nothing wraps around the end of the address space. No stack is used.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305

open Spec.ChaCha20Poly1305
open Spec.Poly1305 (bytesAt)

open VG.RISCV64 in
/-- The precondition of both functions; `enc` for `seal`. -/
def preRISCV64 (enc : Bool) (s : RISCV64.State) : Prop :=
  let key : Region := ⟨s.gpr .a0, 32⟩
  let nonce : Region := ⟨s.gpr .a1, 12⟩
  let aad : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  let data : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let tag : Region := ⟨s.gpr .a6, 16⟩
  let work : Region := ⟨s.gpr .a7, 616⟩
  s.rd = (if enc then [key, nonce, aad] else [key, nonce, aad, tag]) ∧
  s.wr = (if enc then [data, tag, work] else [data, work]) ∧
  key.Disjoint data ∧ key.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
  aad.Disjoint data ∧ aad.Disjoint work ∧ data.Disjoint tag ∧ data.Disjoint work ∧
  tag.Disjoint work ∧
  (if enc then key.Disjoint tag ∧ nonce.Disjoint tag ∧ aad.Disjoint tag else True) ∧
  (s.gpr .a0).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 12 ≤ 2 ^ 64 ∧
  (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧
  (s.gpr .a6).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .a7).toNat + 616 ≤ 2 ^ 64

open VG.RISCV64 in
def pubRISCV64 (s₁ s₂ : RISCV64.State) : Prop :=
  s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
  s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
  s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ s₁.sp = s₂.sp

open VG.RISCV64 in
/-- `seal(key, nonce, aad, aad_len, data, len, tag, work)`. -/
def sealRISCV64 : Contract RISCV64.isa where
  pre := preRISCV64 true
  post s s' :=
    encrypt (bytesAt s.mem (s.gpr .a0) 32) (bytesAt s.mem (s.gpr .a1) 12)
        (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) =
      (bytesAt s'.mem (s.gpr .a4) (s.gpr .a5).toNat, bytesAt s'.mem (s.gpr .a6) 16)
  pub := pubRISCV64

open VG.RISCV64 in
/-- `open(key, nonce, aad, aad_len, data, len, tag, work) -> u32`. -/
def openRISCV64 : Contract RISCV64.isa where
  pre := preRISCV64 false
  post s s' :=
    match decrypt (bytesAt s.mem (s.gpr .a0) 32) (bytesAt s.mem (s.gpr .a1) 12)
        (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
        (bytesAt s.mem (s.gpr .a6) 16) with
    | some pt => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a4) (s.gpr .a5).toNat = pt
    | none => s'.gpr .a0 = 0
  pub := pubRISCV64

end VG.Proof.ChaCha20Poly1305
