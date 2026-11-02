module

public import VerifiedGarbage.Spec.Poly1305
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Poly1305: the RISC-V contracts

The contracts the proofs are written against; the artifacts are emitted with
the shared contracts (`Spec/Poly1305/Contract.lean`), which imply these
(`Contract.Implies`). No function uses the stack or a working space:
`finalizeScratchRISCV64` is `finalizeRISCV64` with an unused `scratch`.
-/

@[expose] public section

namespace VG.Proof.Poly1305

open Spec.Poly1305

open RISCV64 in
/-- `vg_poly1305_init(state: *mut [u64; 16], key: *const [u8; 32])`. -/
def initRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 128⟩
    let key : Region := ⟨s.gpr .a1, 32⟩
    s.rd = [key] ∧ s.wr = [state] ∧ state.Disjoint key
  post s s' := Repr s'.mem (s.gpr .a0) (bytesAt s.mem (s.gpr .a1) 32) []
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.sp = s₂.sp

open RISCV64 in
/-- `vg_poly1305_blocks(state = a0, blocks = a1, n = a2)`. -/
def blocksRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 128⟩
    let blocks : Region := ⟨s.gpr .a1, 16 * (s.gpr .a2).toNat⟩
    s.rd = [blocks] ∧ s.wr = [state] ∧ state.Disjoint blocks ∧
      (s.gpr .a1).toNat + 16 * (s.gpr .a2).toNat ≤ 2 ^ 64 ∧ (s.gpr .a0).toNat % 8 = 0
  post s s' := ∀ key msg, Repr s.mem (s.gpr .a0) key msg →
    Repr s'.mem (s.gpr .a0) key (msg ++ bytesAt s.mem (s.gpr .a1) (16 * (s.gpr .a2).toNat))
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

open RISCV64 in
/-- `vg_poly1305_update(state = a0, count = a1, data = a2, len = a3)`: only
`count mod 16`, the number of bytes buffered, matters. -/
def updateRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 128⟩
    let data : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    s.rd = [data] ∧ s.wr = [state] ∧ state.Disjoint data ∧ (s.gpr .a0).toNat % 8 = 0
  post s s' := ∀ key msg, Buffered s.mem (s.gpr .a0) key msg →
    (s.gpr .a1).toNat % 16 = msg.length % 16 →
    Buffered s'.mem (s.gpr .a0) key (msg ++ bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

open RISCV64 in
/-- `vg_poly1305_finalize(state = a0, count = a1, out = a2)`: only `count mod
16`, the number of bytes buffered, matters. -/
def finalizeRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 128⟩
    let out : Region := ⟨s.gpr .a2, 16⟩
    s.rd = [] ∧ s.wr = [state, out] ∧ state.Disjoint out ∧ (s.gpr .a0).toNat % 8 = 0
  post s s' := ∀ key msg, Buffered s.mem (s.gpr .a0) key msg →
    (s.gpr .a1).toNat % 16 = msg.length % 16 → bytesAt s'.mem (s.gpr .a2) 16 = mac key msg
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

open RISCV64 in
/-- `vg_poly1305_finalize_scratch(state = a0, count = a1, out = a2, scratch = a3)`:
`finalizeRISCV64`, whatever `scratch` is. -/
def finalizeScratchRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 128⟩
    let out : Region := ⟨s.gpr .a2, 16⟩
    let scratch : Region := ⟨s.gpr .a3, 128⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧ state.Disjoint out ∧ state.Disjoint scratch ∧
      out.Disjoint scratch ∧ (s.gpr .a0).toNat % 8 = 0
  post s s' := finalizeRISCV64.post s s'
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

end VG.Proof.Poly1305
