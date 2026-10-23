module

public import VerifiedGarbage.Spec.Poly1305
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Poly1305: the PPC64LE contracts

The contracts the proofs are written against; the artifacts are emitted with
the shared contracts (`Spec/Poly1305/Contract.lean`, and for `blocks` and
`update` with their working space as an argument,
`Proof/Poly1305/BlocksScratch.lean` and `Proof/Poly1305/Scratch.lean`), which
imply these (`Contract.Implies`).

`blocks`, `update` and `finalize` take a working space, where they save the
nonvolatile registers they use (`r14`–`r21`, in its first 64 bytes).
-/

@[expose] public section

namespace VG.Proof.Poly1305

open Spec.Poly1305

open PPC64LE in
/-- `vg_poly1305_init(state: *mut [u64; 16], key: *const [u8; 32])`. -/
def initPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 128⟩
    let key : Region := ⟨s.gpr .r4, 32⟩
    s.rd = [key] ∧ s.wr = [state] ∧ state.Disjoint key
  post s s' := Repr s'.mem (s.gpr .r3) (bytesAt s.mem (s.gpr .r4) 32) []
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.sp = s₂.sp

open PPC64LE in
/-- `blocks(state = r3, blocks = r4, n = r5, scratch = r6)`,
`vg_poly1305_blocks` with its working space (128 bytes) in `scratch`. -/
def blocksPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 128⟩
    let blocks : Region := ⟨s.gpr .r4, 16 * (s.gpr .r5).toNat⟩
    let scratch : Region := ⟨s.gpr .r6, 128⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧ state.Disjoint blocks ∧
      state.Disjoint scratch ∧ blocks.Disjoint scratch ∧
      (s.gpr .r4).toNat + 16 * (s.gpr .r5).toNat ≤ 2 ^ 64
  post s s' := ∀ key msg, Repr s.mem (s.gpr .r3) key msg →
    Repr s'.mem (s.gpr .r3) key (msg ++ bytesAt s.mem (s.gpr .r4) (16 * (s.gpr .r5).toNat))
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

open PPC64LE in
/-- `update(state = r3, count = r4, data = r5, len = r6, scratch = r7)`,
`vg_poly1305_update` with its working space (128 bytes) in `scratch`: only
`count mod 16`, the number of bytes buffered, matters. -/
def updatePPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 128⟩
    let data : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, 128⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧ state.Disjoint data ∧ state.Disjoint scratch ∧
      data.Disjoint scratch
  post s s' := ∀ key msg, Buffered s.mem (s.gpr .r3) key msg →
    (s.gpr .r4).toNat % 16 = msg.length % 16 →
    Buffered s'.mem (s.gpr .r3) key (msg ++ bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

open PPC64LE in
/-- `finalize(state = r3, count = r4, out = r5, scratch = r6)`,
`vg_poly1305_finalize` with its working space (128 bytes) in `scratch`: only
`count mod 16`, the number of bytes buffered, matters. -/
def finalizePPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 128⟩
    let out : Region := ⟨s.gpr .r5, 16⟩
    let scratch : Region := ⟨s.gpr .r6, 128⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧ state.Disjoint out ∧ state.Disjoint scratch ∧
      out.Disjoint scratch
  post s s' := ∀ key msg, Buffered s.mem (s.gpr .r3) key msg →
    (s.gpr .r4).toNat % 16 = msg.length % 16 → bytesAt s'.mem (s.gpr .r5) 16 = mac key msg
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

end VG.Proof.Poly1305
