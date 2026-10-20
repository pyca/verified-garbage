module
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Impl.Sha256.AArch64.Stream
public import VerifiedGarbage.Proof.Sha256.AArch64.Contract

import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Streaming SHA-256 on AArch64: `initQ` in the one-shot digests

What the one-shot digests need of the code storing the initial hash value
(`initQ`, `Init.lean`): its contract, that it writes no general register but
`x9` (and `x10`), and none of `v8`–`v15`.
-/

@[expose] public section

namespace VG.Proof.Sha256.AArch64.Stream

open VG VG.AArch64 VG.Impl.Sha256.AArch64.Stream
open VG.Spec.Sha256 (HashValue)

theorem initQ_ok (iv : HashValue) :
    ∀ s, (Proof.Sha256.initAArch64 iv).pre s → ∃ t s', Exec isa (initQ iv) s t s' ∧
      abiPreserved s s' ∧ (Proof.Sha256.initAArch64 iv).post s s' := fun s h => by
  obtain ⟨t, s', he, h⟩ := initQ_correct iv h
  exact ⟨t, s', he, h⟩

theorem initQ_writes (iv : HashValue) :
    ∀ r, r ≠ .x9 → r ≠ .x10 → ∀ i ∈ instrs (initQ iv), clobbers i r = false := by
  intro r h9 _ i hi
  simp only [initQ, instrs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [clobbers, dstOf, Ne.symm h9]

theorem initQ_keepsV (iv : HashValue) :
    (initQ iv).allInstrs VG.AArch64.keepsV = true := by
  rw [Code.allInstrs_eq]
  simp [initQ, instrs, VG.AArch64.keepsV, vdstOf]

end VG.Proof.Sha256.AArch64.Stream
