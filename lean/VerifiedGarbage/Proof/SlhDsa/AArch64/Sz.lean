module

public import VerifiedGarbage.Spec.SlhDsa

/-!
# SLH-DSA on AArch64: the parameter sets the code is built for

The SHAKE parameter sets: `n` of 16, 24 or 32 bytes, `lg_w = 4` (so
`len = 2n + 3`). Every proof of the AArch64 code is for such a `p`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64

open VG.Spec.SlhDsa

/-- Sizes of the parameter sets. -/
structure Sz (p : Params) : Prop where
  nv : p.n = 16 ∨ p.n = 24 ∨ p.n = 32
  len : p.len = 2 * p.n + 3
  lgw : p.lgw = 4
  shake : p.family = .shake

variable {p : Params}

theorem Sz.n16 (h : Sz p) : 16 ≤ p.n := by rcases h.nv with e | e | e <;> rw [e] <;> decide
theorem Sz.n32 (h : Sz p) : p.n ≤ 32 := by rcases h.nv with e | e | e <;> rw [e] <;> decide
theorem Sz.n8 (h : Sz p) : p.n % 8 = 0 := by rcases h.nv with e | e | e <;> rw [e] <;> decide

end VG.Proof.SlhDsa.AArch64
