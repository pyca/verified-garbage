module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.MlKem.RISCV64.Top

/-!
# ML-KEM on RISC-V: what the proofs need of a parameter set

As on PPC64LE (`Proof/MlKem/PPC64LE/KemLay.lean`): the proofs of the
top-level functions hold for any parameter set `K : KemLay` that passes
`KemLay.wf`, a computation on the literals of `K`, which each parameter set
checks by `decide` (`kl768_wf`). The proofs use it as facts (`KemLay.WF`):
`1 ≤ k ≤ 4`, a `scratch` of at least 32 KiB, `η₁ = η₂ = 2`, and that the
buffers of decapsulation fit in `scratch`.
-/

@[expose] public section

namespace VG.Impl.MlKem.RISCV64

open VG VG.RISCV64

/-- What the proofs need of the parameters, as facts. -/
structure KemLay.WF (K : KemLay) : Prop where
  k1 : 1 ≤ K.k
  k4 : K.k ≤ 4
  scr : 32768 ≤ K.scratch
  η₁ : K.p.η₁ = 2
  η₂ : K.p.η₂ = 2
  du1 : 1 ≤ K.du
  du : K.du ≤ 11
  dv : K.dv ≤ 11
  ct : oPoly K.jCt + K.ctLen ≤ oCin
  cin : oCin + K.ctLen ≤ 32768

/-- `KemLay.WF` as a computation. -/
def KemLay.wf (K : KemLay) : Bool :=
  decide (1 ≤ K.k) && (decide (K.k ≤ 4) && (decide (32768 ≤ K.scratch) && (decide (K.p.η₁ = 2) &&
  (decide (K.p.η₂ = 2) && (decide (1 ≤ K.du) && (decide (K.du ≤ 11) && (decide (K.dv ≤ 11) &&
  (decide (oPoly K.jCt + K.ctLen ≤ oCin) && decide (oCin + K.ctLen ≤ 32768)))))))))

theorem KemLay.WF.of {K : KemLay} (h : K.wf = true) : K.WF := by
  simp only [KemLay.wf, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end VG.Impl.MlKem.RISCV64

namespace VG.Proof.MlKem.RISCV64

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64

theorem kl768_wf : kl768.WF := .of (by decide)

/-- The parameter set with `k` changed, for the facts about offsets that the
proofs decide for every `k ≤ 4`. -/
def kOf (k : Nat) : KemLay := { kl768 with p := { kl768.p with k := k } }

end VG.Proof.MlKem.RISCV64
