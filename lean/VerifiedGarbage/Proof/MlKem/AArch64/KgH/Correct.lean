module

public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Matrix
public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Prefix
public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Tail
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenPrefix
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! # The key generation hashing `ek` during the matrix is correct

`using_correctH`: `G` (`a_using_ok`), the noise, `ŝ` and the all-zero third
state (`pre_ok`), the matrix with the rows of `t̂` between its pairs
(`matrixRows_ok`), and the tail (`tail_ok`). -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.Hybrid (TStk)

variable {P : KemLay}

theorem matrixRows_ne_nil (P : KemLay) (hk : 1 ≤ P.k) : Kem16.kgMatrixRows P ≠ [] := by
  intro h
  rw [Kem16.kgMatrixRows] at h
  have h2 := (List.append_eq_nil_iff.mp h).2
  by_cases ho : P.k * P.k % 2 = 1
  · rw [ite_eq_left ho] at h2; exact List.cons_ne_nil _ _ h2
  · have hp : 0 < P.k * P.k / 2 := by
      have := Nat.mul_le_mul hk hk
      omega
    exact List.cons_ne_nil _ _ (List.flatMap_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1 0
      (List.mem_range.mpr hp))

/-- **The key generation hashing `ek` during the matrix is correct.** -/
theorem using_correctH (v : Proof.Sha3.AArch64.Permutation) (hash : FixedHash.HashFn)
    (hG : FixedHash.HashCorrect hash .x28 ST WK 72 6
      [⟨.x25,0,32⟩,⟨.x28,BK,1⟩] [⟨.x28,SB,32⟩,⟨.x28,SG,32⟩])
    {s₀ : State} (hp : Pre P s₀) (hk : Stk128K P s₀) (hr : Noise.Room P) (tables : Tables s₀)
    (ts : TStk s₀) (depthA : (FixedHashCallers.kgAUsing hash P).aarch64Depth ≤ 1)
    (depthP : (Kem16.kgPre P).aarch64Depth ≤ 1) :
    WP isa (Kem16.keyGenH hash v.callee P) s₀ fun t => abiPreserved s₀ t ∧ (keyGenAArch64 P).post s₀ t := by
  have hw := hp.wf
  unfold Kem16.keyGenH
  refine WPs.seqs (by simp) ?_
  refine WPs.cons (WP.mono_syms (WP.tablesDepth (a_using_ok hash hG hp) tables depthA) fun sA ⟨hA, ta⟩ hs => ?_)
  refine WPs.cons (WP.mono (pre_ok hp hr hA ta (ts.of hs hA.kb.sp) depthP) fun s₁ h₁ => ?_)
  refine WPs.cons (WP.mono (WPs.seqs (matrixRows_ne_nil P hw.facts.1) (matrixRows_ok hp hk hr h₁))
    fun s₂ h₂ => ?_)
  exact WPs.single (WP.mono (tail_ok v hp h₂) fun t ht => ⟨ht.abi, post_ofW h₂.b ht⟩)

end VG.Proof.MlKem.AArch64.KeyGen
