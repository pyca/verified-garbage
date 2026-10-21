module

import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Matrix
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Prefix
import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Tail
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenPrefix
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.KgCommon
public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Inv

/-! # The key generation hashing `ek` during the matrix is correct

`using_correctP`: `G` (`a_using_ok`), the first two pairs of the matrix
computing the first PRF outputs (`first_step`), the noise, `ŝ` and the
all-zero third state (`pre_ok`), the rest of the matrix with the rows of `t̂`
between its pairs (`matrixRows_ok`), and the tail (`tail_ok`). -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.Hybrid (TStk)

variable {P : KemLay}

theorem matrixRows_ne_nil (P : KemLay) (hk3 : 3 ≤ P.k) : Impl.MlKem.AArch64.Kem16P.kgMatrixRows P ≠ [] := by
  intro h
  unfold Impl.MlKem.AArch64.Kem16P.kgMatrixRows Impl.MlKem.AArch64.Kem16P.pairs at h
  have h2 := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).2
  have hp : 0 < P.k * P.k / 2 - 2 := by
    have := Nat.mul_le_mul hk3 hk3
    omega
  exact List.cons_ne_nil _ _ (List.flatMap_eq_nil_iff.mp h2 0 (List.mem_range.mpr hp))

/-- **The key generation computing the first PRF outputs in the matrix is correct.** -/
theorem using_correctP (v : Proof.Sha3.AArch64.Permutation) (hash : FixedHash.HashFn)
    (hG : FixedHash.HashCorrect hash .x28 ST WK 72 6
      [⟨.x25,0,32⟩,⟨.x28,BK,1⟩] [⟨.x28,SB,32⟩,⟨.x28,SG,32⟩])
    {s₀ : State} (hp : Pre P s₀) (hk : Stk128K P s₀) (hr : Noise.Room P) (hk3 : 3 ≤ P.k) (tables : Tables s₀)
    (ts : TStk s₀) (depthA : (FixedHashCallers.kgAUsing hash P).aarch64Depth ≤ 1)
    (depthP : (Impl.MlKem.AArch64.Kem16P.kgPre P).aarch64Depth ≤ 1) :
    WP isa (Impl.MlKem.AArch64.Kem16P.keyGen hash v.callee P) s₀ fun t =>
      abiPreserved s₀ t ∧ (keyGenAArch64 P).post s₀ t := by
  unfold Impl.MlKem.AArch64.Kem16P.keyGen
  refine WPs.seqs (by simp) ?_
  refine WPs.cons (WP.mono_syms (WP.tablesDepth (a_using_ok hash hG hp) tables depthA) fun sA ⟨hA, ta⟩ hs => ?_)
  refine WPs.cons (WP.mono (first_step hp hk (p := 0) (by decide) hk3
    (FInv.zero hA ta (ts.of hs hA.kb.sp))) fun s₁ h₁ => ?_)
  refine WPs.cons (WP.mono (first_step hp hk (p := 1) (by decide) hk3 h₁) fun s₂ h₂ => ?_)
  refine WPs.cons (WP.mono (pre_ok hp hr hk3 h₂ depthP) fun s₃ h₃ => ?_)
  refine WPs.cons (WP.mono (WPs.seqs (matrixRows_ne_nil P hk3) (matrixRows_ok hp hk hr hk3 h₃))
    fun s₄ h₄ => ?_)
  exact WPs.single (WP.mono (tail_ok v hp h₄) fun t ht => ⟨ht.abi, post_ofW h₄.b ht⟩)

end VG.Proof.MlKem.AArch64.KeyGen
