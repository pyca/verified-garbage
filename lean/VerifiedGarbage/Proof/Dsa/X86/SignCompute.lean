module

import VerifiedGarbage.Proof.Dsa.X86.PublicKey
import VerifiedGarbage.Proof.Dsa.X86.PrivateKey
import VerifiedGarbage.Proof.Dsa.X86.SignArithmetic
public import VerifiedGarbage.Impl.Dsa.X86.SignVerify
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Dsa.X86.Persistent

/-! # Signing arithmetic and all post-shape acceptance conditions -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem signCompute_ok {base : Addr} {size pLen qLen p q g y x k digestLen digest : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (Y : CallerBuffer s0 base size (.input .y) pLen)
    (X : CallerBuffer s0 base size (.input .x) qLen)
    (K : CallerBuffer s0 base size (.input .nonce) qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hy : operandValue s0 base (.input .y) pLen = y)
    (hx : operandValue s0 base (.input .x) qLen = x)
    (hk : operandValue s0 base (.input .nonce) qLen = k)
    (hD : operandValue s0 base (.input .digest) digestLen = digest) :
    let rv := g ^ k % p % q
    let sv := k ^ (q - 2) % q * ((digest % q + x * rv % q) % q) % q
    WP isa (SignVerify.signCompute pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      operandValue sf base (.local r) qLen = rv ∧
      operandValue sf base (.local VG.Impl.Dsa.Layout.s) qLen = sv ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 &&&
        mask32 (publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ (0 < k ∧ k < q) ∧
          g ^ x % p = y ∧ rv ≠ 0 ∧ sv ≠ 0) ∧ Execution base s0 sf := by
  dsimp only
  have L := M.lengths
  have A := M.aligned
  have nq : (qLen + 7) / 8 ≤ 48 := by omega
  unfold SignVerify.signCompute Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (publicKey_ok M G Y hg hy) fun s1 ⟨M1, F1, Q1, E1⟩ => ?_)
  refine WP.seq (WP.mono (privateKey_ok M1 (E1.buffer G (by decide)) (E1.buffer Y (by decide))
    (E1.buffer X (by decide)) (E1.buffer K (by decide))
    ((E1.value G (by decide) M.extent).trans hg) ((E1.value Y (by decide) M.extent).trans hy)
    ((E1.value X (by decide) M.extent).trans hx) ((E1.value K (by decide) M.extent).trans hk))
    fun s2 ⟨M2, F2, Q2, E2⟩ => ?_)
  have E12 := E1.trans E2
  refine WP.seq (WP.mono (signArithmetic_ok M2 (E12.buffer G (by decide)) (E12.buffer K (by decide))
    (E12.buffer X (by decide)) (E12.buffer D (by decide)) hd (E12.prefixLen.trans hP)
    ((E12.value G (by decide) M.extent).trans hg) ((E12.value K (by decide) M.extent).trans hk)
    ((E12.value X (by decide) M.extent).trans hx) ((E12.value D (by decide) M.extent).trans hD)
    (Q2.trans Q1)) fun s3 ⟨M3, R3, S3, E3, F3⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (stageZero_ok M3 (by omega) (by omega) (by omega)
    (M3.scalarReady (by decide) nq) true) fun s4 ⟨M4, F4, A4⟩ => ?_))
  have E4 := A4.execution (.inr ⟨rfl, rfl⟩)
  refine WP.mono (stageZero_ok M4 (by omega) (by omega) (by omega) (M4.scalarReady (by decide) nq) true)
    fun sf ⟨Mf, F5, A5⟩ => ?_
  refine WP.block_nil ⟨Mf, ?_, ?_, ?_, (((E12.trans E3).trans E4).trans (A5.execution (.inr ⟨rfl, rfl⟩)))⟩
  · rw [A5.scalar_keep_mask M4 (by decide), A4.scalar_keep_mask M3 (by decide), R3]
  · rw [A5.scalar_keep_mask M4 (by decide), A4.scalar_keep_mask M3 (by decide), S3]
  · rw [F5, F4, F3, F2, F1, A4.scalar_keep_mask M3 (by decide), R3, S3]
    simp only [ite_true, BitVec.and_assoc, mask32_and, and_assoc]

end VG.Proof.Dsa.X86
