module

import VerifiedGarbage.Proof.Dsa.X86.PublicKey
import VerifiedGarbage.Proof.Dsa.X86.VerifyArithmetic
public import VerifiedGarbage.Impl.Dsa.X86.SignVerify
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Dsa.X86.Persistent

/-! # Verification arithmetic and all post-shape acceptance conditions -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem verifyCompute_ok {base : Addr} {size pLen qLen p q g y digestLen digest rv sv : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (Y : CallerBuffer s0 base size (.input .y) pLen)
    (R : CallerBuffer s0 base size (.input .signature) qLen)
    (S : CallerBuffer s0 base size .signatureS qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hy : operandValue s0 base (.input .y) pLen = y)
    (hr : operandValue s0 base (.input .signature) qLen = rv)
    (hs : operandValue s0 base .signatureS qLen = sv)
    (hD : operandValue s0 base (.input .digest) digestLen = digest) :
    let computed := (g ^ (digest % q * (sv ^ (q - 2) % q) % q) % p *
      (y ^ (rv * (sv ^ (q - 2) % q) % q) % p) % p) % q
    WP isa (SignVerify.verifyCompute pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 &&&
        mask32 (publicChecks p q g y ∧ (0 < rv ∧ rv < q) ∧ (0 < sv ∧ sv < q) ∧ computed = rv) ∧
      Execution base s0 sf := by
  dsimp only
  have L := M.lengths
  have A := M.aligned
  have nq : (qLen + 7) / 8 ≤ 48 := by omega
  unfold SignVerify.verifyCompute Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (publicKey_ok M G Y hg hy) fun s1 ⟨M1, F1, Q1, E1⟩ => ?_)
  have R1 := E1.buffer R (by decide)
  refine WP.seq (WP.seq (WP.mono (stageRange_ok M1 (by omega) (by omega) (by omega)
    M1.qReady (R1.ready (M1.context nq)) false) fun s2 ⟨M2, F2, A2⟩ => ?_))
  have E2 := A2.execution (.inr ⟨rfl, rfl⟩)
  have E12 := E1.trans E2
  have S2 := E12.buffer S (by decide)
  refine WP.mono (stageRange_ok M2 (by omega) (by omega) (by omega) M2.qReady (S2.ready (M2.context nq)) false)
    fun s3 ⟨M3, F3, A3⟩ => ?_
  have E3 := A3.execution (.inr ⟨rfl, rfl⟩)
  have E123 := E12.trans E3
  have Q3 : operandValue s3 base (.local qMinusTwo) qLen = q - 2 := by
    rw [A3.scalar_keep_mask M2 (by decide), A2.scalar_keep_mask M1 (by decide), Q1]
  refine WP.seq (WP.mono (verifyArithmetic_ok M3 (E123.buffer G (by decide)) (E123.buffer Y (by decide))
    (E123.buffer R (by decide)) (E123.buffer S (by decide)) (E123.buffer D (by decide)) hd (E123.prefixLen.trans hP)
    ((E123.value G (by decide) M.extent).trans hg) ((E123.value Y (by decide) M.extent).trans hy)
    ((E123.value R (by decide) M.extent).trans hr) ((E123.value S (by decide) M.extent).trans hs)
    ((E123.value D (by decide) M.extent).trans hD) Q3) fun s4 ⟨M4, U4, E4, F4⟩ => ?_)
  have E1234 := E123.trans E4
  have R4 := E1234.buffer R (by decide)
  refine WP.seq (WP.mono (stageEqual_ok M4 (by omega) (by omega) (by omega) (M4.scalarReady (by decide) nq)
    (R4.ready (M4.context nq))) fun sf ⟨Mf, F5, A5⟩ => ?_)
  refine WP.block_nil ⟨Mf, ?_, E1234.trans (A5.execution (.inr ⟨rfl, rfl⟩))⟩
  rw [F5, F4, F3, F2, F1, U4, E1234.value R (by decide) M.extent,
    E12.value S (by decide) M.extent, E1.value R (by decide) M.extent, hr, hs, M1.qValue, M2.qValue]
  simp only [Bool.false_eq_true, ite_false, BitVec.and_assoc, mask32_and, and_assoc]

end VG.Proof.Dsa.X86
