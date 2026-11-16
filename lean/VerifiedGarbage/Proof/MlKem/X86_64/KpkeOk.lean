module

public import VerifiedGarbage.Proof.MlKem.X86_64.FragKpke
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeKgV
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEncV
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDecV
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA16
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
public import VerifiedGarbage.Proof.Framework.X86_64.InstrBits

/-! # ML-KEM on x86-64: the K-PKE functions of ML-KEM-768, safe to call -/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-- `CalleeOk` from its proofs and the checks of every instruction, which
the kernel evaluates in one walk of the code, with one match for each
instruction (`Proof/Framework/X86_64/InstrBits.lean`). -/
theorem calleeOk_of {k : Contract isa} {c : Prog isa}
    (ok : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c)
    (h : (c.allInstrs (hasBits (bSp + bNs)) && c.depth == 0 && ctlOk c) = true) : CalleeOk k c := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨ok, ct, nosp_of (Code.noRsp_of_bits (m := bSp + bNs) rfl h.1.1), h.1.2, h.2,
    Code.spSafe_of_bits (m := bSp + bNs) rfl h.1.1⟩

/-- The three functions' checks, in one declaration: the kernel evaluates the
code they share once. -/
theorem kpke768_checks :
    ((kpkeKg kem768 .avx2 keygenMul16Y).allInstrs (hasBits (bSp + bNs)) &&
      (kpkeKg kem768 .avx2 keygenMul16Y).depth == 0 && ctlOk (kpkeKg kem768 .avx2 keygenMul16Y)) = true ∧
    ((kpkeEnc kem768 .avx2 encryptMul16Y).allInstrs (hasBits (bSp + bNs)) &&
      (kpkeEnc kem768 .avx2 encryptMul16Y).depth == 0 && ctlOk (kpkeEnc kem768 .avx2 encryptMul16Y)) = true ∧
    ((kpkeDec kem768 .avx2 Kpke16.dmInnerY).allInstrs (hasBits (bSp + bNs)) &&
      (kpkeDec kem768 .avx2 Kpke16.dmInnerY).depth == 0 && ctlOk (kpkeDec kem768 .avx2 Kpke16.dmInnerY)) = true := by
  lit_decide

theorem KpkeOk.k768 : KpkeOk kem768 where
  kg := calleeOk_of kpkeKg768Y_correct kpkeKg768Y_ct kpke768_checks.1
  enc := calleeOk_of kpkeEnc768Y_correct kpkeEnc768Y_ct kpke768_checks.2.1
  dec := calleeOk_of kpkeDec768Y_correct kpkeDec768Y_ct kpke768_checks.2.2

end VG.Proof.MlKem.X86_64
