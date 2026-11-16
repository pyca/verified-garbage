module

public import VerifiedGarbage.Proof.MlKem.X86_64.FragKpke
public import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem
import VerifiedGarbage.Proof.MlKem1024.X86_64.KpkeKgV
import VerifiedGarbage.Proof.MlKem1024.X86_64.KpkeEncV
import VerifiedGarbage.Proof.MlKem1024.X86_64.KpkeDecV
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA16
public import VerifiedGarbage.Proof.Framework.X86_64.InstrBits

/-! # ML-KEM-1024 on x86-64: the K-PKE functions, safe to call -/

@[expose] public section

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem.X86_64

/-- `CalleeOk` from its proofs and the checks of every instruction, which
the kernel evaluates at once, building the code once. -/
theorem calleeOk_of {k : Contract isa} {c : Prog isa}
    (ok : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c)
    (h : (c.allInstrs (fun i => !Taint.clobbers i .rsp) && c.depth == 0 && ctlOk c &&
      c.allInstrs (fun i => !isa.writesSp i)) = true) : CalleeOk k c := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨ok, ct, nosp_of h.1.1.1, h.1.1.2, h.1.2, Code.all_of_allInstrs h.2⟩

/-- `calleeOk_of`, from the tests of every instruction in one walk of the
code, with one match for each instruction
(`Proof/Framework/X86_64/InstrBits.lean`). -/
theorem calleeOk_of_bits {k : Contract isa} {c : Prog isa}
    (ok : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c)
    (h : (c.allInstrs (hasBits (bSp + bNs)) && c.depth == 0 && ctlOk c) = true) : CalleeOk k c := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨ok, ct, nosp_of (Code.noRsp_of_bits (m := bSp + bNs) rfl h.1.1), h.1.2, h.2,
    Code.spSafe_of_bits (m := bSp + bNs) rfl h.1.1⟩

/-- The three functions' checks, in one declaration: the kernel evaluates the
code they share once. -/
theorem kpke1024_checks :
    ((kpkeKg kem1024 .avx2 keygenMul16Y).allInstrs (hasBits (bSp + bNs)) && (kpkeKg kem1024 .avx2 keygenMul16Y).depth == 0 && ctlOk (kpkeKg kem1024 .avx2 keygenMul16Y)) = true ∧
    ((kpkeEnc kem1024 .avx2 encryptMul16Y).allInstrs (hasBits (bSp + bNs)) && (kpkeEnc kem1024 .avx2 encryptMul16Y).depth == 0 && ctlOk (kpkeEnc kem1024 .avx2 encryptMul16Y)) = true ∧
    ((kpkeDec kem1024 .avx2 Kpke16.dmInnerY).allInstrs (hasBits (bSp + bNs)) && (kpkeDec kem1024 .avx2 Kpke16.dmInnerY).depth == 0 && ctlOk (kpkeDec kem1024 .avx2 Kpke16.dmInnerY)) = true := by
  lit_decide

theorem KpkeOk.k1024 : KpkeOk kem1024 where
  kg := calleeOk_of_bits kpkeKg1024Y_correct kpkeKg1024Y_ct kpke1024_checks.1
  enc := calleeOk_of_bits kpkeEnc1024Y_correct kpkeEnc1024Y_ct kpke1024_checks.2.1
  dec := calleeOk_of_bits kpkeDec1024Y_correct kpkeDec1024Y_ct kpke1024_checks.2.2

end VG.Proof.MlKem1024.X86_64
