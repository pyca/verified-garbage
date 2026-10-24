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

theorem KpkeOk.k1024 : KpkeOk kem1024 where
  kg := calleeOk_of kpkeKg1024Y_correct kpkeKg1024Y_ct (by lit_decide)
  enc := calleeOk_of kpkeEnc1024Y_correct kpkeEnc1024Y_ct (by lit_decide)
  dec := calleeOk_of kpkeDec1024Y_correct kpkeDec1024Y_ct (by lit_decide)

end VG.Proof.MlKem1024.X86_64
