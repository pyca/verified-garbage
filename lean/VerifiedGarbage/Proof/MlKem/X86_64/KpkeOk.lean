module

public import VerifiedGarbage.Proof.MlKem.X86_64.FragKpke
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeKgV
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEncV
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDecV
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA16
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit

/-! # ML-KEM on x86-64: the K-PKE functions of ML-KEM-768, safe to call -/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64

/-- `CalleeOk` from its proofs and the checks of every instruction, which
the kernel evaluates at once, building the code once. -/
theorem calleeOk_of {k : Contract isa} {c : Prog isa}
    (ok : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (ct : ConstantTime isa k.pre k.pub c)
    (h : (c.allInstrs (fun i => !Taint.clobbers i .rsp) && c.depth == 0 && ctlOk c &&
      c.allInstrs (fun i => !isa.writesSp i)) = true) : CalleeOk k c := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨ok, ct, nosp_of h.1.1.1, h.1.1.2, h.1.2, Code.all_of_allInstrs h.2⟩

theorem KpkeOk.k768 : KpkeOk kem768 where
  kg := calleeOk_of kpkeKg768Y_correct kpkeKg768Y_ct (by lit_decide)
  enc := calleeOk_of kpkeEnc768Y_correct kpkeEnc768Y_ct (by lit_decide)
  dec := calleeOk_of kpkeDec768Y_correct kpkeDec768Y_ct (by lit_decide)

end VG.Proof.MlKem.X86_64
