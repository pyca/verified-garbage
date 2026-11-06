module

public import VerifiedGarbage.Proof.Xdh.RISCV64
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Verified
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Xdh.RISCV64
meta import VerifiedGarbage.Proof.X448.RISCV64.R64.Verified
meta import VerifiedGarbage.Spec.X448.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.PowLit

/-!
# X448 exchange, with RFC 7748's check, on RISC-V

Untrusted: everything here is checked by Lean. `vg_x448` is a callee of
`Impl.Xdh.RISCV64.exchange` (`callee`) by its shared contract, so
`vg_x448_exchange`, which calls it and checks its result
(`Proof/Xdh/RISCV64.lean`), is `Verified` against its shared contract, with
the 16 bytes of stack its frame uses (`exchange_verified`).
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64.Exchange

open VG VG.RISCV64 VG.Proof.Xdh.RISCV64

theorem callee : Callee 56 8192 Spec.X448.x448 Impl.X448.RISCV64.R64.x448
    (Spec.X448.x448Contract RISCV64.abi) where
  hv := Proof.X448.RISCV64.R64.x448_verified.1
  hct := Proof.X448.RISCV64.R64.x448_verified.2.1
  pre s h := by
    obtain ⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3, al3, al⟩ := h
    sig_pre [Spec.X448.x448Contract, Spec.X448.x448Sig, RISCV64.abi, RISCV64.argRegs]
    sig_reduce [Spec.X448.x448Contract, Spec.X448.x448Sig, RISCV64.abi, RISCV64.argRegs, List.getD]
    sig_and_intros
    all_goals first
      | with_reducible assumption
      | trivial
      | omega
      | exact Region.Disjoint.symm ‹_›
  post s s' h := by
    sig_post [Spec.X448.x448Contract, Spec.X448.x448Sig, RISCV64.abi, RISCV64.argRegs] at h
    exact h
  pub s₁ s₂ h := by
    obtain ⟨q0, q1, q2, q3, qsp⟩ := h
    sig_pub [Spec.X448.x448Contract, Spec.X448.x448Sig, RISCV64.abi, RISCV64.argRegs]
    sig_reduce [Spec.X448.x448Contract, Spec.X448.x448Sig, RISCV64.abi, RISCV64.argRegs]
    sig_and_intros
    all_goals first | with_reducible assumption | trivial
  nf := by lit_decide

theorem exchange_verified :
    Verified RISCV64.target (Impl.Xdh.RISCV64.exchange "vg_x448" Impl.X448.RISCV64.R64.x448 56)
      (Spec.X448.exchangeContract RISCV64.abi 16) :=
  Verified.of_correct (k := exContract 56 8192 Spec.X448.x448) (exchange_correct callee (by decide))
    (exchange_ct callee ⟨_, by taint_decide⟩) (by
      contract_implies [Spec.X448.exchangeContract, Spec.X448.exchangeSig, Spec.X448.x448Sig,
        exContract, ExPre, CallPre, ExPost, Pub, RISCV64.abi, RISCV64.argRegs]
        [Proof.X448.RISCV64.R64.x448Sat] using Proof.X448.RISCV64.R64.x448Sat)

end VG.Proof.X448.RISCV64.Exchange
