module

public import VerifiedGarbage.Proof.X448.Contract
public import VerifiedGarbage.Proof.Xdh.AArch64
public import VerifiedGarbage.Proof.X448.AArch64.Fast.Verified
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Xdh.AArch64
meta import VerifiedGarbage.Proof.X448.AArch64.Fast.Verified
meta import VerifiedGarbage.Spec.X448.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.X448.Contract

/-!
# X448 exchange, with RFC 7748's check, on AArch64

Untrusted: everything here is checked by Lean. `vg_x448` is a callee of
`Impl.Xdh.AArch64.exchange` (`callee`) by its shared contract, so
`vg_x448_exchange`, which calls it and checks its result
(`Proof/Xdh/AArch64.lean`), is `Verified` against its shared contract, with
the 16 bytes of stack its frame uses (`exchange_verified`).
-/

@[expose] public section

namespace VG.Proof.X448.AArch64.Exchange

open VG VG.AArch64 VG.Proof.Xdh.AArch64

theorem callee : Callee 56 8192 Spec.X448.x448 Impl.X448.AArch64.Fast.x448
    (Proof.X448.x448Contract AArch64.abi) where
  hv := Proof.X448.AArch64.Fast.x448_verified.1
  hct := Proof.X448.AArch64.Fast.x448_verified.2.1
  pre s h := by
    obtain ⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3⟩ := h
    sig_pre [Proof.X448.x448Contract, Proof.X448.x448Sig, AArch64.abi, AArch64.argRegs]
    sig_reduce [Proof.X448.x448Contract, Proof.X448.x448Sig, AArch64.abi, AArch64.argRegs, List.getD]
    sig_and_intros
    all_goals first
      | with_reducible assumption
      | trivial
      | omega
      | exact Region.Disjoint.symm ‹_›
  post s s' h := by
    sig_post [Proof.X448.x448Contract, Proof.X448.x448Sig, AArch64.abi, AArch64.argRegs] at h
    exact h
  pub s₁ s₂ h := by
    obtain ⟨q0, q1, q2, q3, qsp⟩ := h
    sig_pub [Proof.X448.x448Contract, Proof.X448.x448Sig, AArch64.abi, AArch64.argRegs]
    sig_reduce [Proof.X448.x448Contract, Proof.X448.x448Sig, AArch64.abi, AArch64.argRegs]
    sig_and_intros
    all_goals first | with_reducible assumption | trivial
  nf := by lit_decide

theorem exchange_verified :
    Verified AArch64.target (Impl.Xdh.AArch64.exchange "vg_x448" Impl.X448.AArch64.Fast.x448 56)
      (Spec.X448.exchangeContract AArch64.abi 16) :=
  Verified.of_correct (k := exContract 56 8192 Spec.X448.x448) (exchange_correct callee (by decide))
    (exchange_ct callee ⟨_, by taint_decide⟩) (by
      contract_implies [Spec.X448.exchangeContract, Spec.X448.exchangeSig, Proof.X448.x448Sig,
        exContract, ExPre, CallPre, ExPost, Pub, AArch64.abi, AArch64.argRegs]
        [Proof.X448.AArch64.Fast.satState] using Proof.X448.AArch64.Fast.satState)

end VG.Proof.X448.AArch64.Exchange
