module

public import VerifiedGarbage.Proof.X448.Contract
public import VerifiedGarbage.Proof.Xdh.PPC64LE
public import VerifiedGarbage.Proof.X448.PPC64LE.Verified
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Xdh.PPC64LE
meta import VerifiedGarbage.Proof.X448.PPC64LE.Verified
meta import VerifiedGarbage.Spec.X448.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.X448.Contract

/-!
# X448 exchange, with RFC 7748's check, on PPC64LE

Untrusted: everything here is checked by Lean. `vg_x448` is a callee of
`Impl.Xdh.PPC64LE.exchange` (`callee`) by its shared contract, so
`vg_x448_exchange`, which calls it and checks its result
(`Proof/Xdh/PPC64LE.lean`), is `Verified` against its shared contract, with
the 48 bytes of stack its frame uses (`exchange_verified`).
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE.Exchange

open VG VG.PPC64LE VG.Proof.Xdh.PPC64LE

theorem callee : Callee 56 8192 Spec.X448.x448 Impl.X448.PPC64LE.x448
    (Proof.X448.x448Contract PPC64LE.abi) where
  hv := Proof.X448.PPC64LE.x448_verified.1
  hct := Proof.X448.PPC64LE.x448_verified.2.1
  pre s h := by
    obtain ⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3⟩ := h
    sig_pre [Proof.X448.x448Contract, Proof.X448.x448Sig, PPC64LE.abi, PPC64LE.argRegs]
    sig_reduce [Proof.X448.x448Contract, Proof.X448.x448Sig, PPC64LE.abi, PPC64LE.argRegs, List.getD]
    sig_and_intros
    all_goals first
      | with_reducible assumption
      | trivial
      | omega
      | exact Region.Disjoint.symm ‹_›
  post s s' h := by
    sig_post [Proof.X448.x448Contract, Proof.X448.x448Sig, PPC64LE.abi, PPC64LE.argRegs] at h
    exact h
  pub s₁ s₂ h := by
    obtain ⟨q0, q1, q2, q3, qsp⟩ := h
    sig_pub [Proof.X448.x448Contract, Proof.X448.x448Sig, PPC64LE.abi, PPC64LE.argRegs]
    sig_reduce [Proof.X448.x448Contract, Proof.X448.x448Sig, PPC64LE.abi, PPC64LE.argRegs]
    sig_and_intros
    all_goals first | with_reducible assumption | trivial
  nf := by lit_decide

theorem exchange_verified :
    Verified PPC64LE.target (Impl.Xdh.PPC64LE.exchange "vg_x448" Impl.X448.PPC64LE.x448 56)
      (Spec.X448.exchangeContract PPC64LE.abi 48) :=
  Verified.of_correct (k := exContract 56 8192 Spec.X448.x448) (exchange_correct callee (by decide))
    (exchange_ct callee ⟨_, by taint_decide⟩) (by
      contract_implies [Spec.X448.exchangeContract, Spec.X448.exchangeSig, Proof.X448.x448Sig,
        exContract, ExPre, CallPre, ExPost, Pub, PPC64LE.abi, PPC64LE.argRegs]
        [Proof.X448.PPC64LE.x448Sat] using Proof.X448.PPC64LE.x448Sat)

end VG.Proof.X448.PPC64LE.Exchange
