module

public import VerifiedGarbage.Proof.Xdh.PPC64LE
public import VerifiedGarbage.Proof.X25519.PPC64LE.Verified
public import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Xdh.PPC64LE
meta import VerifiedGarbage.Proof.X25519.PPC64LE.Verified
meta import VerifiedGarbage.Spec.X25519.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.PowLit

/-!
# X25519 exchange, with RFC 7748's check, on PPC64LE

Untrusted: everything here is checked by Lean. `vg_x25519` is a callee of
`Impl.Xdh.PPC64LE.exchange` (`callee`) by its shared contract, so
`vg_x25519_exchange`, which calls it and checks its result
(`Proof/Xdh/PPC64LE.lean`), is `Verified` against its shared contract, with
the 48 bytes of stack its frame uses (`exchange_verified`).
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE.Exchange

open VG VG.PPC64LE VG.Proof.Xdh.PPC64LE

theorem callee : Callee 32 4096 Spec.X25519.x25519 Impl.X25519.PPC64LE.x25519
    (Spec.X25519.x25519Contract PPC64LE.abi) where
  hv := Proof.X25519.PPC64LE.x25519_verified.1
  hct := Proof.X25519.PPC64LE.x25519_verified.2.1
  pre s h := by
    obtain ⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3⟩ := h
    sig_pre [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, PPC64LE.abi, PPC64LE.argRegs]
    sig_reduce [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, PPC64LE.abi, PPC64LE.argRegs, List.getD]
    sig_and_intros
    all_goals first
      | with_reducible assumption
      | trivial
      | omega
      | exact Region.Disjoint.symm ‹_›
  post s s' h := by
    sig_post [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, PPC64LE.abi, PPC64LE.argRegs] at h
    exact h
  pub s₁ s₂ h := by
    obtain ⟨q0, q1, q2, q3, qsp⟩ := h
    sig_pub [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, PPC64LE.abi, PPC64LE.argRegs]
    sig_reduce [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, PPC64LE.abi, PPC64LE.argRegs]
    sig_and_intros
    all_goals first | with_reducible assumption | trivial
  nf := by lit_decide

theorem exchange_verified :
    Verified PPC64LE.target (Impl.Xdh.PPC64LE.exchange "vg_x25519" Impl.X25519.PPC64LE.x25519 32)
      (Spec.X25519.exchangeContract PPC64LE.abi 48) :=
  Verified.of_correct (k := exContract 32 4096 Spec.X25519.x25519) (exchange_correct callee (by decide))
    (exchange_ct callee ⟨_, by taint_decide⟩) (by
      contract_implies [Spec.X25519.exchangeContract, Spec.X25519.exchangeSig, Spec.X25519.x25519Sig,
        exContract, ExPre, CallPre, ExPost, Pub, PPC64LE.abi, PPC64LE.argRegs]
        [Proof.X25519.PPC64LE.x25519Sat] using Proof.X25519.PPC64LE.x25519Sat)

end VG.Proof.X25519.PPC64LE.Exchange
