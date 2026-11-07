module

public import VerifiedGarbage.Proof.X25519.Contract
public import VerifiedGarbage.Proof.Xdh.RISCV64
public import VerifiedGarbage.Proof.X25519.RISCV64.R64.Verified
public import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Xdh.RISCV64
meta import VerifiedGarbage.Proof.X25519.RISCV64.R64.Verified
meta import VerifiedGarbage.Spec.X25519.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.X25519.Contract

/-!
# X25519 exchange, with RFC 7748's check, on RISC-V

Untrusted: everything here is checked by Lean. `vg_x25519` is a callee of
`Impl.Xdh.RISCV64.exchange` (`callee`) by its shared contract, so
`vg_x25519_exchange`, which calls it and checks its result
(`Proof/Xdh/RISCV64.lean`), is `Verified` against its shared contract, with
the 16 bytes of stack its frame uses (`exchange_verified`).
-/

@[expose] public section

namespace VG.Proof.X25519.RISCV64.Exchange

open VG VG.RISCV64 VG.Proof.Xdh.RISCV64

theorem callee : Callee 32 4096 Spec.X25519.x25519 Impl.X25519.RISCV64.R64.x25519
    (Proof.X25519.x25519Contract RISCV64.abi) where
  hv := Proof.X25519.RISCV64.R64.x25519_verified.1
  hct := Proof.X25519.RISCV64.R64.x25519_verified.2.1
  pre s h := by
    obtain ⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3, al3, al⟩ := h
    sig_pre [Proof.X25519.x25519Contract, Proof.X25519.x25519Sig, RISCV64.abi, RISCV64.argRegs]
    sig_reduce [Proof.X25519.x25519Contract, Proof.X25519.x25519Sig, RISCV64.abi, RISCV64.argRegs, List.getD]
    sig_and_intros
    all_goals first
      | with_reducible assumption
      | trivial
      | omega
      | exact Region.Disjoint.symm ‹_›
  post s s' h := by
    sig_post [Proof.X25519.x25519Contract, Proof.X25519.x25519Sig, RISCV64.abi, RISCV64.argRegs] at h
    exact h
  pub s₁ s₂ h := by
    obtain ⟨q0, q1, q2, q3, qsp⟩ := h
    sig_pub [Proof.X25519.x25519Contract, Proof.X25519.x25519Sig, RISCV64.abi, RISCV64.argRegs]
    sig_reduce [Proof.X25519.x25519Contract, Proof.X25519.x25519Sig, RISCV64.abi, RISCV64.argRegs]
    sig_and_intros
    all_goals first | with_reducible assumption | trivial
  nf := by lit_decide

theorem exchange_verified :
    Verified RISCV64.target (Impl.Xdh.RISCV64.exchange "vg_x25519" Impl.X25519.RISCV64.R64.x25519 32)
      (Spec.X25519.exchangeContract RISCV64.abi 16) :=
  Verified.of_correct (k := exContract 32 4096 Spec.X25519.x25519) (exchange_correct callee (by decide))
    (exchange_ct callee ⟨_, by taint_decide⟩) (by
      contract_implies [Spec.X25519.exchangeContract, Spec.X25519.exchangeSig, Proof.X25519.x25519Sig,
        exContract, ExPre, CallPre, ExPost, Pub, RISCV64.abi, RISCV64.argRegs]
        [Proof.X25519.RISCV64.R64.x25519Sat] using Proof.X25519.RISCV64.R64.x25519Sat)

end VG.Proof.X25519.RISCV64.Exchange
