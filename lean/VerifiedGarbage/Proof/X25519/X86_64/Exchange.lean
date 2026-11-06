module

public import VerifiedGarbage.Proof.Xdh.X86_64
public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Verified
public import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.X25519.X86_64.Adx.Verified
public import VerifiedGarbage.Proof.X25519.X86_64.Verified
import VerifiedGarbage.Proof.X25519.X86_64.Lit
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Lit
meta import VerifiedGarbage.Proof.Xdh.X86_64
meta import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Verified
meta import VerifiedGarbage.Spec.X25519.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.Verified
meta import VerifiedGarbage.Proof.X25519.X86_64.Verified
meta import VerifiedGarbage.Proof.X25519.X86_64.Lit
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
meta import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Lit

/-!
# X25519 exchange, with RFC 7748's check, on x86-64

Untrusted: everything here is checked by Lean. Each implementation of
`vg_x25519` is a callee of `Impl.Xdh.X86_64.exchange` by its shared contract
(`callee`), so `vg_x25519_exchange`, which calls it and checks its result
(`Proof/Xdh/X86_64.lean`), is `Verified` against its shared contract, with
the 24 bytes of stack its frame, its call and its callee's calls use
(`exchange_verified`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Exchange

open VG VG.X86_64 VG.Proof.Xdh.X86_64

theorem callee {c : Prog isa} (hv : Verified X86_64.target c (Spec.X25519.x25519Contract X86_64.abi 8))
    (hn : NoSp c) (hd : c.depth ≤ 1) : Callee 32 4096 Spec.X25519.x25519 c (Spec.X25519.x25519Contract X86_64.abi 8) where
  hv := hv.1
  hct := hv.2.1
  pre s h := by
    obtain ⟨rd, wr, d1, d2, d3, d4, d5, r1, r2, r3, r4, k1, k2, k3, k4, b0, b1, b2, b3, stk⟩ := h
    sig_pre [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, X86_64.abi, X86_64.argRegs]
    sig_reduce [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, X86_64.abi, X86_64.argRegs, stackBelow, List.getD]
    sig_and_intros
    all_goals first
      | with_reducible assumption
      | trivial
      | omega
      | exact Region.Disjoint.symm ‹_›
  post s s' h := by
    sig_post [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, X86_64.abi, X86_64.argRegs] at h
    exact h
  pub s₁ s₂ h := by
    obtain ⟨qsp, q0, q1, q2, q3⟩ := h
    sig_pub [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, X86_64.abi, X86_64.argRegs]
    sig_reduce [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, X86_64.abi, X86_64.argRegs]
    sig_and_intros
    all_goals first | with_reducible assumption | trivial
  noSp := hn
  depth := hd

/-- `vg_x25519_exchange` calling `c`, an implementation of `vg_x25519`, as `name`. -/
theorem exchange_verified {c : Prog isa} (name : String)
    (hv : Verified X86_64.target c (Spec.X25519.x25519Contract X86_64.abi 8)) (hn : NoSp c) (hd : c.depth ≤ 1) :
    Verified X86_64.target (Impl.Xdh.X86_64.exchange name c 32) (Spec.X25519.exchangeContract X86_64.abi 24) :=
  Verified.of_correct (k := exContract 32 4096 Spec.X25519.x25519) (exchange_correct (callee hv hn hd) (by decide))
    (exchange_ct (callee hv hn hd) ⟨_, by taint_decide⟩) (by
      contract_implies [Spec.X25519.exchangeContract, Spec.X25519.exchangeSig, Spec.X25519.x25519Sig,
        Proof.Xdh.X86_64.exContract, Proof.Xdh.X86_64.Pre, Proof.Xdh.X86_64.ExPost, Proof.Xdh.X86_64.Pub,
        Proof.Xdh.X86_64.outR, Proof.Xdh.X86_64.scR, Proof.Xdh.X86_64.ptR, Proof.Xdh.X86_64.wsR,
        Proof.Xdh.X86_64.retR, Proof.Xdh.X86_64.stkR, X86_64.abi, X86_64.argRegs, stackBelow]
        [Proof.X25519.X86_64.satState] using Proof.X25519.X86_64.satState)

section
variable [VG.Proof.X25519.X86_64.DivstepInv]

theorem exchange_baseline :
    Verified X86_64.target (Impl.Xdh.X86_64.exchange "vg_x25519" Impl.X25519.X86_64.x25519 32)
      (Spec.X25519.exchangeContract X86_64.abi 24) :=
  exchange_verified _ Proof.X25519.X86_64.x25519_verified
    (NoSp.of_inlineOk Proof.X25519.X86_64.x25519_inlineOk) (by lit_decide)

theorem exchange_adx :
    Verified X86_64.target (Impl.Xdh.X86_64.exchange "vg_x25519_adx" Impl.X25519.X86_64.x25519Adx 32)
      (Spec.X25519.exchangeContract X86_64.abi 24) :=
  exchange_verified _ Proof.X25519.X86_64.x25519Adx_verified
    (NoSp.of_inlineOk Proof.X25519.X86_64.x25519Adx_inlineOk) (by lit_decide)

theorem exchange_ifma :
    Verified X86_64.target (Impl.Xdh.X86_64.exchange "vg_x25519_ifma" Impl.X25519.X86_64.x25519Ifma 32)
      (Spec.X25519.exchangeContract X86_64.abi 24) :=
  exchange_verified _ Proof.X25519.X86_64.x25519Ifma_verified
    (NoSp.of_inlineOk Proof.X25519.X86_64.x25519Ifma_inlineOk) (by lit_decide)

end

end VG.Proof.X25519.X86_64.Exchange
