module

public import VerifiedGarbage.Proof.X25519.Contract
public import VerifiedGarbage.Proof.Xdh.X86
public import VerifiedGarbage.Proof.X25519.X86.Verified
public import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.X25519.X86.Lit
meta import VerifiedGarbage.Proof.Xdh.X86
meta import VerifiedGarbage.Proof.X25519.X86.Verified
meta import VerifiedGarbage.Spec.X25519.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.X25519.X86.Lit
meta import VerifiedGarbage.Proof.X25519.Contract

/-!
# X25519 exchange, with RFC 7748's check, on x86

Untrusted: everything here is checked by Lean. `vg_x25519` is a callee of
`Impl.Xdh.X86.exchange` by the contract its proof is written against
(`Proof.X25519.x25519X86`, `callee`), so `vg_x25519_exchange`, which calls it and checks
its result (`Proof/Xdh/X86.lean`), is `Verified` against its shared
contract, with the 28 bytes of stack its frame, its call and its callee's
calls and frames use (`exchange_verified`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86.Exchange

open VG VG.X86 VG.Proof.Xdh.X86

theorem callee : Callee 32 4096 8 Spec.X25519.x25519 Impl.X25519.X86.x25519 Proof.X25519.x25519X86 where
  hv := Proof.X25519.X86.x25519_ok
  hct := Proof.X25519.X86.x25519_ct
  pre s h := by
    obtain ⟨rd, wr, d1, d2, d3, d4, d5, d6, d7, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5, b0, b1, b2, b3, stk,
      top⟩ := h
    exact ⟨rd, wr, d3, d5, d6, d4.symm, d7.symm, r1, r4, b0, b1, b2, b3, top, k1, k4, k5, stk⟩
  post _ _ h := h
  pub _ _ h := h
  noSp := NoSp.of_all (by lit_decide)
  depth := by lit_decide

theorem exchange_verified :
    Verified X86.target (Impl.Xdh.X86.exchange "vg_x25519" Impl.X25519.X86.x25519 32)
      (Spec.X25519.exchangeContract X86.abi 28) :=
  Verified.of_correct (k := exContract 32 4096 8 Spec.X25519.x25519) (exchange_correct callee)
    (exchange_ct callee ⟨_, by taint_decide⟩) (by
      have a0 : arg Proof.X25519.X86.satState 0 = 0x1000 := by decide
      have a1 : arg Proof.X25519.X86.satState 1 = 0x2000 := by decide
      have a2 : arg Proof.X25519.X86.satState 2 = 0x3000 := by decide
      have a3 : arg Proof.X25519.X86.satState 3 = 0x4000 := by decide
      have e : argAddr Proof.X25519.X86.satState 0 = 0x8004 := by decide
      have esp : Proof.X25519.X86.satState.gpr .esp = 0x8000 := rfl
      contract_implies [Spec.X25519.exchangeContract, Spec.X25519.exchangeSig, Proof.X25519.x25519Sig, Proof.Xdh.X86.exContract,
        Proof.Xdh.X86.Pre, Proof.Xdh.X86.ExPost, Proof.Xdh.X86.Pub, Proof.Xdh.X86.outR, Proof.Xdh.X86.scR, Proof.Xdh.X86.ptR, Proof.Xdh.X86.wsR,
        Proof.Xdh.X86.argR, Proof.Xdh.X86.retR, Proof.Xdh.X86.stkR, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes, stackBelow] [a0, a1, a2, a3, e, esp] using Proof.X25519.X86.satState)

end VG.Proof.X25519.X86.Exchange
