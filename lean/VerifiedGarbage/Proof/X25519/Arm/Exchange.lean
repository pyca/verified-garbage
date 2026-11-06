module

public import VerifiedGarbage.Proof.Xdh.Arm
public import VerifiedGarbage.Proof.X25519.Arm.Verified
public import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Xdh.Arm
meta import VerifiedGarbage.Proof.X25519.Arm.Verified
meta import VerifiedGarbage.Spec.X25519.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.PowLit

/-!
# X25519 exchange, with RFC 7748's check, on ARMv7

Untrusted: everything here is checked by Lean. Each implementation of
`vg_x25519` is a callee of `Impl.Xdh.Arm.exchange` by its shared contract
(`callee`), so `vg_x25519_exchange`, which calls it and checks its result
(`Proof/Xdh/Arm.lean`), is `Verified` against its shared contract, with the
8 bytes of stack its frames use.
-/

@[expose] public section

namespace VG.Proof.X25519.Arm.Exchange

open VG VG.Arm VG.Proof.Xdh.Arm

theorem callee {c : Prog isa} (hv : Verified Arm.target c (Spec.X25519.x25519Contract Arm.abi))
    (hn : c.noFrames = true) : Callee 32 4096 Spec.X25519.x25519 c (Spec.X25519.x25519Contract Arm.abi) where
  hv := hv.1
  hct := hv.2.1
  pre s h := by
    obtain ⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3⟩ := h
    sig_pre [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
    sig_reduce [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, List.getD]
    sig_and_intros
    all_goals first
      | with_reducible assumption
      | trivial
      | omega
      | exact Region.Disjoint.symm ‹_›
  post s s' h := by
    sig_post [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] at h
    exact h
  pub s₁ s₂ h := by
    obtain ⟨q0, q1, q2, q3, qsp⟩ := h
    sig_pub [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
    sig_reduce [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
    sig_and_intros
    all_goals first | with_reducible assumption | trivial
  nf := hn

/-- `vg_x25519_exchange` calling `c`, an implementation of `vg_x25519`, as `name`. -/
theorem exchange_verified {c : Prog isa} (name : String)
    (hv : Verified Arm.target c (Spec.X25519.x25519Contract Arm.abi)) (hn : c.noFrames = true)
    (ht : ∃ hc, (taint.check (Taint.ofRegs [.r1]) (.block (Impl.Xdh.Arm.check 32)) hc).isSome = true) :
    Verified Arm.target (Impl.Xdh.Arm.exchange name c 32) (Spec.X25519.exchangeContract Arm.abi 8) :=
  Verified.of_correct (k := exContract 32 4096 Spec.X25519.x25519) (exchange_correct (callee hv hn) (by decide))
    (exchange_ct (callee hv hn) ht) (by
      contract_implies [Spec.X25519.exchangeContract, Spec.X25519.exchangeSig, Spec.X25519.x25519Sig,
        exContract, ExPre, CallPre, ExPost, Pub, Proof.Xdh.Arm.outR, Proof.Xdh.Arm.scR, Proof.Xdh.Arm.ptR, Proof.Xdh.Arm.wsR,
        Proof.Xdh.Arm.frR, ret32, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val,
        Arm.State.addr] [Proof.X25519.Arm.x25519Sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.X25519.Arm.x25519Sat)

/-- The taint analysis of the check. -/
theorem check_taint : ∃ hc, (taint.check (Taint.ofRegs [.r1]) (.block (Impl.Xdh.Arm.check 32)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem exchange_baseline :
    Verified Arm.target (Impl.Xdh.Arm.exchange "vg_x25519" Impl.X25519.Arm.x25519 32)
      (Spec.X25519.exchangeContract Arm.abi 8) :=
  exchange_verified _ Proof.X25519.Arm.x25519_verified (by lit_decide) check_taint

theorem exchange_umaal :
    Verified Arm.target (Impl.Xdh.Arm.exchange "vg_x25519_umaal" Impl.X25519.Arm.x25519Umaal 32)
      (Spec.X25519.exchangeContract Arm.abi 8) :=
  exchange_verified _ Proof.X25519.Arm.x25519Umaal_verified (by lit_decide) check_taint

end VG.Proof.X25519.Arm.Exchange
