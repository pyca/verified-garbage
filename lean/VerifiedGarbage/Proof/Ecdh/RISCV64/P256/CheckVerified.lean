module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.Check
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.CheckLit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.Check
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.CheckLit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_p256_check_point` on RISC-V: `Verified`

`check_rv` with the function's constant time, by taint tracking (only the
pointer, in `a0`, public: every address is `s0` plus a constant, and the only
branches are the field functions', on their pointers), and a state
satisfying the precondition (`satState`: `p`, `R² mod p`, `a R mod p` and
`b R mod p` at their slots, the flag zero).
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.P256

open VG VG.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdsa.RISCV64 VG.Proof.Ecdsa.RISCV64.P256

theorem check_ct : ConstantTime isa checkRVc.pre checkRVc.pub checkP256 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0])
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.2⟩) (by taint_decide)

/-- Byte `a` of the number `x` at slot `i` of a working space at `0x1000`. -/
def satByte (a : Addr) (i x : Nat) : Option (BitVec 8) :=
  if 0x1000 + p256.sl i ≤ a.toNat ∧ a.toNat < 0x1000 + p256.sl i + 32 then
    some (BitVec.ofNat 8 (x >>> (8 * (a.toNat - (0x1000 + p256.sl i)))))
  else none

/-- The memory of `satState`. -/
def satMem : Mem := fun a =>
  ((satByte a MP W.p).orElse fun _ => (satByte a R2P (2 ^ 256 * 2 ^ 256 % W.p)).orElse fun _ =>
    (satByte a AP (W.a * 2 ^ 256 % W.p)).orElse fun _ => satByte a BP (W.b * 2 ^ 256 % W.p)).getD 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | _ => 0
  sp := 0x10000
  mem := satMem
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem sat_check : CC.pre 0x1000 satMem := by
  unfold Impl.Weierstrass.CheckPoint.Curve.pre
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, .inl (by decide +kernel)⟩

theorem check_verified : Verified RISCV64.target checkP256 (CC.checkContract RISCV64.abi) :=
  Verified.of_correct check_rv check_ct
    { pre := by sig_implies_pre [Impl.Weierstrass.CheckPoint.Curve.checkContract, Impl.Weierstrass.CheckPoint.sig,
        checkRVc, RISCV64.abi, RISCV64.argRegs]
      post := by sig_implies_post [Impl.Weierstrass.CheckPoint.Curve.checkContract, Impl.Weierstrass.CheckPoint.sig,
        checkRVc, RISCV64.abi, RISCV64.argRegs]
      pub := by sig_implies_pub [Impl.Weierstrass.CheckPoint.Curve.checkContract, Impl.Weierstrass.CheckPoint.sig,
        checkRVc, RISCV64.abi, RISCV64.argRegs]
      sat := ⟨satState, Sig.contract_pre_of_check (by decide +kernel) (by
        sig_reduce [Sig.wfPre, Impl.Weierstrass.CheckPoint.sig, RISCV64.abi, RISCV64.argRegs, satState]
        exact ⟨by decide, sat_check⟩)⟩ }

end VG.Proof.Ecdh.RISCV64.P256
