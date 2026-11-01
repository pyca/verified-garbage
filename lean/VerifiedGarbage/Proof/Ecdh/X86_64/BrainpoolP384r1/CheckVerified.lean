module

public import VerifiedGarbage.Proof.Ecdh.X86_64.CheckFn
public import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP384r1.InverseVerified
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP384r1.InverseLit
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.TaintMap
import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP384r1Literals
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
meta import VerifiedGarbage.Proof.Ecdh.X86_64.CheckFn
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP384r1.InverseVerified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP384r1.InverseLit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.TaintMap
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.BrainpoolP384r1Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb

/-!
# `vg_brainpoolp384r1_check_point` on x86-64: `Verified`

`CheckFn.correct` for brainpoolP384r1's configurations (`Inverse.cfg`), whose slots
are the curve's (`agree`); constant time by taint tracking, `rdi` and `rsp`
public, on the code's literals.
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86_64.BrainpoolP384r1.Check

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64 VG.Proof.Ecdh.X86_64.CheckFn
open VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64.BrainpoolP384r1.Inverse (cfg cfg_ok)

abbrev C : CP := Impl.Weierstrass.CheckPoint.brainpoolp384r1

/-- `vg_brainpoolp384r1_check_point`. -/
abbrev code : Prog isa := Cfg.invFnX (Impl.Ecdh.X86_64.Cfg.checkBody cfg)

theorem agree : Agree cfg C := ⟨rfl, rfl, by decide +kernel, keeps_of_covers (by decide +kernel), by decide +kernel⟩

theorem hvm : (Impl.Ecdh.X86_64.Cfg.checkBody cfg).allInstrs
    (fun i => !KeepReg.writesVec i && !loadsMxcsr i) = true := by
  lit_decide

theorem hv : (Impl.Ecdh.X86_64.Cfg.checkBody cfg).allInstrs (fun i => !KeepReg.writesVec i) = true :=
  (hv_hmx hvm).1

theorem hn : (Impl.Ecdh.X86_64.Cfg.checkBody cfg).noCalls = true := by
  lit_decide

theorem hmx : code.allInstrs (fun i => !loadsMxcsr i) = true :=
  (hv_hmx hvm).2

theorem ct : ConstantTime isa (checkK C).pre (checkK C).pub code :=
  VG.Taint.constantTime (A := X86_64.taint) (Taint.ofRegs [.rdi, .rsp]) (agreeK C) (by taint_decide)

theorem sat : C.pre 0x1000 (satMem C) := by
  unfold Impl.Weierstrass.CheckPoint.Curve.pre; decide +kernel

theorem verified (hI : InvSounds) : Verified X86_64.target code (C.checkContract X86_64.abi) :=
  Verified.of_correct (correct (cfg_ok hI) agree hv hn hmx) ct (implies C sat)

end VG.Proof.Ecdh.X86_64.BrainpoolP384r1.Check
