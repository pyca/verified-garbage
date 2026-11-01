module

public import VerifiedGarbage.Proof.Ecdh.X86_64.CheckFn
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.InverseVerified
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.InverseLit
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.TaintMap
import VerifiedGarbage.Proof.Weierstrass.X86_64.P224Literals
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
meta import VerifiedGarbage.Proof.Ecdh.X86_64.CheckFn
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.InverseVerified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.InverseLit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.TaintMap
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.P224Literals
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb

/-!
# `vg_p224_check_point` on x86-64: `Verified`

`CheckFn.correct` for P-224's configurations (`Inverse.cfg`), whose slots
are the curve's (`agree`); constant time by taint tracking, `rdi` and `rsp`
public, on the code's literals.
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86_64.P224.Check

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64 VG.Proof.Ecdh.X86_64.CheckFn
open VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64.P224.Inverse (cfg cfg_ok)

abbrev C : CP := Impl.Weierstrass.CheckPoint.p224

/-- `vg_p224_check_point` (no `_adx` form: `adx` is ignored). -/
abbrev code (adx : Bool) : Prog isa := Cfg.invFnX (Impl.Ecdh.X86_64.Cfg.checkBody (cfg adx))

theorem agree (adx : Bool) : Agree (cfg adx) C := by
  cases adx <;> exact ⟨rfl, rfl, by decide +kernel, keeps_of_covers (by decide +kernel), by decide +kernel⟩

theorem hvm (adx : Bool) : (Impl.Ecdh.X86_64.Cfg.checkBody (cfg adx)).allInstrs
    (fun i => !KeepReg.writesVec i && !loadsMxcsr i) = true := by
  cases adx <;> lit_decide

theorem hv (adx : Bool) :
    (Impl.Ecdh.X86_64.Cfg.checkBody (cfg adx)).allInstrs (fun i => !KeepReg.writesVec i) = true :=
  (hv_hmx (hvm adx)).1

theorem hn (adx : Bool) : (Impl.Ecdh.X86_64.Cfg.checkBody (cfg adx)).noCalls = true := by
  cases adx <;> lit_decide

theorem hmx (adx : Bool) : (code adx).allInstrs (fun i => !loadsMxcsr i) = true :=
  (hv_hmx (hvm adx)).2

theorem ct (adx : Bool) : ConstantTime isa (checkK C).pre (checkK C).pub (code adx) := by
  cases adx <;>
    exact VG.Taint.constantTime (A := X86_64.taint) (Taint.ofRegs [.rdi, .rsp]) (agreeK C) (by taint_decide)

theorem sat : C.pre 0x1000 (satMem C) := by
  unfold Impl.Weierstrass.CheckPoint.Curve.pre; decide +kernel

theorem verified (hI : InvSounds) (adx : Bool) :
    Verified X86_64.target (code adx) (C.checkContract X86_64.abi) :=
  Verified.of_correct (correct (cfg_ok hI adx) (agree adx) (hv adx) (hn adx) (hmx adx)) (ct adx)
    (implies C sat)

end VG.Proof.Ecdh.X86_64.P224.Check
