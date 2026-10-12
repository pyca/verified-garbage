import VerifiedGarbage.Proof.Ecdh.X86_64.CheckFn
import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.InverseVerified
import VerifiedGarbage.Proof.Weierstrass.X86_64.Secp256k1Literals

/-!
# `vg_secp256k1_check_point` on x86-64: `Verified`

`CheckFn.correct` for secp256k1's configurations (`Inverse.cfg`), whose slots
are the curve's (`agree`); constant time by taint tracking, `rdi` and `rsp`
public, on the code's literals.
-/

namespace VG.Proof.Ecdh.X86_64.Secp256k1.Check

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64 VG.Proof.Ecdh.X86_64.CheckFn
open VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64.Secp256k1.Inverse (cfg cfg_ok)

abbrev C : CP := Spec.Weierstrass.CheckPoint.secp256k1

/-- `vg_secp256k1_check_point` (no `_adx` form: `adx` is ignored). -/
abbrev code (adx : Bool) : Prog isa := Cfg.invFnX (Impl.Ecdh.X86_64.Cfg.checkBody (cfg adx))

theorem agree (adx : Bool) : Agree (cfg adx) C := by
  cases adx <;> exact ⟨rfl, rfl, by decide, keeps_of (by decide), by decide⟩

theorem hv (adx : Bool) :
    (Impl.Ecdh.X86_64.Cfg.checkBody (cfg adx)).allInstrs (fun i => !KeepReg.writesVec i) = true := by
  cases adx <;> lit_decide

theorem hn (adx : Bool) : (Impl.Ecdh.X86_64.Cfg.checkBody (cfg adx)).noCalls = true := by
  cases adx <;> lit_decide

theorem hmx (adx : Bool) : (code adx).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases adx <;> lit_decide

theorem ct (adx : Bool) : ConstantTime isa (checkK C).pre (checkK C).pub (code adx) := by
  cases adx <;>
    exact VG.Taint.constantTime (A := X86_64.taint) (Taint.ofRegs [.rdi, .rsp]) (agreeK C) (by taint_decide)

theorem sat : C.pre 0x1000 (satMem C) := by
  unfold Spec.Weierstrass.CheckPoint.Curve.pre; decide +kernel

theorem verified (hI : InvSounds) (adx : Bool) :
    Verified X86_64.target (code adx) (C.checkContract X86_64.abi) :=
  Verified.of_correct (correct (cfg_ok hI adx) (agree adx) (hv adx) (hn adx) (hmx adx)) (ct adx)
    (implies C sat)

end VG.Proof.Ecdh.X86_64.Secp256k1.Check
