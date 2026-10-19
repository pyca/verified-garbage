module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PrimeLoop
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Draw
import VerifiedGarbage.Proof.Framework.Omega

/-! Reuse the shared whole-draw availability check before reading entropy. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem tapeCheck_ok {P : PrimeParams} {used : Nat} {s : State}
    (h : PrimeState P used s) (hu : used ≤ P.rand.length) :
    WP isa (.block Impl.Dsa.AArch64.Generation.tapeCheck) s fun t =>
      isa.eval (.zero .x .x5) t = some (decide (P.rand.length < used + P.drawBytes)) ∧
      t.mem = s.mem ∧ Keep [.x3, .x4, .x5, .x7] s t :=
  VG.Proof.Ffdh.AArch64.ParameterCandidate.roomHead_ok h.ready.ws
    (by have := P.drawMax; omega) P.randMax hu h.draw h.randLen h.used

end VG.Proof.Dsa.AArch64.Generation
