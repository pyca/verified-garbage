module

public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentPowerLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationEnvironment
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedPower
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerVetted
import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerCT

/-! One reusable RSA Montgomery helper instantiates cached private-key powers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedPower
open VG VG.Arm VG.Proof.Bignum.Arm

def power (backend : MontBackend) : Prog isa :=
  VG.Impl.Ffdh.Arm.CachedPower.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)

theorem powerLaw (backend : MontBackend) :
    EnvironmentPowerLaw cachedGenerationEnvironment ScalarLayout.vetted (power backend) := by
  constructor
  · intro s p slots eb context cached calls stable h52 _h56 _h32 ready modulus odd r2 exponent size scalarFit
    exact vetted_correct backend s context cached calls stable h52 ready modulus odd r2 exponent size scalarFit
  · exact code_ct backend

end VG.Proof.Ffdh.Arm.CachedPower
