module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveContext

/-! The public sieve loop records precisely which RSA primes have been tried. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (arrAt)

def sieveAny (value count : Nat) : Bool :=
  (List.range count).any fun i => value % VG.Impl.RsaKeyGen.tabEntry i == 0

end VG.Proof.Ffdh.Arm.ParameterCandidate
