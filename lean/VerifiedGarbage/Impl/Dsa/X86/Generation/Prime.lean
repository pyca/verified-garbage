module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeControl

/-! # Prepare a loaded candidate once, then consume its primality witnesses -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

def primePrepare (len : Nat) : Prog isa :=
  let n := (len + 7) / 8
  .seq (contextSetup n) (prepareExponent n)

def primeTest (len : Nat) : Prog isa :=
  .seq (primePrepare len) (primeLoop len (8 * ((len + 7) / 8)) (if len ≤ 256 then 64 else 128))
end VG.Impl.Dsa.X86.Generation
