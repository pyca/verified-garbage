module

public import VerifiedGarbage.Proof.Pbkdf2.Stream.PPC64LE.Instance
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Md5
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.PPC64LE.Instance
meta import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Md5

/-!
# PBKDF2-HMAC-MD5 on PPC64LE: `iterate`

The constant time of `iterate`'s code over MD5's streaming functions, which
the kernel checks, and `iterate` against the shared contract of
`Spec.Hmac.md5I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Stream.PPC64LE.Md5

open VG.PPC64LE
open VG.Proof.Hmac.Stream.PPC64LE.Md5 (hash ok)

/-- `iterate`'s constant time, which the kernel checks. -/
theorem iterate_ct : ConstantTime isa (iterG ok.SH (VG.Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes hash) 96).pre
    (iterG ok.SH (VG.Impl.Pbkdf2.Stream.PPC64LE.Iter.bytes hash) 96).pub
    (VG.Impl.Pbkdf2.Stream.PPC64LE.iterate hash) :=
  Shared.ct _ _ (by taint_decide)

theorem iterate : Verified PPC64LE.target (VG.Impl.Pbkdf2.Stream.PPC64LE.iterate hash)
    (Spec.Hmac.md5I.iterateContract PPC64LE.abi 96) :=
  Shared.iterate ok rfl (by decide) iterate_ct (by
    inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig,
      Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, PPC64LE.abi, PPC64LE.argRegs]
      using iterSat 80 16 384)

end VG.Proof.Pbkdf2.Stream.PPC64LE.Md5
