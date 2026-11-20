module

public import VerifiedGarbage.Impl.Rsa.X86_64.Fn
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
public import VerifiedGarbage.Proof.Rsa.X86_64.Instances
public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.Verified
public import VerifiedGarbage.Proof.Rsa.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Lit

/-!
# RSA's key functions on x86-64, without secret residue

Each function as emitted (`Impl.Rsa.X86_64.Fn`), its whole stack wiped by its
cleanup (`X86_64.Scrub.verifiedScrubbedAll`): it meets its contract in
constant time and returns without secret residue. Their postconditions read
the memory on return only within their buffers (`Proof/Rsa/X86_64/Scrub.lean`).
-/

-- separate module: the kernel's evaluation of the cleanup's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Scrubbed

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Rsa.X86_64

theorem publicPrecompute_codeSp :
    (Precompute.code Fn.mmBase).all (fun i => !isa.writesSp i) = true := by sp_safe

theorem publicPrecompute_scrubbed :
    VerifiedScrubbed target Fn.publicPrecompute (Spec.Rsa.publicPrecomputeApi.contract X86_64.abi 8) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.publicPrecomputeApi)
    { code := Precompute.code Fn.mmBase, stack := 8
      verified := Proof.Rsa.X86_64.Instances.precompute_verified, spSafe := publicPrecompute_codeSp }
    .sse (Proof.Rsa.X86_64.Scrub.publicPrecomputeOut 8)

theorem publicPrecompute_spSafe : Fn.publicPrecompute.all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe publicPrecompute_codeSp

theorem publicPrecomputeAdx_codeSp :
    (Precompute.code Fn.mmAdx (Impl.Bignum.X86_64.R2Adx.choice Fn.mmAdx)).all (fun i => !isa.writesSp i) = true := by
  sp_safe

theorem publicPrecomputeAdx_scrubbed :
    VerifiedScrubbed target Fn.publicPrecomputeAdx (Spec.Rsa.publicPrecomputeApi.contract X86_64.abi 8) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.publicPrecomputeApi)
    { code := Precompute.code Fn.mmAdx (Impl.Bignum.X86_64.R2Adx.choice Fn.mmAdx), stack := 8
      verified := Proof.Rsa.X86_64.Instances.precomputeAdx_verified, spSafe := publicPrecomputeAdx_codeSp }
    .sse (Proof.Rsa.X86_64.Scrub.publicPrecomputeOut 8)

theorem publicPrecomputeAdx_spSafe : Fn.publicPrecomputeAdx.all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe publicPrecomputeAdx_codeSp

theorem privatePrecompute_codeSp : (PrivPre.code Fn.mmBase).all (fun i => !isa.writesSp i) = true := by sp_safe

theorem privatePrecompute_scrubbed :
    VerifiedScrubbed target Fn.privatePrecompute (Spec.Rsa.privatePrecomputeApi.contract X86_64.abi 8) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.privatePrecomputeApi)
    { code := PrivPre.code Fn.mmBase, stack := 8
      verified := Proof.Bignum.X86_64.PrivPre.pp_verified, spSafe := privatePrecompute_codeSp }
    .sse (Proof.Bignum.X86_64.PrivPre.pp_postOut 8)

theorem privatePrecompute_spSafe : Fn.privatePrecompute.all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe privatePrecompute_codeSp

theorem privatePrecomputeAdx_codeSp : (PrivPre.code Fn.mmAdx).all (fun i => !isa.writesSp i) = true := by sp_safe

theorem privatePrecomputeAdx_scrubbed :
    VerifiedScrubbed target Fn.privatePrecomputeAdx (Spec.Rsa.privatePrecomputeApi.contract X86_64.abi 8) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.privatePrecomputeApi)
    { code := PrivPre.code Fn.mmAdx, stack := 8
      verified := Proof.Bignum.X86_64.PrivPre.ppAdx_verified, spSafe := privatePrecomputeAdx_codeSp }
    .sse (Proof.Bignum.X86_64.PrivPre.pp_postOut 8)

theorem privatePrecomputeAdx_spSafe : Fn.privatePrecomputeAdx.all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe privatePrecomputeAdx_codeSp

theorem crtValues_codeSp : Keys.CrtValues.code.all (fun i => !isa.writesSp i) = true := by sp_safe

theorem crtValues_scrubbed :
    VerifiedScrubbed target Fn.crtValues (Spec.Rsa.crtValuesApi.contract X86_64.abi 0) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.crtValuesApi)
    { code := Keys.CrtValues.code, stack := 0
      verified := Proof.Rsa.X86_64.Instances.crtValues_verified, spSafe := crtValues_codeSp }
    .sse (Proof.Rsa.X86_64.Scrub.crtValuesOut 0)

theorem crtValues_spSafe : Fn.crtValues.all (fun i => !isa.writesSp i) = true := scrubKs_spSafe crtValues_codeSp

theorem recoverPrimesDet_codeSp : Keys.RecoverDet.code.all (fun i => !isa.writesSp i) = true := by sp_safe

theorem recoverPrimesDet_scrubbed :
    VerifiedScrubbed target Fn.recoverPrimesDet (Spec.Rsa.recoverPrimesDetApi.contract X86_64.abi 0) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.recoverPrimesDetApi)
    { code := Keys.RecoverDet.code, stack := 0
      verified := Proof.Rsa.X86_64.Instances.recoverDet_verified, spSafe := recoverPrimesDet_codeSp }
    .sse (Proof.Rsa.X86_64.Scrub.recoverPrimesDetOut 0)

theorem recoverPrimesDet_spSafe : Fn.recoverPrimesDet.all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe recoverPrimesDet_codeSp

theorem checkKey_codeSp : CheckKey.code.all (fun i => !isa.writesSp i) = true := by sp_safe

theorem checkKey_scrubbed :
    VerifiedScrubbed target Fn.checkKey (Spec.Rsa.checkKeyApi.contract X86_64.abi 0) 32 :=
  verifiedScrubbedAll (api := Spec.Rsa.checkKeyApi)
    { code := CheckKey.code, stack := 0
      verified := Proof.Rsa.X86_64.Instances.checkKey_verified, spSafe := checkKey_codeSp }
    .sse (Proof.Rsa.X86_64.Scrub.checkKeyOut 0)

theorem checkKey_spSafe : Fn.checkKey.all (fun i => !isa.writesSp i) = true := scrubKs_spSafe checkKey_codeSp

end VG.Proof.Rsa.X86_64.Scrubbed
