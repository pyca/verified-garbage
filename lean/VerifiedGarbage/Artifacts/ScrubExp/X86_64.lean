module

public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256Avx2
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256ShaNi
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Sha256.ScrubLocal
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha256.X86_64.Lit
import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Lit
public meta import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256
public meta import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256Avx2
public meta import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256ShaNi
public meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public meta import VerifiedGarbage.Proof.Sha256.ScrubLocal
public meta import VerifiedGarbage.Proof.Framework.Registration
public meta import VerifiedGarbage.Proof.Sha256.X86_64.Lit
public meta import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Lit

/-!
# Experiment: SHA-256's streaming and one-shot functions without secret residue (x86-64)

The functions `Proof.Pbkdf2.Md.X86_64.Sha256.stream` makes for each
compression function, run by `Impl.Scrub.X86_64.scrub` (`X86_64.scrubReg`),
named with `_scrub` after the variant's suffix, so that they are emitted
next to the functions they scrub, for measuring.
-/

@[expose] public section

namespace VG.Artifacts.ScrubExp.X86_64

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64 VG.Proof.Pbkdf2.Md.X86_64 VG.X86_64.RScrub

abbrev scalar := Proof.Variants.MdHash.X86_64.Sha256.compress
abbrev avx2 := Proof.Variants.MdHash.X86_64.Sha256Avx2.compress
abbrev shani := Proof.Variants.MdHash.X86_64.Sha256ShaNi.compress

theorem updOut (stack : Nat) :
    PostOut (Spec.Sha256.updateContract X86_64.abi stack) (Spec.Sha256.updateSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha256.updatePost_out 64)

theorem finOut (stack : Nat) :
    PostOut (Spec.Sha256.finalizeContract X86_64.abi stack) (Spec.Sha256.finalizeSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha256.finalizePost_out 64)

theorem digOut (stack : Nat) :
    PostOut (Spec.Sha256.digestContract X86_64.abi 32 Spec.Sha256.hash stack)
      ((Spec.Sha256.digestSig 32).retBits 64) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha256.digestPost_out 32 Spec.Sha256.hash 64 (by decide))

/-- `vg_sha256_update` with the compression function `v`, as `Sha256.stream`
registers it, but named with `_scrub`. -/
def updR (v : Proof.Sha256.X86_64.Compress) : Registration Spec.Sha256.updateApi X86_64.target where
  suffix := v.suffix ++ "_scrub"
  code := Impl.StackScratch.X86_64.withStackScratch 616 .r8 (Impl.Sha256.X86_64.Stream.update v.callee)
  contract := Spec.Sha256.updateContract X86_64.abi (8 + 616)
  stack := 8 + 616
  verified := Proof.Sha256.X86_64.Shared.update v.ok v.mxcsr v.spSafe v.noStack
  spSafe := X86_64.withStackScratch_spSafe (by decide)
    (Proof.Sha256.X86_64.Shared.update_spSafe v.spSafe)
  features := v.features

def finR (v : Proof.Sha256.X86_64.Compress) : Registration Spec.Sha256.finalizeApi X86_64.target where
  suffix := v.suffix ++ "_scrub"
  code := Impl.StackScratch.X86_64.withStackScratch 616 .rcx (Impl.Sha256.X86_64.Stream.finalize v.callee)
  contract := Spec.Sha256.finalizeContract X86_64.abi (8 + 616)
  stack := 8 + 616
  verified := Proof.Sha256.X86_64.Shared.finalize v.ok v.mxcsr v.spSafe v.noStack
  spSafe := X86_64.withStackScratch_spSafe (by decide)
    (Proof.Sha256.X86_64.Shared.finalize_spSafe v.spSafe)
  features := v.features

def digR (v : Proof.Sha256.X86_64.Compress) : Registration Spec.Sha256.digest256Api X86_64.target where
  suffix := v.suffix ++ "_scrub"
  code := Proof.Sha256.X86_64.OneShot.digest (Impl.MdStream.X86_64.out32 8 true) Spec.Sha256.H0 v.callee
  contract := Spec.Sha256.digestContract X86_64.abi 32 Spec.Sha256.hash (8 + Proof.Sha256.X86_64.OneShot.frame)
  stack := 8 + Proof.Sha256.X86_64.OneShot.frame
  verified := Proof.Sha256.X86_64.OneShot.verified Proof.Sha256.X86_64.OneShot.code256
    Proof.Sha256.X86_64.OneShot.init_check256 Proof.Sha256.X86_64.OneShot.hash_take v.ok v.mxcsr v.spSafe
    v.noStack
  spSafe := Proof.Sha256.X86_64.OneShot.spSafe Proof.Sha256.X86_64.OneShot.code256 Spec.Sha256.H0 v.spSafe
  features := v.features

def updScalarKs : List Nat := keep_for% Spec.Sha256.updateApi.sig (updR scalar).stack (updR scalar).code

theorem updScalarRes : ResOk (updR scalar).code (updR scalar).contract (updR scalar).stack updScalarKs (chunks (updR scalar).stack) :=
  RScrub.resOk_reg (updR scalar) updScalarKs (by taint_decide)

def updScalar := scrubReg (updR scalar) .sse updScalarKs (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (updOut _) updScalarRes rfl

theorem updScalar_noResidue : NoResidue updScalar.code (updR scalar).contract (Spec.Sha256.updateSig.retBits 64) :=
  scrubReg_noResidue (updR scalar) .sse updScalarKs (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
    (updOut _) updScalarRes rfl

def updAvx2Ks : List Nat := keep_for% Spec.Sha256.updateApi.sig (updR avx2).stack (updR avx2).code

theorem updAvx2Res : ResOk (updR avx2).code (updR avx2).contract (updR avx2).stack updAvx2Ks (chunks (updR avx2).stack) :=
  RScrub.resOk_reg (updR avx2) updAvx2Ks (by taint_decide)

def updAvx2 := scrubReg (updR avx2) .avx updAvx2Ks (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (updOut _) updAvx2Res rfl

theorem updAvx2_noResidue : NoResidue updAvx2.code (updR avx2).contract (Spec.Sha256.updateSig.retBits 64) :=
  scrubReg_noResidue (updR avx2) .avx updAvx2Ks (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
    (updOut _) updAvx2Res rfl

def updShaniKs : List Nat := keep_for% Spec.Sha256.updateApi.sig (updR shani).stack (updR shani).code

theorem updShaniRes : ResOk (updR shani).code (updR shani).contract (updR shani).stack updShaniKs (chunks (updR shani).stack) :=
  RScrub.resOk_reg (updR shani) updShaniKs (by taint_decide)

def updShani := scrubReg (updR shani) .sse updShaniKs (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (updOut _) updShaniRes rfl

theorem updShani_noResidue : NoResidue updShani.code (updR shani).contract (Spec.Sha256.updateSig.retBits 64) :=
  scrubReg_noResidue (updR shani) .sse updShaniKs (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
    (updOut _) updShaniRes rfl

def finScalarKs : List Nat := keep_for% Spec.Sha256.finalizeApi.sig (finR scalar).stack (finR scalar).code

theorem finScalarRes : ResOk (finR scalar).code (finR scalar).contract (finR scalar).stack finScalarKs (chunks (finR scalar).stack) :=
  RScrub.resOk_reg (finR scalar) finScalarKs (by taint_decide)

def finScalar := scrubReg (finR scalar) .sse finScalarKs (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (finOut _) finScalarRes rfl

theorem finScalar_noResidue : NoResidue finScalar.code (finR scalar).contract (Spec.Sha256.finalizeSig.retBits 64) :=
  scrubReg_noResidue (finR scalar) .sse finScalarKs (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
    (finOut _) finScalarRes rfl

def finAvx2Ks : List Nat := keep_for% Spec.Sha256.finalizeApi.sig (finR avx2).stack (finR avx2).code

theorem finAvx2Res : ResOk (finR avx2).code (finR avx2).contract (finR avx2).stack finAvx2Ks (chunks (finR avx2).stack) :=
  RScrub.resOk_reg (finR avx2) finAvx2Ks (by taint_decide)

def finAvx2 := scrubReg (finR avx2) .avx finAvx2Ks (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (finOut _) finAvx2Res rfl

theorem finAvx2_noResidue : NoResidue finAvx2.code (finR avx2).contract (Spec.Sha256.finalizeSig.retBits 64) :=
  scrubReg_noResidue (finR avx2) .avx finAvx2Ks (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
    (finOut _) finAvx2Res rfl

def finShaniKs : List Nat := keep_for% Spec.Sha256.finalizeApi.sig (finR shani).stack (finR shani).code

theorem finShaniRes : ResOk (finR shani).code (finR shani).contract (finR shani).stack finShaniKs (chunks (finR shani).stack) :=
  RScrub.resOk_reg (finR shani) finShaniKs (by taint_decide)

def finShani := scrubReg (finR shani) .sse finShaniKs (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (finOut _) finShaniRes rfl

theorem finShani_noResidue : NoResidue finShani.code (finR shani).contract (Spec.Sha256.finalizeSig.retBits 64) :=
  scrubReg_noResidue (finR shani) .sse finShaniKs (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
    (finOut _) finShaniRes rfl

def digScalarKs : List Nat := keep_for% Spec.Sha256.digest256Api.sig (digR scalar).stack (digR scalar).code

theorem digScalarRes : ResOk (digR scalar).code (digR scalar).contract (digR scalar).stack digScalarKs (chunks (digR scalar).stack) :=
  RScrub.resOk_reg (digR scalar) digScalarKs (by taint_decide)

def digScalar := scrubReg (digR scalar) .sse digScalarKs (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (digOut _) digScalarRes rfl

theorem digScalar_noResidue : NoResidue digScalar.code (digR scalar).contract ((Spec.Sha256.digestSig 32).retBits 64) :=
  scrubReg_noResidue (digR scalar) .sse digScalarKs (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
    (digOut _) digScalarRes rfl

def digAvx2Ks : List Nat := keep_for% Spec.Sha256.digest256Api.sig (digR avx2).stack (digR avx2).code

theorem digAvx2Res : ResOk (digR avx2).code (digR avx2).contract (digR avx2).stack digAvx2Ks (chunks (digR avx2).stack) :=
  RScrub.resOk_reg (digR avx2) digAvx2Ks (by taint_decide)

def digAvx2 := scrubReg (digR avx2) .avx digAvx2Ks (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (digOut _) digAvx2Res rfl

theorem digAvx2_noResidue : NoResidue digAvx2.code (digR avx2).contract ((Spec.Sha256.digestSig 32).retBits 64) :=
  scrubReg_noResidue (digR avx2) .avx digAvx2Ks (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
    (digOut _) digAvx2Res rfl

def digShaniKs : List Nat := keep_for% Spec.Sha256.digest256Api.sig (digR shani).stack (digR shani).code

theorem digShaniRes : ResOk (digR shani).code (digR shani).contract (digR shani).stack digShaniKs (chunks (digR shani).stack) :=
  RScrub.resOk_reg (digR shani) digShaniKs (by taint_decide)

def digShani := scrubReg (digR shani) .sse digShaniKs (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (digOut _) digShaniRes rfl

theorem digShani_noResidue : NoResidue digShani.code (digR shani).contract ((Spec.Sha256.digestSig 32).retBits 64) :=
  scrubReg_noResidue (digR shani) .sse digShaniKs (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
    (digOut _) digShaniRes rfl

def artifacts : List Artifact := [
  Spec.Sha256.updateApi.artifact X86_64.target updScalar,
  Spec.Sha256.updateApi.artifact X86_64.target updAvx2,
  Spec.Sha256.updateApi.artifact X86_64.target updShani,
  Spec.Sha256.finalizeApi.artifact X86_64.target finScalar,
  Spec.Sha256.finalizeApi.artifact X86_64.target finAvx2,
  Spec.Sha256.finalizeApi.artifact X86_64.target finShani,
  Spec.Sha256.digest256Api.artifact X86_64.target digScalar,
  Spec.Sha256.digest256Api.artifact X86_64.target digAvx2,
  Spec.Sha256.digest256Api.artifact X86_64.target digShani]

end VG.Artifacts.ScrubExp.X86_64
