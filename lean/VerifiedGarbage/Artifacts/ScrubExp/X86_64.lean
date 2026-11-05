module

public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256Avx2
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256ShaNi
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Sha256.ScrubLocal
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha256.X86_64.Lit
import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Lit

/-!
# Experiment: SHA-256's streaming and one-shot functions without secret residue (x86-64)

The functions `Proof.Pbkdf2.Md.X86_64.Sha256.stream` makes for each
compression function, run by `Impl.Scrub.X86_64.scrub` (`X86_64.scrubReg`),
named with `_scrub` after the variant's suffix, so that they are emitted
next to the functions they scrub, for measuring.
-/

@[expose] public section

namespace VG.Artifacts.ScrubExp.X86_64

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64 VG.Proof.Pbkdf2.Md.X86_64

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

def updScalar := scrubReg (updR scalar) .sse (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (updOut _) rfl

theorem updScalar_noResidue : NoResidue updScalar.code (updR scalar).contract (Spec.Sha256.updateSig.retBits 64) :=
  scrubReg_noResidue (updR scalar) .sse (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
    (updOut _) rfl

def updAvx2 := scrubReg (updR avx2) .avx (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (updOut _) rfl

theorem updAvx2_noResidue : NoResidue updAvx2.code (updR avx2).contract (Spec.Sha256.updateSig.retBits 64) :=
  scrubReg_noResidue (updR avx2) .avx (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
    (updOut _) rfl

def updShani := scrubReg (updR shani) .sse (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (updOut _) rfl

theorem updShani_noResidue : NoResidue updShani.code (updR shani).contract (Spec.Sha256.updateSig.retBits 64) :=
  scrubReg_noResidue (updR shani) .sse (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
    (updOut _) rfl

def finScalar := scrubReg (finR scalar) .sse (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (finOut _) rfl

theorem finScalar_noResidue : NoResidue finScalar.code (finR scalar).contract (Spec.Sha256.finalizeSig.retBits 64) :=
  scrubReg_noResidue (finR scalar) .sse (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
    (finOut _) rfl

def finAvx2 := scrubReg (finR avx2) .avx (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (finOut _) rfl

theorem finAvx2_noResidue : NoResidue finAvx2.code (finR avx2).contract (Spec.Sha256.finalizeSig.retBits 64) :=
  scrubReg_noResidue (finR avx2) .avx (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
    (finOut _) rfl

def finShani := scrubReg (finR shani) .sse (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (finOut _) rfl

theorem finShani_noResidue : NoResidue finShani.code (finR shani).contract (Spec.Sha256.finalizeSig.retBits 64) :=
  scrubReg_noResidue (finR shani) .sse (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
    (finOut _) rfl

def digScalar := scrubReg (digR scalar) .sse (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (digOut _) rfl

theorem digScalar_noResidue : NoResidue digScalar.code (digR scalar).contract ((Spec.Sha256.digestSig 32).retBits 64) :=
  scrubReg_noResidue (digR scalar) .sse (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
    (digOut _) rfl

def digAvx2 := scrubReg (digR avx2) .avx (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (digOut _) rfl

theorem digAvx2_noResidue : NoResidue digAvx2.code (digR avx2).contract ((Spec.Sha256.digestSig 32).retBits 64) :=
  scrubReg_noResidue (digR avx2) .avx (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
    (digOut _) rfl

def digShani := scrubReg (digR shani) .sse (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
  (digOut _) rfl

theorem digShani_noResidue : NoResidue digShani.code (digR shani).contract ((Spec.Sha256.digestSig 32).retBits 64) :=
  scrubReg_noResidue (digR shani) .sse (by lit_decide) (by decide) (by decide) (by lit_decide) (by decide)
    (digOut _) rfl

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
