module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha224
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFin
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Loop
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256
public import VerifiedGarbage.Proof.Sha256.X86.Stream.Variant
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.Sha256.X86

/-! # PBKDF2-HMAC-SHA-224 (RFC 8018) on x86, for every x86 SHA-256 backend: the iteration and the whole derivation -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha224.X86

def artifactsFor (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  Spec.Hmac.sha224I.pbkdf2Api.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Whole.X86.pbkFrame Spec.Hmac.sha224I) 7 v.F224.pbkdf2
    stack := 76 + Proof.Pbkdf2.Whole.X86.pbkFrame Spec.Hmac.sha224I
    verified := Proof.Pbkdf2.Whole.X86.pbkFramed (Proof.Pbkdf2.Whole.X86.sha224_verified v)
      Proof.Pbkdf2.Whole.X86.sha224_pbkFrameSat
      (Proof.Pbkdf2.Whole.X86.noEsp_of_all v.pbkdf2_224Sp) (Proof.Pbkdf2.Whole.X86.sha224_stack v)
    spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe v.pbkdf2_224Sp
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.Sha256.X86.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Pbkdf2Sha224.X86
