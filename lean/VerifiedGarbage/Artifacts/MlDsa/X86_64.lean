module

public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Inst
import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.MlDsa.X86_64.KeyGen.Inst
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Call
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
public import VerifiedGarbage.Proof.MlDsa.DecideAt
public import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Mask
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.RestRow
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Samp4
public import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Top
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.MlDsaArith.X86_64
public import VerifiedGarbage.Proof.MlDsa.X86_64.PkTr
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Prims
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.Prepare
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.ExternalMu
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Verified
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Sign
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inst
public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignFn
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
public import VerifiedGarbage.Proof.MlDsa.Pack.Arith
public import VerifiedGarbage.Proof.MlDsa.Pack.Stream
public import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseCCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseDCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseKCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseOCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.SignCT
public import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
public import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.Sat
public import VerifiedGarbage.Impl.MlDsa.X86_64.Message
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignVerified
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.HashCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCorrect
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Instrs
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyFn
public import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
public import VerifiedGarbage.Proof.MlDsa.Verify.Mem
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Same
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintPack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintUnpack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.SimpleBitPack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Unpack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.BallCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTCompute
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTSample
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTStages
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Control
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Correct
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Verified
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyVerified
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CallPack

/-! # ML-DSA (FIPS 204) on x86-64 -/

@[expose] public section

-- ML-DSA (FIPS 204) on x86-64: key generation
namespace VG.Artifacts.MlDsa.X86_64.KeyGen

open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Impl.MlDsa.X86_64.KeyGen (keyGen primsWith)

def artifactsFor (v : ArithImpl) : List Artifact := [
  Spec.MlDsa.keyGen44Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := keyGen (primsWith v.code) Spec.MlDsa.mlDsa44
    stack := 32
    verified := Proof.MlDsa.X86_64.KeyGen.keyGen_verifiedWith v (.inl rfl)
    spSafe := Proof.MlDsa.X86_64.KeyGen.keyGen_spSafe v (.inl rfl) },
  Spec.MlDsa.keyGen65Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := keyGen (primsWith v.code) Spec.MlDsa.mlDsa65
    stack := 32
    verified := Proof.MlDsa.X86_64.KeyGen.keyGen_verifiedWith v (.inr (.inl rfl))
    spSafe := Proof.MlDsa.X86_64.KeyGen.keyGen_spSafe v (.inr (.inl rfl)) },
  Spec.MlDsa.keyGen87Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := keyGen (primsWith v.code) Spec.MlDsa.mlDsa87
    stack := 32
    verified := Proof.MlDsa.X86_64.KeyGen.keyGen_verifiedWith v (.inr (.inr rfl))
    spSafe := Proof.MlDsa.X86_64.KeyGen.keyGen_spSafe v (.inr (.inr rfl)) }]

def artifacts : List Artifact :=
  VG.Proof.Variants.MlDsaArith.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.MlDsa.X86_64.KeyGen

-- ML-DSA (FIPS 204) on x86-64: preparing keys
namespace VG.Artifacts.MlDsa.X86_64.PreparedKey

open VG
open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.Verify (primsWith prims_okWith)
open VG.Proof.MlDsa.X86_64.Verify.Prepare (preparePublic_verified prepareSecret_verified preparePublic_spSafe
  prepareSecret_spSafe)

def artifactsFor (v : ArithImpl) : List Artifact := [
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith v.code) Spec.MlDsa.mlDsa44
    stack := 32
    verified := preparePublic_verified (prims_okWith v) (List.mem_cons_self ..)
    spSafe := preparePublic_spSafe (prims_okWith v) (List.mem_cons_self ..) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith v.code) Spec.MlDsa.mlDsa44
    stack := 32
    verified := prepareSecret_verified (prims_okWith v) (List.mem_cons_self ..)
    spSafe := prepareSecret_spSafe (prims_okWith v) (List.mem_cons_self ..) },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith v.code) Spec.MlDsa.mlDsa65
    stack := 32
    verified := preparePublic_verified (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    spSafe := preparePublic_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith v.code) Spec.MlDsa.mlDsa65
    stack := 32
    verified := prepareSecret_verified (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    spSafe := prepareSecret_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) },
  (Spec.MlDsa.preparePublicKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.PreparedKey.preparePublic (primsWith v.code) Spec.MlDsa.mlDsa87
    stack := 32
    verified := preparePublic_verified (prims_okWith v)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := preparePublic_spSafe (prims_okWith v)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) },
  (Spec.MlDsa.prepareSecretKeyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.PreparedKey.prepareSecret (primsWith v.code) Spec.MlDsa.mlDsa87
    stack := 32
    verified := prepareSecret_verified (prims_okWith v)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := prepareSecret_spSafe (prims_okWith v)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) }]

def artifacts : List Artifact :=
  VG.Proof.Variants.MlDsaArith.X86_64.samplerFreeVariants.flatMap fun v => artifactsFor v

end VG.Artifacts.MlDsa.X86_64.PreparedKey

-- ML-DSA (FIPS 204) on x86-64: signing
namespace VG.Artifacts.MlDsa.X86_64.Sign

open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.Sign (primsWith)

def artifactsFor (v : ArithImpl) : List Artifact := [
  Spec.MlDsa.sign44Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Sign.entry (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa44) 0
    stack := 40
    verified := Proof.MlDsa.X86_64.Message.signEntry_verified v (List.mem_cons_self ..) _
    spSafe := Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl)) 0 },
  Spec.MlDsa.sign65Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Sign.entry (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa65) 0
    stack := 40
    verified := Proof.MlDsa.X86_64.Message.signEntry_verified v (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _
    spSafe := Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl))) 0 },
  Spec.MlDsa.sign87Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Sign.entry (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa87) 0
    stack := 40
    verified := Proof.MlDsa.X86_64.Message.signEntry_verified v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) _
    spSafe := Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl))) 0 },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Sign.entry (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa44) 1
    stack := 40
    verified := Proof.MlDsa.X86_64.Message.signPreparedEntry_verified v (List.mem_cons_self ..) _
    spSafe := Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl)) 1 },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Sign.entry (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa65) 1
    stack := 40
    verified := Proof.MlDsa.X86_64.Message.signPreparedEntry_verified v (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _
    spSafe := Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl))) 1 },
  (Spec.MlDsa.preparedSignApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Sign.entry (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa87) 1
    stack := 40
    verified := Proof.MlDsa.X86_64.Message.signPreparedEntry_verified v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) _
    spSafe := Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl))) 1 }]

def artifacts : List Artifact :=
  VG.Proof.Variants.MlDsaArith.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.MlDsa.X86_64.Sign

-- ML-DSA (FIPS 204) on x86-64: signing messages
namespace VG.Artifacts.MlDsa.X86_64.SignMessage

open VG
open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.Sign (primsWith)
open VG.Proof.MlDsa.X86_64.Message (signFn signMessage_verified signMessage_spSafe signMessagePrepared_verified
  signPrepared_sat)

def artifactsFor (v : ArithImpl) : List Artifact := [
  Spec.MlDsa.signMessage44Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Message.signMessage (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44 0
    stack := 112
    verified := signMessage_verified (signFn v (List.mem_cons_self ..)) (List.mem_cons_self ..)
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl)) 0 },
  Spec.MlDsa.signMessage65Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Message.signMessage (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65 0
    stack := 112
    verified := signMessage_verified (signFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl))) 0 },
  Spec.MlDsa.signMessage87Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Message.signMessage (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87 0
    stack := 112
    verified := signMessage_verified (signFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl))) 0 },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Message.signMessage (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44 1
    stack := 112
    verified := signMessagePrepared_verified (signFn v (List.mem_cons_self ..)) (List.mem_cons_self ..)
      (signPrepared_sat (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_self ..))
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl)) 1 },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Message.signMessage (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65 1
    stack := 112
    verified := signMessagePrepared_verified (signFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (signPrepared_sat (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl))) 1 },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Message.signMessage (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87 1
    stack := 112
    verified := signMessagePrepared_verified (signFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (signPrepared_sat (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl))) 1 }]

def artifacts : List Artifact :=
  VG.Proof.Variants.MlDsaArith.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.MlDsa.X86_64.SignMessage

-- ML-DSA (FIPS 204) on x86-64: verification
namespace VG.Artifacts.MlDsa.X86_64.Verify

open VG
open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.Verify (primsWith prims_okWith verify_spSafe)

def artifactsFor (v : ArithImpl) : List Artifact := [
  Spec.MlDsa.verify44Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Verify.entry (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa44) 0
    stack := 40
    verified := Proof.MlDsa.X86_64.Message.verifyEntry_verified v (List.mem_cons_self ..) _
    spSafe := Proof.MlDsa.X86_64.Message.verifyEntry_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_self ..)) 0 },
  Spec.MlDsa.verify65Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Verify.entry (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa65) 0
    stack := 40
    verified := Proof.MlDsa.X86_64.Message.verifyEntry_verified v (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _
    spSafe := Proof.MlDsa.X86_64.Message.verifyEntry_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))) 0 },
  Spec.MlDsa.verify87Api.artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Verify.entry (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa87) 0
    stack := 40
    verified := Proof.MlDsa.X86_64.Message.verifyEntry_verified v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) _
    spSafe := Proof.MlDsa.X86_64.Message.verifyEntry_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) 0 },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Verify.entry (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa44) 1
    stack := 40
    verified := Proof.MlDsa.X86_64.Message.verifyPreparedEntry_verified v (List.mem_cons_self ..) _
    spSafe := Proof.MlDsa.X86_64.Message.verifyEntry_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_self ..)) 1 },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Verify.entry (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa65) 1
    stack := 40
    verified := Proof.MlDsa.X86_64.Message.verifyPreparedEntry_verified v (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _
    spSafe := Proof.MlDsa.X86_64.Message.verifyEntry_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))) 1 },
  (Spec.MlDsa.preparedVerifyApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Verify.entry (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa87) 1
    stack := 40
    verified := Proof.MlDsa.X86_64.Message.verifyPreparedEntry_verified v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) _
    spSafe := Proof.MlDsa.X86_64.Message.verifyEntry_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) 1 }]

def artifacts : List Artifact :=
  VG.Proof.Variants.MlDsaArith.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.MlDsa.X86_64.Verify

-- ML-DSA (FIPS 204) on x86-64: verifying messages
namespace VG.Artifacts.MlDsa.X86_64.VerifyMessageCached

open VG
open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.Verify (primsWith prims_okWith verify_spSafe)
open VG.Proof.MlDsa.X86_64.Message (verifyFn verifyMessage_verified verifyMessage_spSafe
  verifyMessagePrepared_verified verifyPrepared_sat)

def artifactsFor (v : ArithImpl) : List Artifact := [
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Message.verifyMessageCached (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44 0
    stack := 112
    verified := verifyMessage_verified (verifyFn v (List.mem_cons_self ..)) (List.mem_cons_self ..)
    spSafe := verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_self ..)) 0 },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Message.verifyMessageCached (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65 0
    stack := 112
    verified := verifyMessage_verified (verifyFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    spSafe := verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))) 0 },
  (Spec.MlDsa.verifyMessageCachedApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Message.verifyMessageCached (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87 0
    stack := 112
    verified := verifyMessage_verified (verifyFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := verifyMessage_spSafe (verify_spSafe (prims_okWith v)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) 0 },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Message.verifyMessageCached (Proof.MlDsa.verifyWithCacheName "mldsa44" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44 1
    stack := 112
    verified := verifyMessagePrepared_verified (verifyFn v (List.mem_cons_self ..)) (List.mem_cons_self ..)
      (verifyPrepared_sat (prims_okWith v) (List.mem_cons_self ..))
    spSafe := verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_self ..)) 1 },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Message.verifyMessageCached (Proof.MlDsa.verifyWithCacheName "mldsa65" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65 1
    stack := 112
    verified := verifyMessagePrepared_verified (verifyFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (verifyPrepared_sat (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..))) 1 },
  (Spec.MlDsa.preparedVerifyMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86_64.target {
    suffix := v.code.sfx
    code := Impl.MlDsa.X86_64.Message.verifyMessageCached (Proof.MlDsa.verifyWithCacheName "mldsa87" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Verify.verify (primsWith v.code) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87 1
    stack := 112
    verified := verifyMessagePrepared_verified (verifyFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (verifyPrepared_sat (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    spSafe := verifyMessage_spSafe (verify_spSafe (prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) 1 }]

def artifacts : List Artifact :=
  VG.Proof.Variants.MlDsaArith.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.MlDsa.X86_64.VerifyMessageCached

namespace VG.Artifacts.MlDsa.X86_64

def artifacts : List Artifact :=
  KeyGen.artifacts ++
  [
    Spec.MlDsa.pkTr44Api.artifact X86_64.target {
      code := Impl.MlDsa.X86_64.PkTr.pkTr Spec.MlDsa.mlDsa44
      stack := 32
      verified := Proof.MlDsa.X86_64.PkTr.pkTr44_verified },
    Spec.MlDsa.pkTr65Api.artifact X86_64.target {
      code := Impl.MlDsa.X86_64.PkTr.pkTr Spec.MlDsa.mlDsa65
      stack := 32
      verified := Proof.MlDsa.X86_64.PkTr.pkTr65_verified },
    Spec.MlDsa.pkTr87Api.artifact X86_64.target {
      code := Impl.MlDsa.X86_64.PkTr.pkTr Spec.MlDsa.mlDsa87
      stack := 32
      verified := Proof.MlDsa.X86_64.PkTr.pkTr87_verified }] ++
  PreparedKey.artifacts ++
  Sign.artifacts ++
  SignMessage.artifacts ++
  Verify.artifacts ++
  VerifyMessageCached.artifacts

end VG.Artifacts.MlDsa.X86_64
