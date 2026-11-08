module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignFn
import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.MlDsa.X86_64.PreparedKey.Sat
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Prims
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
public import VerifiedGarbage.Impl.MlDsa.X86_64.Message
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Sign
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignVerified
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Verified
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.MlDsa.Pack.Arith
public import VerifiedGarbage.Proof.MlDsa.Pack.Stream
public import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.HashCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCorrect
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseCCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseDCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseKCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseOCT
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.SignCT
public import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
public import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
public import VerifiedGarbage.TCB.X86_64.Print

/-! # ML-DSA (FIPS 204) on x86-64: signing messages -/

@[expose] public section

namespace VG.Generic.MlDsaArith.X86_64.MlDsaSignMessage

open VG
open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.Sign (primsWith)
open VG.Proof.MlDsa.X86_64.Message (signFn signMessage_verified signMessage_spSafe signMessagePrepared_verified
  signPrepared_sat)

def artifacts (v : ArithImpl) : List Artifact := [
  Spec.MlDsa.signMessage44Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.Message.signMessage (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44 0
    stack := 112
    verified := signMessage_verified (signFn v (List.mem_cons_self ..)) (List.mem_cons_self ..)
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl)) 0 },
  Spec.MlDsa.signMessage65Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.Message.signMessage (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65 0
    stack := 112
    verified := signMessage_verified (signFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl))) 0 },
  Spec.MlDsa.signMessage87Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.Message.signMessage (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87 0
    stack := 112
    verified := signMessage_verified (signFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl))) 0 },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa44 "mldsa44" "ML-DSA-44").artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.Message.signMessage (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44 1
    stack := 112
    verified := signMessagePrepared_verified (signFn v (List.mem_cons_self ..)) (List.mem_cons_self ..)
      (signPrepared_sat (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_self ..))
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl)) 1 },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa65 "mldsa65" "ML-DSA-65").artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.Message.signMessage (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65 1
    stack := 112
    verified := signMessagePrepared_verified (signFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..))) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (signPrepared_sat (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl))) 1 },
  (Spec.MlDsa.preparedSignMessageApi Spec.MlDsa.mlDsa87 "mldsa87" "ML-DSA-87").artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.Message.signMessage (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87 1
    stack := 112
    verified := signMessagePrepared_verified (signFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (signPrepared_sat (Proof.MlDsa.X86_64.Verify.prims_okWith v) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl))) 1 }]

end VG.Generic.MlDsaArith.X86_64.MlDsaSignMessage
