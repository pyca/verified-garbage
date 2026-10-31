module

import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignFn
import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.MlDsa.X86_64.Message
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Sign
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inst
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignVerified
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Verified
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignFn
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignVerified
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
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Verified
public import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
public import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.HashCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCorrect
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseCCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseKCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseOCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.SignCT
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress

/-! # ML-DSA (FIPS 204) on x86-64: signing messages -/

@[expose] public section

namespace VG.Generic.MlDsaArith.X86_64.MlDsaSignMessage

open VG
open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.Sign (primsWith)
open VG.Proof.MlDsa.X86_64.Message (signFn signMessage_verified signMessage_spSafe)

def artifacts (v : ArithImpl) : List Artifact := [
  Spec.MlDsa.signMessage44Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.Message.signMessage (Spec.MlDsa.sign44Api.name ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa44) Spec.MlDsa.mlDsa44
    stack := 112
    verified := signMessage_verified (signFn v (List.mem_cons_self ..)) (List.mem_cons_self ..)
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl)) },
  Spec.MlDsa.signMessage65Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.Message.signMessage (Spec.MlDsa.sign65Api.name ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa65) Spec.MlDsa.mlDsa65
    stack := 112
    verified := signMessage_verified (signFn v (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl))) },
  Spec.MlDsa.signMessage87Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.Message.signMessage (Spec.MlDsa.sign87Api.name ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa87) Spec.MlDsa.mlDsa87
    stack := 112
    verified := signMessage_verified (signFn v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..)))) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    spSafe := signMessage_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl))) }]

end VG.Generic.MlDsaArith.X86_64.MlDsaSignMessage
