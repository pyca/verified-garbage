module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Verified
import Mathlib.Tactic.Conv
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Sign
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inst
public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignFn
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Proof.Framework.X86_64.Lit
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
public import VerifiedGarbage.TCB.X86_64.Print

/-! # ML-DSA (FIPS 204) on x86-64: signing -/

@[expose] public section

namespace VG.Generic.MlDsaArith.X86_64.MlDsaSign

open VG.Proof.MlDsa.X86_64 (ArithImpl)
open VG.Proof.MlDsa.X86_64.Sign (primsWith)

def artifacts (v : ArithImpl) : List Artifact := [
  Spec.MlDsa.sign44Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.Sign.entry (Proof.MlDsa.signWithCacheName "mldsa44" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa44) 0
    stack := 40
    verified := Proof.MlDsa.X86_64.Message.signEntry_verified v (List.mem_cons_self ..) _
    spSafe := Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inl rfl)) 0 },
  Spec.MlDsa.sign65Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.Sign.entry (Proof.MlDsa.signWithCacheName "mldsa65" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa65) 0
    stack := 40
    verified := Proof.MlDsa.X86_64.Message.signEntry_verified v (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _
    spSafe := Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inl rfl))) 0 },
  Spec.MlDsa.sign87Api.artifact X86_64.target {
    suffix := v.code.sfx
    features := v.features
    code := Impl.MlDsa.X86_64.Sign.entry (Proof.MlDsa.signWithCacheName "mldsa87" ++ v.code.sfx)
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code) Spec.MlDsa.mlDsa87) 0
    stack := 40
    verified := Proof.MlDsa.X86_64.Message.signEntry_verified v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) _
    spSafe := Proof.MlDsa.X86_64.Message.signEntry_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v (.inr (.inr rfl))) 0 }]

end VG.Generic.MlDsaArith.X86_64.MlDsaSign
