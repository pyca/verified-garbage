module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Decrypt
public import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
public import VerifiedGarbage.Proof.Sha256.X86.Shared

/-! # SHA-256 and HMAC callees for each x86 SHA-256 backend

The scratch-taking APIs use the disjoint workspace area at offset 3072.
The SHA-256 API reserves 608 bytes there; HMAC needs 832. Keeping this space in the
caller's workspace avoids allocating additional frames around the hashes.
-/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86
open VG.Proof.Sha256.X86.Variants (Backend)

def hashFns (v : Backend) : Impl.RsaPkcs1Enc.X86.Decrypt.Fns where
  initN := Spec.Sha256.initApi.name
  initC := Impl.Sha256.X86.Stream.init
  updN := Spec.Sha256.updateScratchApi.name ++ v.suffix
  updC := v.stream.upd
  finN := Spec.Sha256.finalizeScratchApi.name ++ v.suffix
  finC := v.stream.fin
  hiN := Spec.Hmac.sha256I.initScratchApi.name ++ v.suffix
  hiC := v.M.hmacInit
  hfN := Spec.Hmac.sha256I.finalizeScratchApi.name ++ v.suffix
  hfC := v.M.hmacFin

theorem init_verified (v : Backend) : Verified target (hashFns v).initC (Spec.Sha256.initContract abi) :=
  Proof.Sha256.X86.Shared.init

theorem update_verified (v : Backend) : Verified target (hashFns v).updC
    (Spec.Sha256.updateScratchContract abi 20) :=
  (Proof.Sha256.X86.Shared.updateWide_of v.stream.updOK
    Proof.Sha256.X86.Shared.updateWide_implies.sat_left).of_implies Proof.Sha256.X86.Shared.updateWide_implies

theorem finalize_verified (v : Backend) : Verified target (hashFns v).finC
    (Spec.Sha256.finalizeScratchContract abi 20) :=
  (Proof.Sha256.X86.Shared.finalizeWide_of v.stream.finOK
    Proof.Sha256.X86.Shared.finalizeWide_implies.sat_left).of_implies Proof.Sha256.X86.Shared.finalizeWide_implies

theorem hmacInit_verified (v : Backend) :
    Verified target (hashFns v).hiC (Spec.Hmac.sha256I.initScratchContract abi 48) := v.hmacInit

theorem hmacFinalize_verified (v : Backend) :
    Verified target (hashFns v).hfC (Spec.Hmac.sha256I.finalizeScratchContract abi 48) := v.hmacFin

end VG.Proof.RsaPkcs1Enc.X86.Dec
