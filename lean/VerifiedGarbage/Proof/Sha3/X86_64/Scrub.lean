module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
meta import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks

public import VerifiedGarbage.Spec.Sha3.Instances
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha3.X86_64.Instances
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit
meta import VerifiedGarbage.Spec.Sha3.Instances
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sha3.X86_64.Instances
meta import VerifiedGarbage.Proof.Sha3.Stream
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit
import VerifiedGarbage.Proof.Sha3.PostOut
meta import VerifiedGarbage.Proof.Sha3.PostOut

/-!
# SHA-3 and SHAKE's functions on x86-64, without secret residue

Each instance's `update`, and SHAKE's `finalize` and `squeeze`, followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`), which clears the
registers and the granules of its stack that the residue analysis
(`X86_64.RTaint`) finds may hold secrets. Their postconditions read the
memory on return only within the buffers (`X86_64.Scrub.PostOut`,
`Proof/Sha3/PostOut.lean`).

SHA-3's fixed digest copy avoids generic squeezing. Its finalizer clears
the 680-byte stack with aligned stores after writing the digest.
-/

@[expose] public section

namespace VG.Proof.Sha3.X86_64.Scrub

open VG.Spec.Sha3 VG.X86_64 VG.X86_64.Scrub

theorem updateOut (rate stack : Nat) :
    PostOut (updateContract X86_64.abi rate stack) (updateSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.updatePost_out rate 64)

/-- A fixed digest's postcondition reads only its output buffer. -/
theorem finalizeOut (H : HashFn) (stack : Nat) (hlen : H.len < 2 ^ 64) :
    PostOut (finalizeContract X86_64.abi H stack) ((finalizeSig H.len).retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.finalizePost_out H 64 hlen)

theorem xofFinalizeOut (X : Xof) (stack : Nat) :
    PostOut (xofFinalizeContract X86_64.abi X stack) (xofFinalizeSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.xofFinalizePost_out X 64)

theorem xofSqueezeOut (X : Xof) (stack : Nat) :
    PostOut (xofSqueezeContract X86_64.abi X stack) (xofSqueezeSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.xofSqueezePost_out X)

/-! ## The registrations -/
def updateSha3_224Ks : List Nat := keep_for% Spec.Sha3.updateSha3_224Api.sig 8 (Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_224.rate) []

theorem updateSha3_224Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.updateSha3_224Api.sig 8 []) (Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_224.rate)
      h).any (RScrub.resOkB · 8 updateSha3_224Ks (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of updateSha3_224Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `updateSha3_224Api`'s function. -/
def updateSha3_224Reg : Registration Spec.Sha3.updateSha3_224Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_224.rate
    stack := 8
    verified := Proof.Sha3.X86_64.Instances.update_sha3_224 } (updateOut _ _) [] (pubOk_nil _)
    (some ⟨updateSha3_224Ks, updateSha3_224Ok⟩)
def updateSha3_256Ks : List Nat := keep_for% Spec.Sha3.updateSha3_256Api.sig 8 (Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_256.rate) []

theorem updateSha3_256Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.updateSha3_256Api.sig 8 []) (Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_256.rate)
      h).any (RScrub.resOkB · 8 updateSha3_256Ks (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of updateSha3_256Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `updateSha3_256Api`'s function. -/
def updateSha3_256Reg : Registration Spec.Sha3.updateSha3_256Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_256.rate
    stack := 8
    verified := Proof.Sha3.X86_64.Instances.update_sha3_256 } (updateOut _ _) [] (pubOk_nil _)
    (some ⟨updateSha3_256Ks, updateSha3_256Ok⟩)
def updateSha3_384Ks : List Nat := keep_for% Spec.Sha3.updateSha3_384Api.sig 8 (Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_384.rate) []

theorem updateSha3_384Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.updateSha3_384Api.sig 8 []) (Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_384.rate)
      h).any (RScrub.resOkB · 8 updateSha3_384Ks (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of updateSha3_384Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `updateSha3_384Api`'s function. -/
def updateSha3_384Reg : Registration Spec.Sha3.updateSha3_384Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_384.rate
    stack := 8
    verified := Proof.Sha3.X86_64.Instances.update_sha3_384 } (updateOut _ _) [] (pubOk_nil _)
    (some ⟨updateSha3_384Ks, updateSha3_384Ok⟩)
def updateSha3_512Ks : List Nat := keep_for% Spec.Sha3.updateSha3_512Api.sig 8 (Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_512.rate) []

theorem updateSha3_512Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.updateSha3_512Api.sig 8 []) (Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_512.rate)
      h).any (RScrub.resOkB · 8 updateSha3_512Ks (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of updateSha3_512Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `updateSha3_512Api`'s function. -/
def updateSha3_512Reg : Registration Spec.Sha3.updateSha3_512Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.update Spec.Sha3.hashSha3_512.rate
    stack := 8
    verified := Proof.Sha3.X86_64.Instances.update_sha3_512 } (updateOut _ _) [] (pubOk_nil _)
    (some ⟨updateSha3_512Ks, updateSha3_512Ok⟩)
def updateShake128Ks : List Nat := keep_for% Spec.Sha3.updateShake128Api.sig 8 (Impl.Sha3.X86_64.Instances.update Spec.Sha3.xofShake128.rate) []

theorem updateShake128Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.updateShake128Api.sig 8 []) (Impl.Sha3.X86_64.Instances.update Spec.Sha3.xofShake128.rate)
      h).any (RScrub.resOkB · 8 updateShake128Ks (Impl.Scrub.X86_64.chunks 8)) = true :=
  RScrub.Analysed.ok_of updateShake128Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `updateShake128Api`'s function. -/
def updateShake128Reg : Registration Spec.Sha3.updateShake128Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.update Spec.Sha3.xofShake128.rate
    stack := 8
    verified := Proof.Sha3.X86_64.Instances.update_shake128 } (updateOut _ _) [] (pubOk_nil _)
    (some ⟨updateShake128Ks, updateShake128Ok⟩)
def finalizeShake128Ks : List Nat := keep_for% Spec.Sha3.finalizeShake128Api.sig 656 (Impl.Sha3.X86_64.Instances.xofFinalize Spec.Sha3.xofShake128.rate) []

theorem finalizeShake128Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.finalizeShake128Api.sig 656 []) (Impl.Sha3.X86_64.Instances.xofFinalize Spec.Sha3.xofShake128.rate)
      h).any (RScrub.resOkB · 656 finalizeShake128Ks (Impl.Scrub.X86_64.chunks 656)) = true :=
  RScrub.Analysed.ok_of finalizeShake128Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `finalizeShake128Api`'s function. -/
def finalizeShake128Reg : Registration Spec.Sha3.finalizeShake128Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.xofFinalize Spec.Sha3.xofShake128.rate
    stack := 656
    verified := Proof.Sha3.X86_64.Instances.finalize_shake128 } (xofFinalizeOut _ _) [] (pubOk_nil _)
    (some ⟨finalizeShake128Ks, finalizeShake128Ok⟩)
def squeezeShake128Ks : List Nat := keep_for% Spec.Sha3.squeezeShake128Api.sig 656 (Impl.Sha3.X86_64.Instances.xofSqueeze Spec.Sha3.xofShake128.rate) []

theorem squeezeShake128Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.squeezeShake128Api.sig 656 []) (Impl.Sha3.X86_64.Instances.xofSqueeze Spec.Sha3.xofShake128.rate)
      h).any (RScrub.resOkB · 656 squeezeShake128Ks (Impl.Scrub.X86_64.chunks 656)) = true :=
  RScrub.Analysed.ok_of squeezeShake128Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `squeezeShake128Api`'s function. -/
def squeezeShake128Reg : Registration Spec.Sha3.squeezeShake128Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.xofSqueeze Spec.Sha3.xofShake128.rate
    stack := 656
    verified := Proof.Sha3.X86_64.Instances.squeeze_shake128 } (xofSqueezeOut _ _) [] (pubOk_nil _)
    (some ⟨squeezeShake128Ks, squeezeShake128Ok⟩)
def finalizeShake256Ks : List Nat := keep_for% Spec.Sha3.finalizeShake256Api.sig 656 (Impl.Sha3.X86_64.Instances.xofFinalize Spec.Sha3.xofShake256.rate) []

theorem finalizeShake256Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.finalizeShake256Api.sig 656 []) (Impl.Sha3.X86_64.Instances.xofFinalize Spec.Sha3.xofShake256.rate)
      h).any (RScrub.resOkB · 656 finalizeShake256Ks (Impl.Scrub.X86_64.chunks 656)) = true :=
  RScrub.Analysed.ok_of finalizeShake256Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `finalizeShake256Api`'s function. -/
def finalizeShake256Reg : Registration Spec.Sha3.finalizeShake256Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.xofFinalize Spec.Sha3.xofShake256.rate
    stack := 656
    verified := Proof.Sha3.X86_64.Instances.finalize_shake256 } (xofFinalizeOut _ _) [] (pubOk_nil _)
    (some ⟨finalizeShake256Ks, finalizeShake256Ok⟩)
def squeezeShake256Ks : List Nat := keep_for% Spec.Sha3.squeezeShake256Api.sig 656 (Impl.Sha3.X86_64.Instances.xofSqueeze Spec.Sha3.xofShake256.rate) []

theorem squeezeShake256Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.squeezeShake256Api.sig 656 []) (Impl.Sha3.X86_64.Instances.xofSqueeze Spec.Sha3.xofShake256.rate)
      h).any (RScrub.resOkB · 656 squeezeShake256Ks (Impl.Scrub.X86_64.chunks 656)) = true :=
  RScrub.Analysed.ok_of squeezeShake256Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `squeezeShake256Api`'s function. -/
def squeezeShake256Reg : Registration Spec.Sha3.squeezeShake256Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.xofSqueeze Spec.Sha3.xofShake256.rate
    stack := 656
    verified := Proof.Sha3.X86_64.Instances.squeeze_shake256 } (xofSqueezeOut _ _) [] (pubOk_nil _)
    (some ⟨squeezeShake256Ks, squeezeShake256Ok⟩)

/-- SHA3-224's finalizer, with its whole stack cleared after the digest is written. -/
def finalizeSha3_224Reg : Registration Spec.Sha3.finalizeSha3_224Api X86_64.target :=
  RScrub.withScrubAllC {
    code := Impl.Sha3.X86_64.Instances.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len
    verified := Proof.Sha3.X86_64.Instances.finalize_sha3_224 } (finalizeOut _ _ (by decide)) [8, 672]

/-- SHA3-256's finalizer, with its whole stack cleared after the digest is written. -/
def finalizeSha3_256Reg : Registration Spec.Sha3.finalizeSha3_256Api X86_64.target :=
  RScrub.withScrubAllC {
    code := Impl.Sha3.X86_64.Instances.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len
    verified := Proof.Sha3.X86_64.Instances.finalize_sha3_256 } (finalizeOut _ _ (by decide)) [8, 672]

/-- SHA3-384's finalizer, with its whole stack cleared after the digest is written. -/
def finalizeSha3_384Reg : Registration Spec.Sha3.finalizeSha3_384Api X86_64.target :=
  RScrub.withScrubAllC {
    code := Impl.Sha3.X86_64.Instances.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len
    verified := Proof.Sha3.X86_64.Instances.finalize_sha3_384 } (finalizeOut _ _ (by decide)) [8, 672]

/-- SHA3-512's finalizer, with its whole stack cleared after the digest is written. -/
def finalizeSha3_512Reg : Registration Spec.Sha3.finalizeSha3_512Api X86_64.target :=
  RScrub.withScrubAllC {
    code := Impl.Sha3.X86_64.Instances.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len
    verified := Proof.Sha3.X86_64.Instances.finalize_sha3_512 } (finalizeOut _ _ (by decide)) [8, 672]

end VG.Proof.Sha3.X86_64.Scrub
