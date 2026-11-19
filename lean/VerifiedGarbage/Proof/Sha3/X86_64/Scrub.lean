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

Each instance's `absorb`, and SHAKE's `finalize` and `squeeze`, followed by
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

/-! ## `absorb`: `update` with its working space on the stack -/

theorem absorbOut (rate stack : Nat) :
    PostOut (absorbContract X86_64.abi rate stack) (absorbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.absorbPost_out rate 64)

theorem stream_sp : Impl.Sha3.X86_64.Stream.absorb.all (fun i => !X86_64.isa.writesSp i) = true := by
  lit_decide

theorem stream_xd : Impl.Sha3.X86_64.Stream.absorb.x86_64Depth ≤ 8 := by lit_decide

/-- A state satisfying `absorbContract`'s precondition (with no data), with
656 bytes of stack. -/
def absorbSat : X86_64.State := { Proof.Sha3.X86_64.Instances.updateSat with wr := [⟨0x1000, 200⟩] }

theorem absorbSat_pre {rate : Nat} (h0 : 0 < rate) :
    ∃ s, (absorbContract X86_64.abi rate 656).pre s := by
  refine ⟨absorbSat, ?_⟩
  sig_pre [absorbContract, absorbSig, absorbPre, absorbPost, X86_64.abi, X86_64.argRegs, absorbSat,
    Proof.Sha3.X86_64.Instances.updateSat, Proof.Sha3.X86_64.Stream.Absorb.sat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact h0

/-- `vg_<f>_absorb`: `update`, with its working space `scratch` in a frame of
648 bytes on the stack (`withStackScratch`), which `update`'s contract with
`scratch` (`Sig.scratchContract`, by `rfl` `updateContract`) proves
(`Verified.stackScratch`). -/
theorem absorb_verified {rate : Nat} (hr : rate ∈ rates)
    (hsp : (Impl.Sha3.X86_64.Instances.update rate).all (fun i => !X86_64.isa.writesSp i) = true)
    (hd : (Impl.Sha3.X86_64.Instances.update rate).x86_64Depth ≤ 8) :
    Verified X86_64.target (Impl.Sha3.X86_64.Instances.absorb rate) (absorbContract X86_64.abi rate 656) :=
  X86_64.Verified.stackScratch (sig := absorbSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := absorbPre rate X86_64.abi.ptrBits) (post := absorbPost rate X86_64.abi.ptrBits)
    (wa := true) (stack := 8) (bytes := 648)
    (Proof.Sha3.X86_64.Instances.update_verified hr) (by decide) (by decide) (by decide) hsp hd
    (Proof.Sha3.PostOut.absorbPost_out rate _)
    (absorbSat_pre (by simp [rates] at hr; omega_using [hr]))

theorem absorb_sha3_224 :
    Verified X86_64.target (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_224.rate)
      (absorbContract X86_64.abi Spec.Sha3.hashSha3_224.rate 656) :=
  absorb_verified (by decide)
    (by lit_decide) (by lit_decide)

theorem absorb_sha3_256 :
    Verified X86_64.target (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_256.rate)
      (absorbContract X86_64.abi Spec.Sha3.hashSha3_256.rate 656) :=
  absorb_verified (by decide)
    (by lit_decide) (by lit_decide)

theorem absorb_sha3_384 :
    Verified X86_64.target (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_384.rate)
      (absorbContract X86_64.abi Spec.Sha3.hashSha3_384.rate 656) :=
  absorb_verified (by decide)
    (by lit_decide) (by lit_decide)

theorem absorb_sha3_512 :
    Verified X86_64.target (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_512.rate)
      (absorbContract X86_64.abi Spec.Sha3.hashSha3_512.rate 656) :=
  absorb_verified (by decide)
    (by lit_decide) (by lit_decide)

theorem absorb_shake128 :
    Verified X86_64.target (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.xofShake128.rate)
      (absorbContract X86_64.abi Spec.Sha3.xofShake128.rate 656) :=
  absorb_verified (by decide)
    (by lit_decide) (by lit_decide)

/-! ## The registrations -/
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


def absorbSha3_224Ks : List Nat := keep_for% Spec.Sha3.absorbSha3_224Api.sig 656 (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_224.rate) []

theorem absorbSha3_224Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.absorbSha3_224Api.sig 656 []) (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_224.rate)
      h).any (RScrub.resOkB · 656 absorbSha3_224Ks (Impl.Scrub.X86_64.chunks 656)) = true :=
  RScrub.Analysed.ok_of absorbSha3_224Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `absorbSha3_224Api`'s function. -/
def absorbSha3_224Reg : Registration Spec.Sha3.absorbSha3_224Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_224.rate
    stack := 656
    verified := absorb_sha3_224 } (absorbOut _ _) [] (pubOk_nil _)
    (some ⟨absorbSha3_224Ks, absorbSha3_224Ok⟩)

def absorbSha3_256Ks : List Nat := keep_for% Spec.Sha3.absorbSha3_256Api.sig 656 (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_256.rate) []

theorem absorbSha3_256Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.absorbSha3_256Api.sig 656 []) (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_256.rate)
      h).any (RScrub.resOkB · 656 absorbSha3_256Ks (Impl.Scrub.X86_64.chunks 656)) = true :=
  RScrub.Analysed.ok_of absorbSha3_256Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `absorbSha3_256Api`'s function. -/
def absorbSha3_256Reg : Registration Spec.Sha3.absorbSha3_256Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_256.rate
    stack := 656
    verified := absorb_sha3_256 } (absorbOut _ _) [] (pubOk_nil _)
    (some ⟨absorbSha3_256Ks, absorbSha3_256Ok⟩)

def absorbSha3_384Ks : List Nat := keep_for% Spec.Sha3.absorbSha3_384Api.sig 656 (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_384.rate) []

theorem absorbSha3_384Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.absorbSha3_384Api.sig 656 []) (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_384.rate)
      h).any (RScrub.resOkB · 656 absorbSha3_384Ks (Impl.Scrub.X86_64.chunks 656)) = true :=
  RScrub.Analysed.ok_of absorbSha3_384Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `absorbSha3_384Api`'s function. -/
def absorbSha3_384Reg : Registration Spec.Sha3.absorbSha3_384Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_384.rate
    stack := 656
    verified := absorb_sha3_384 } (absorbOut _ _) [] (pubOk_nil _)
    (some ⟨absorbSha3_384Ks, absorbSha3_384Ok⟩)

def absorbSha3_512Ks : List Nat := keep_for% Spec.Sha3.absorbSha3_512Api.sig 656 (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_512.rate) []

theorem absorbSha3_512Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.absorbSha3_512Api.sig 656 []) (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_512.rate)
      h).any (RScrub.resOkB · 656 absorbSha3_512Ks (Impl.Scrub.X86_64.chunks 656)) = true :=
  RScrub.Analysed.ok_of absorbSha3_512Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `absorbSha3_512Api`'s function. -/
def absorbSha3_512Reg : Registration Spec.Sha3.absorbSha3_512Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.hashSha3_512.rate
    stack := 656
    verified := absorb_sha3_512 } (absorbOut _ _) [] (pubOk_nil _)
    (some ⟨absorbSha3_512Ks, absorbSha3_512Ok⟩)

def absorbShake128Ks : List Nat := keep_for% Spec.Sha3.absorbShake128Api.sig 656 (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.xofShake128.rate) []

theorem absorbShake128Ok : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Sha3.absorbShake128Api.sig 656 []) (Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.xofShake128.rate)
      h).any (RScrub.resOkB · 656 absorbShake128Ks (Impl.Scrub.X86_64.chunks 656)) = true :=
  RScrub.Analysed.ok_of absorbShake128Ks (by taint_decide)

open VG.X86_64.RScrub in
/-- `absorbShake128Api`'s function. -/
def absorbShake128Reg : Registration Spec.Sha3.absorbShake128Api X86_64.target :=
  withScrub {
    code := Impl.Sha3.X86_64.Instances.absorb Spec.Sha3.xofShake128.rate
    stack := 656
    verified := absorb_shake128 } (absorbOut _ _) [] (pubOk_nil _)
    (some ⟨absorbShake128Ks, absorbShake128Ok⟩)

end VG.Proof.Sha3.X86_64.Scrub
