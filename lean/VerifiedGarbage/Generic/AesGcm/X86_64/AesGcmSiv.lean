module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Verified
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Verified
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.SealVerified
public import VerifiedGarbage.Generic.AesGcm.X86_64.AesGcm
import VerifiedGarbage.Proof.Framework.X86_64.HighRegs

/-!
# AES-GCM-SIV (RFC 8452) on x86-64

A generic file (see `TCB/Emit.lean`): the artifacts it lists, calling the
implementations `v` of `vg_aes_ctr32`, `vg_aes_expand_key` and `vg_ghash`
(those of AES-GCM), and the implementation of `vg_aes_encrypt_blocks` that
goes with `v`'s `vg_aes_ctr32` (`ecbOf`), are emitted once for each combination
(`Variants/AesGcm/X86_64/`), named with its suffix (e.g.
`vg_aes_gcm_siv_seal_aesni_pclmul`), and need the CPU features of the four.
They do not call AES-GCM's interleaved loops, so the instances of
combinations differing only in those are the same code under other names,
which keeps every instance of a combination callable together.

`open` deciphers and computes POLYVAL in one interleaved loop
(`Impl.AesGcmSiv.X86_64Stitch`) from 256 bytes of data on with
the implementations whose `vg_aes_ctr32` uses VAES and whose `vg_ghash` uses
VPCLMULQDQ (`sivStitch`), whose CPU features that loop needs; with them,
`seal` computes POLYVAL and enciphers the data's 256-byte groups in loops of
its own.

Each keeps its working space in a frame of 3848 bytes on the stack
(`Proof/AesGcmSiv/X86_64/Verified.lean`), below which its calls use 8 bytes:
the return address of a call of one of the four, which make no calls.
-/

@[expose] public section

namespace VG.Generic.AesGcm.X86_64.AesGcmSiv

open VG.Proof.AesGcm.X86_64 (GcmImpl GcmVariant)
open VG.Proof.AesGcmSiv.X86_64

/-- Which implementations an instance calls. -/
def note (v : GcmImpl) : String :=
  "This implementation encrypts with `" ++ (ecbOf v).enc.name ++ "` and `" ++ v.ctr.callee.name ++
    "` (and expands keys with `" ++ v.key.fn.name ++ "`) and computes POLYVAL with `" ++ v.gh.fn.name ++ "`."

/-- The implementation of `vg_aes_encrypt_blocks` they call. -/
def ecbFn (v : GcmImpl) : Impl.AesGcm.X86_64.Fn := ⟨(ecbOf v).enc.name, (ecbOf v).enc.code⟩

/-- Whether `open` interleaves counter mode and POLYVAL: with VAES and
VPCLMULQDQ (and so AVX2) in `v`'s callees. -/
def sivStitch (v : GcmImpl) : Bool := v.ctr.features.contains "vaes" && v.gh.features.contains "vpclmulqdq"

/-- The code of `open` for `v`. -/
def openCode (v : GcmImpl) : Prog X86_64.isa :=
  if sivStitch v then Impl.AesGcmSiv.X86_64Stitch.«open» v.callees (ecbFn v) (sivWide v)
  else Impl.AesGcmSiv.X86_64.«open» v.callees (ecbFn v) (sivWide v)

/-- The code of `seal` for `v`. -/
def sealCode (v : GcmImpl) : Prog X86_64.isa :=
  if sivStitch v then Impl.AesGcmSiv.X86_64Stitch.«seal» v.callees (ecbFn v) (sivWide v)
  else Impl.AesGcmSiv.X86_64.«seal» v.callees (ecbFn v) (sivWide v)

theorem sealCode_framed (v : GcmImpl) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (sealCode v))
      (Spec.GcmSiv.sealContract X86_64.abi 3856) := by
  unfold sealCode; split
  · exact sealS_framed v (ecbOf v) (sivWide v)
  · exact seal_framed v (ecbOf v) (sivWide v)

theorem sealCode_spSafe (v : GcmImpl) : (sealCode v).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold sealCode; split
  · exact sealS_spSafe v (ecbOf v) (sivWide v)
  · exact seal_spSafe v (ecbOf v) (sivWide v)

theorem openCode_framed (v : GcmImpl) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (openCode v))
      (Spec.GcmSiv.openContract X86_64.abi 3856) := by
  unfold openCode; split
  · exact openS_framed v (ecbOf v) (sivWide v)
  · exact open_framed v (ecbOf v) (sivWide v)

theorem openCode_spSafe (v : GcmImpl) : (openCode v).all (fun i => !X86_64.isa.writesSp i) = true := by
  unfold openCode; split
  · exact openS_spSafe v (ecbOf v) (sivWide v)
  · exact open_spSafe v (ecbOf v) (sivWide v)

/-- The artifacts calling the implementations `v`. -/
def artifactsOf (v : GcmImpl) : List Artifact := [
  { Spec.GcmSiv.sealApi with
    name := Spec.GcmSiv.sealApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.GcmSiv.sealApi.doc (notes := [note v])
    code := Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (sealCode v)
    contract := Spec.GcmSiv.sealContract X86_64.abi 3856
    stack := 3856
    verified := sealCode_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (sealCode_spSafe v)
    features := features v },
  { Spec.GcmSiv.openApi with
    name := Spec.GcmSiv.openApi.name ++ v.suffix
    target := X86_64.target
    doc := Spec.GcmSiv.openApi.doc (notes := [note v,
      "It compares the tags and overwrites the data with zeros without a branch on the result."])
    code := Impl.StackScratch.X86_64.withStackArgScratch 3848 2 (openCode v)
    contract := Spec.GcmSiv.openContract X86_64.abi 3856
    stack := 3856
    verified := openCode_framed v
    spSafe := X86_64.withStackArgScratch_spSafe (openCode_spSafe v)
    features := features v }]

/-- The artifacts of a variant, from the implementations it names. -/
def artifacts (v : GcmVariant) : List Artifact := artifactsOf v.impl

end VG.Generic.AesGcm.X86_64.AesGcmSiv
