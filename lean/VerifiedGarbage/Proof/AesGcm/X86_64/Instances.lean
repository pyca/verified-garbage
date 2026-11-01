module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.StreamCallee
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.GatherCallee
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.GatherSplit
public import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.VerifiedP
public import VerifiedGarbage.Proof.AesGcm.X86_64.Variant
public import VerifiedGarbage.Proof.AesGcm.X86_64.GhashImpls
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Field
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.GatherSeal
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.VerifiedP
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.SealFin
import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.Ok
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Ok
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Ct
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.OkP
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Ok
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Short
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.StreamTo
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.BlocksTo
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Gather
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.BlocksVerified
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerifiedP
public import VerifiedGarbage.Spec.Gcm.Prepared16
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.StreamCallee
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.GatherCallee
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.GatherSplit
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.GatherSeal
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.Short
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.Split
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.StreamTo
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.BlocksTo
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.Gather
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.BlocksVerified

/-!
# AES-GCM on x86-64: the functions a variant's artifacts are built from

The interleaved loops a variant names, with their proofs (which import the
algebra of `Proof/Gcm/Poly.lean`, so that the variants need not), the
implementations a variant names, resolved (`GcmVariant.impl`), and the
instances of the functions its callers call (`sealFn`, `toFn`, …), with their
proofs, for `Generic/AesGcm/X86_64/AesGcm.lean`; and the lengths at which
`vg_aes_gcm_seal_gather` changes path (`copyBelow`, `splitFrom`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

/-- The loops named `n` interleave counter mode and GHASH correctly. -/
theorem StitchName.ok : (n : StitchName) → Proof.Gcm.X86_64.Stitch.StitchOk n.enc n.dec
  | .vaes => Proof.Gcm.X86_64.Stitch.stitch_ok
  | .vaesAvx512 => Proof.Gcm.X86_64.StitchZ.stitch_ok
  | .aesniAvx => Proof.Gcm.X86_64.StitchAvx8.stitch_ok

/-- The encryption loop named `n`, if it takes all the blocks, meets its
contract for any number of them from 16 on. -/
theorem StitchName.okFull : (n : StitchName) → n.full = true → ∀ s₀, Proof.Gcm.X86_64.Stitch.SPre s₀ →
    WP X86_64.isa n.enc s₀ (Proof.Gcm.X86_64.Stitch.EPost s₀)
  | .aesniAvx, _ => fun _ hp => Proof.Gcm.X86_64.StitchAvx8.enc_ok hp
  | .vaes, h => absurd h (by decide)
  | .vaesAvx512, h => absurd h (by decide)

/-- The loops `p` names, with their proof. -/
def StitchPart.impl (p : StitchPart) : StitchImpl :=
  ⟨p.suffix, p.features, p.name.enc, p.name.dec, p.name.ok, p.name.full, p.name.okFull, p.encP, p.decP⟩

/-- The loops named `n` for a key context of `vg_aes_gcm_init_precomputed`
interleave counter mode and GHASH correctly. -/
theorem StitchName.okP : (n : StitchName) →
    Proof.Gcm.X86_64.Stitch.StitchOkM Proof.Gcm.X86_64.Stitch.CtxMode.powers n.encP n.decP
  | .vaes => Proof.Gcm.X86_64.Stitch.stitch_ok.toM _
  | .vaesAvx512 => Proof.Gcm.X86_64.StitchZP.stitchP_ok.toM
  | .aesniAvx => Proof.Gcm.X86_64.StitchAvx8.stitch_ok.toM _

/-- The loops `p` names for a key context of `vg_aes_gcm_init_precomputed`,
with their proof, if they read the powers of the hash subkey from it. -/
def StitchPart.implP (p : StitchPart) : Option (StitchCode Proof.Gcm.X86_64.Stitch.CtxMode.powers) :=
  p.pieceP.map fun q => ⟨p.name.encP, p.name.decP, false, false, false, false, false, p.name.encP, p.name.decP,
    p.name.okP, Proof.Gcm.X86_64.Stitch.StitchOkSmall.of16 _ _ _, q.enc, q.dec, q.enc, q.dec⟩

/-- The out-of-place loops named `n` interleave counter mode and GHASH
correctly. -/
theorem StitchToName.ok : (n : StitchToName) → (M : Proof.Gcm.X86_64.Stitch.CtxMode) →
    Proof.Gcm.X86_64.Stitch.StitchToOkM M n.enc (if n.full then 1 else 16)
  | .vaes, M => Proof.Gcm.X86_64.StitchTo.stitchTo_ok M
  | .vaesAvx512, M => Proof.Gcm.X86_64.StitchZTo.stitchTo_ok M
  | .aesniAvx, M => Proof.Gcm.X86_64.StitchAvx8.stitchTo_ok M

/-- The out-of-place loops named `n` for a key context of
`vg_aes_gcm_init_precomputed` interleave counter mode and GHASH correctly. -/
theorem StitchToName.okP : (n : StitchToName) →
    Proof.Gcm.X86_64.Stitch.StitchToOkM Proof.Gcm.X86_64.Stitch.CtxMode.powers n.encP
  | .vaes => Proof.Gcm.X86_64.StitchTo.stitchTo_ok _
  | .vaesAvx512 => Proof.Gcm.X86_64.StitchZTo.stitchToP_ok
  | .aesniAvx => fun s₀ hp _ => Proof.Gcm.X86_64.StitchAvx8.stitchTo_ok _ s₀ hp (Nat.mod_one _)

/-- The out-of-place loops a variant names, with their proof. -/
def GcmVariant.stitchTo (v : GcmVariant) : Option (StitchToCode Proof.Gcm.X86_64.Stitch.CtxMode.base) :=
  (v.stitch.bind (·.toPart)).map fun p => ⟨p.name.enc, p.name.full, p.name.ok _, p.piece⟩

/-- The out-of-place loops a variant names for a key context of
`vg_aes_gcm_init_precomputed`, with their proof. -/
def GcmVariant.stitchToP (v : GcmVariant) : Option (StitchToCode Proof.Gcm.X86_64.Stitch.CtxMode.powers) :=
  (v.stitch.bind (·.toPart)).bind fun p => p.pieceP.map fun q => ⟨p.name.encP, false, p.name.okP, q.enc⟩

/-- The implementations a variant calls. -/
def GcmVariant.impl (v : GcmVariant) : GcmImpl :=
  ⟨v.ctr, v.key, v.gh.impl, v.stitch.map StitchPart.impl, v.stitch.bind StitchPart.implP,
    v.stitch.any (·.name.short), v.stitch.any (·.name.fin), v.stitch.bind (·.name.onePass)⟩

/-- Prepared-context versions of each named interleaved loop (encrypting any
number of blocks from 16 on if `fullR`). -/
theorem StitchName.okR : (n : StitchName) →
    Proof.Gcm.X86_64.Stitch.StitchOkM Proof.Gcm.X86_64.Stitch.CtxMode.prepared n.encR n.decR
      (if n.fullR then 1 else 16) (if n.fullDR then 1 else 16)
  | .vaes => Proof.Gcm.X86_64.StitchR.stitchR_ok.weaken (by decide) (by decide)
  | .vaesAvx512 => Proof.Gcm.X86_64.StitchZH.stitchR_ok.weaken (by decide) (by decide)
  | .aesniAvx => Proof.Gcm.X86_64.StitchAvx8.stitchR_ok

/-- The loops `fullBody` runs on fewer than 16 blocks (from 1 on if
`smallR`). -/
theorem StitchName.okRS : (n : StitchName) →
    Proof.Gcm.X86_64.Stitch.StitchOkSmall Proof.Gcm.X86_64.Stitch.CtxMode.prepared n.encRS n.decRS
      (if n.smallR then 1 else 16) (if n.smallR then 1 else 16)
  | .vaes => Proof.Gcm.X86_64.StitchR.stitchR_ok.small
  | .vaesAvx512 => Proof.Gcm.X86_64.StitchZH.stitchR_ok.small
  | .aesniAvx => Proof.Gcm.X86_64.StitchAvx8.stitchRS_ok

/-- The static and constant-time facts of `encRS` and `decRS`: `encR`'s and
`decR`'s, but for the AES-NI loops'. -/
theorem StitchName.pieceRS : (n : StitchName) → PieceR n →
    Piece n.encRS true n.fullR ∧ Piece n.decRS true n.fullDR
  | .vaes, q => ⟨q.enc, q.dec⟩
  | .vaesAvx512, q => ⟨q.enc, q.dec⟩
  | .aesniAvx, _ => ⟨Proof.Gcm.X86_64.StitchAvx8.encRS_piece, Proof.Gcm.X86_64.StitchAvx8.decRS_piece⟩

def GcmVariant.stitchR (v : GcmVariant) : Option (StitchCode Proof.Gcm.X86_64.Stitch.CtxMode.prepared true) :=
  v.stitch.bind fun p => p.pieceR.map fun q =>
    ⟨p.name.encR, p.name.decR, p.name.fullR, p.name.fullDR, p.name.smallR, p.name.smallR, p.name.small4R,
      p.name.encRS, p.name.decRS, p.name.okR, p.name.okRS, q.enc, q.dec, (p.name.pieceRS q).1, (p.name.pieceRS q).2⟩

theorem StitchToName.okR : (n : StitchToName) →
    Proof.Gcm.X86_64.Stitch.StitchToOkM Proof.Gcm.X86_64.Stitch.CtxMode.prepared n.encR
      (if n.fullR then 1 else 16)
  | .vaes => Proof.Gcm.X86_64.StitchR.stitchTo_ok
  | .vaesAvx512 => Proof.Gcm.X86_64.StitchZHTo.stitchToR_ok
  | .aesniAvx => Proof.Gcm.X86_64.StitchAvx8.stitchToR_ok

def GcmVariant.stitchToR (v : GcmVariant) : Option (StitchToCode Proof.Gcm.X86_64.Stitch.CtxMode.prepared true) :=
  (v.stitch.bind (·.toPart)).bind fun p => p.pieceR.map fun q => ⟨p.name.encR, p.name.fullR, p.name.okR, q.enc⟩

/-- The instance of `vg_aes_gcm_encrypt_blocks_to` of a variant. -/
def blkTo (v : GcmVariant) : StreamTo.BlkToFn Proof.Gcm.X86_64.Stitch.CtxMode.base :=
  .ofBlocks ("vg_aes_gcm_encrypt_blocks_to" ++ v.impl.suffix) v.impl.blkB v.stitchTo

/-- The instance of `vg_aes_gcm_encrypt_blocks_to_precomputed` of a variant. -/
def blkToP (v : GcmVariant) : StreamTo.BlkToFn Proof.Gcm.X86_64.Stitch.CtxMode.powers :=
  .ofBlocks ("vg_aes_gcm_encrypt_blocks_to_precomputed" ++ v.impl.suffix) v.impl.blkP v.stitchToP

/-- The instance of `vg_aes_gcm_stream_encrypt` calling the implementations `v`. -/
def encFn (v : GcmImpl) : StreamTo.EncFn Proof.Gcm.X86_64.Stitch.CtxMode.base :=
  .ofBase ⟨Spec.Gcm.streamEncryptApi.name ++ v.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt v.callees)⟩
    (streamEncrypt_framed v) (X86_64.withStackArgScratch_spSafe (streamEncrypt_spSafe v))
    (StreamTo.framed_xdepth (streamEncrypt_xdepth v)) (StreamTo.framed_mx (streamEncrypt_mx v))

/-- The instance of `vg_aes_gcm_stream_encrypt_precomputed` calling the
implementations `v`. -/
def encFnP (v : GcmImpl) : StreamTo.EncFn Proof.Gcm.X86_64.Stitch.CtxMode.powers :=
  .ofPowers ⟨Spec.Gcm.streamEncryptPrecomputedApi.name ++ v.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2584 1
        (Impl.AesGcm.X86_64.streamEncrypt (v.withBlk v.blkP))⟩
    (streamEncryptP_framed v) (X86_64.withStackArgScratch_spSafe (streamEncryptM_spSafe v v.blkP))
    (StreamTo.framed_xdepth (streamEncryptM_xdepth v v.blkP)) (StreamTo.framed_mx (streamEncryptM_mx v v.blkP))

/-- Below how many bytes `vg_aes_gcm_seal_gather` takes its short path
(copying the text to the output and calling `vg_aes_gcm_seal`, or, from a
first slice holding all the whole blocks, `vg_aes_gcm_seal_split`), rather
than the streaming functions, by the out-of-place interleaved loops a variant
has (`GcmVariant.stitchTo`), as measured on a VAES and AVX-512 Xeon: on
512-bit registers, below 48 blocks, where the streaming functions' calls
cost more than the copy saves; on 256-bit registers, below 16 KiB, where a
slice ending within a block, which the streaming functions buffer, costs
more than the copy saves; and on 128-bit registers (AES-NI and AVX), below
3 KiB, as measured on an AMD EPYC 7763 and a Xeon, where a text of two
slices, the first ending within a block, gains from the streaming functions
from about 3 KiB on. Without them, the streaming path copies the blocks too,
so all texts but those of 2 GiB or more (where the cost of its calls is
negligible) take the copy. -/
def copyBelow (v : GcmVariant) : Nat :=
  match ((v.stitch.bind (·.toPart)).map (·.name) : Option StitchToName) with
  | some .vaesAvx512 => 768
  | some .vaes => 16384
  | some .aesniAvx => 3072
  | none => 2 ^ 31 - 1

theorem copyBelow_lt (v : GcmVariant) : copyBelow v < 2 ^ 31 := by
  unfold copyBelow; split <;> decide

/-- From how many bytes a first slice holding all the whole blocks of a text
on `vg_aes_gcm_seal_gather`'s short path is sealed where it is by
`vg_aes_gcm_seal_split`, rather than copied with the rest and sealed by
`vg_aes_gcm_seal`: without out-of-place interleaved loops, never (their
`vg_aes_gcm_encrypt_blocks_to` copies the blocks and calls
`vg_aes_gcm_encrypt_blocks` anyway); with them, from as many bytes as their
loop needs to beat the copy and `vg_aes_gcm_seal`'s fewer calls, measured by
the Benchmarks workflow on AMD and Intel runners. A 600-byte TLS record's
text was sealed no faster from where it is with VAES or AVX-512, and a
1350-byte one faster; with AES-NI and AVX both were faster. With AVX-512 that
leaves the texts the gathering would otherwise stream (`copyBelow` less a
block). -/
def splitFrom (v : GcmVariant) : Nat :=
  match ((v.stitch.bind (·.toPart)).map (·.name) : Option StitchToName) with
  | some .vaesAvx512 => 752
  | some .vaes => 1024
  | some .aesniAvx => 384
  | none => 2 ^ 31 - 17

theorem splitFrom_pos (v : GcmVariant) : 1 ≤ splitFrom v := by
  unfold splitFrom; split <;> decide

theorem splitFrom_le (v : GcmVariant) : splitFrom v + 16 ≤ copyBelow v := by
  unfold splitFrom copyBelow; split <;> simp_all <;> decide

/-- Whether `vg_aes_gcm_seal_gather_prepared` seals a TLS record's text from
its first slice by `vg_aes_gcm_seal_split_prepared` only when that slice
holds 256 bytes or more (`frontTest`'s `long`): on 512-bit registers, whose
short path of the gathering is faster for less. Elsewhere it does from a
first slice of any length (the path for TLS records is faster than the
others' at every length), but for a text of 256 bytes or more whose first
slice is shorter: the gathering's path for TLS records, which takes it
whole, seals it faster (a 256-byte TLS record, of a 255-byte payload: 22%
faster on Zen 3, with AES-NI and AVX). -/
def tlsLong (v : GcmVariant) : Bool :=
  match ((v.stitch.bind (·.toPart)).map (·.name) : Option StitchToName) with
  | some .vaesAvx512 => true
  | _ => false

theorem sealCode_xdepth (v : GcmImpl) {M : Proof.Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.sealCode (v.withBlk B)).x86_64Depth ≤ 24 := by
  unfold GcmImpl.sealCode; split
  · exact Short.sealM_xdepth v B
  · split
    · exact SealFin.sealFM_xdepth v B
    · exact sealM_xdepth v B

theorem sealCode_mx (v : GcmImpl) {M : Proof.Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.sealCode (v.withBlk B)).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true := by
  unfold GcmImpl.sealCode; split
  · exact Short.sealM_mx v B
  · split
    · exact SealFin.sealFM_mx v B
    · exact sealM_mx v B

theorem sealCodeP_xdepth (v : GcmImpl) {M : Proof.Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.sealCodeP (v.withBlk B)).x86_64Depth ≤ 24 := by
  unfold GcmImpl.sealCodeP; split
  · exact Short.sealMP_xdepth v B
  · split
    · exact Short.sealFinP_xdepth v B
    · exact sealM_xdepth v B

theorem sealCodeP_mx (v : GcmImpl) {M : Proof.Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    (v.sealCodeP (v.withBlk B)).allInstrs (fun i => !VG.X86_64.loadsMxcsr i) = true := by
  unfold GcmImpl.sealCodeP; split
  · exact Short.sealMP_mx v B
  · split
    · exact Short.sealFinP_mx v B
    · exact sealM_mx v B

/-- The instance of `vg_aes_gcm_seal` calling the implementations `v`. -/
def sealFn (v : GcmImpl) : Gather.SealFn Proof.Gcm.X86_64.Stitch.CtxMode.base :=
  .ofBase ⟨Spec.Gcm.sealApi.name ++ v.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCode v.callees)⟩
    (sealSel_framed v Short.shortFacts) (X86_64.withStackArgScratch_spSafe (sealCode_spSafe v v.blkB))
    (StreamTo.framed_xdepth (sealCode_xdepth v v.blkB)) (StreamTo.framed_mx (sealCode_mx v v.blkB))

/-- The instance of `vg_aes_gcm_seal_precomputed` calling the implementations `v`. -/
def sealFnP (v : GcmImpl) : Gather.SealFn Proof.Gcm.X86_64.Stitch.CtxMode.powers :=
  .ofPowers ⟨Spec.Gcm.sealPrecomputedApi.name ++ v.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.sealCode (v.withBlk v.blkP))⟩
    (sealSelP_framed v Short.shortFacts) (X86_64.withStackArgScratch_spSafe (sealCode_spSafe v v.blkP))
    (StreamTo.framed_xdepth (sealCode_xdepth v v.blkP)) (StreamTo.framed_mx (sealCode_mx v v.blkP))

/-- The instance of `vg_aes_gcm_stream_init` calling the implementations `v`. -/
def initFn (v : GcmImpl) : Gather.InitFn :=
  .ofSpec ⟨Spec.Gcm.streamInitApi.name ++ v.suffix,
      Impl.StackScratch.X86_64.withStackScratch 2568 .r8 (Impl.AesGcm.X86_64.streamInit v.callees)⟩
    (streamInit_framed v) (X86_64.withStackScratch_spSafe (by decide) (streamInit_spSafe v))
    (Gather.framedS_xdepth (streamInit_xdepth v)) (Gather.framedS_mx (streamInit_mx v))

/-- The instance of `vg_aes_gcm_stream_aad` calling the implementations `v`. -/
def aadFn (v : GcmImpl) : Gather.AadFn :=
  .ofSpec ⟨Spec.Gcm.streamAadApi.name ++ v.suffix,
      Impl.StackScratch.X86_64.withStackScratch 2568 .r9 (Impl.AesGcm.X86_64.streamAad v.callees)⟩
    (streamAad_framed v) (X86_64.withStackScratch_spSafe (by decide) (streamAad_spSafe v))
    (Gather.framedS_xdepth (streamAad_xdepth v)) (Gather.framedS_mx (streamAad_mx v))

/-- The instance of `vg_aes_gcm_stream_finish` calling the implementations `v`. -/
def finFn (v : GcmImpl) : Gather.FinFn :=
  .ofSpec ⟨Spec.Gcm.streamFinishApi.name ++ v.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2576 0 (Impl.AesGcm.X86_64.streamFinish v.callees)⟩
    (streamFinish_framed v) (X86_64.withStackArgScratch_spSafe (streamFinish_spSafe v))
    (StreamTo.framed_xdepth (streamFinish_xdepth v)) (StreamTo.framed_mx (streamFinish_mx v))

/-- The instance of `vg_aes_gcm_stream_encrypt_to` of a variant. -/
def toFn (v : GcmVariant) : Gather.ToFn Proof.Gcm.X86_64.Stitch.CtxMode.base :=
  .ofBase ⟨"vg_aes_gcm_stream_encrypt_to" ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2232 3
        (Impl.AesGcm.X86_64.StreamTo.encrypt (blkTo v).fn (encFn v.impl).fn)⟩
    (StreamTo.streamEncryptTo_framed (blkTo v) (encFn v.impl))
    (X86_64.withStackArgScratch_spSafe (StreamTo.encrypt_spAll (blkTo v) (encFn v.impl)))
    (StreamTo.framed_xdepth (StreamTo.encrypt_xdepth (blkTo v) (encFn v.impl)))
    (StreamTo.framed_mx (StreamTo.encrypt_mx (blkTo v) (encFn v.impl)))

/-- The instance of `vg_aes_gcm_stream_encrypt_to_precomputed` of a variant. -/
def toFnP (v : GcmVariant) : Gather.ToFn Proof.Gcm.X86_64.Stitch.CtxMode.powers :=
  .ofPowers ⟨"vg_aes_gcm_stream_encrypt_to_precomputed" ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2232 3
        (Impl.AesGcm.X86_64.StreamTo.encrypt (blkToP v).fn (encFnP v.impl).fn)⟩
    (StreamTo.streamEncryptToP_framed (blkToP v) (encFnP v.impl))
    (X86_64.withStackArgScratch_spSafe (StreamTo.encrypt_spAll (blkToP v) (encFnP v.impl)))
    (StreamTo.framed_xdepth (StreamTo.encrypt_xdepth (blkToP v) (encFnP v.impl)))
    (StreamTo.framed_mx (StreamTo.encrypt_mx (blkToP v) (encFnP v.impl)))

/-- The instance of `vg_aes_gcm_seal_split` of a variant. -/
def splitFn (v : GcmVariant) : Gather.SplitFn Proof.Gcm.X86_64.Stitch.CtxMode.base :=
  .ofBase ⟨"vg_aes_gcm_seal_split" ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2616 5
        (Impl.AesGcm.X86_64.SealSplit.«seal» (v.impl.splitMid (v.impl.withBlk v.impl.blkB) (blkTo v).fn))⟩
    (Split.sealSplit_framed v.impl Short.shortFacts v.impl.blkB (blkTo v))
    (X86_64.withStackArgScratch_spSafe (Split.sealSplit_spSafe v.impl v.impl.blkB (blkTo v)))
    (StreamTo.framed_xdepth (Split.sealSplit_xdepth v.impl v.impl.blkB (blkTo v)))
    (StreamTo.framed_mx (Split.sealSplit_mx v.impl v.impl.blkB (blkTo v)))

/-- The instance of `vg_aes_gcm_seal_split_precomputed` of a variant. -/
def splitFnP (v : GcmVariant) : Gather.SplitFn Proof.Gcm.X86_64.Stitch.CtxMode.powers :=
  .ofPowers ⟨"vg_aes_gcm_seal_split_precomputed" ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2616 5
        (Impl.AesGcm.X86_64.SealSplit.«seal» (v.impl.splitMid (v.impl.withBlk v.impl.blkP) (blkToP v).fn))⟩
    (Split.sealSplitP_framed v.impl Short.shortFacts v.impl.blkP (blkToP v))
    (X86_64.withStackArgScratch_spSafe (Split.sealSplit_spSafe v.impl v.impl.blkP (blkToP v)))
    (StreamTo.framed_xdepth (Split.sealSplit_xdepth v.impl v.impl.blkP (blkToP v)))
    (StreamTo.framed_mx (Split.sealSplit_mx v.impl v.impl.blkP (blkToP v)))

/-- The short path of `vg_aes_gcm_seal_gather` of a variant: the text copied
and sealed by `vg_aes_gcm_seal`, or sealed from its first slice by
`vg_aes_gcm_seal_split`. -/
def shortFn (v : GcmVariant) : Gather.ShortFn Proof.Gcm.X86_64.Stitch.CtxMode.base :=
  .ofBoth (sealFn v.impl) (splitFn v) (copyBelow_lt v) (splitFrom_pos v) (splitFrom_le v)

/-- The short path of `vg_aes_gcm_seal_gather_precomputed` of a variant. -/
def shortFnP (v : GcmVariant) : Gather.ShortFn Proof.Gcm.X86_64.Stitch.CtxMode.powers :=
  .ofBoth (sealFnP v.impl) (splitFnP v) (copyBelow_lt v) (splitFrom_pos v) (splitFrom_le v)

/-- Prepared whole-block implementations, propagated through all callers. -/
def blkR (v : GcmVariant) : BlkFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared :=
  v.impl.blkM v.stitchR ("vg_aes_gcm_encrypt_blocks_prepared" ++ v.impl.suffix)
    ("vg_aes_gcm_decrypt_blocks_prepared" ++ v.impl.suffix)

def blkToR (v : GcmVariant) : StreamTo.BlkToFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared :=
  .ofBlocks ("vg_aes_gcm_encrypt_blocks_to_prepared" ++ v.impl.suffix) (blkR v) v.stitchToR

def encFnR (v : GcmVariant) : StreamTo.EncFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared :=
  .ofPrepared ⟨Spec.Gcm.streamEncryptPreparedApi.name ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2584 1
        (Impl.AesGcm.X86_64.streamEncrypt (v.impl.withBlk (blkR v)))⟩
    (streamEncryptPrepared_framed v.impl (blkR v)) (X86_64.withStackArgScratch_spSafe (streamEncryptM_spSafe v.impl (blkR v)))
    (StreamTo.framed_xdepth (streamEncryptM_xdepth v.impl (blkR v))) (StreamTo.framed_mx (streamEncryptM_mx v.impl (blkR v)))

def toFnR (v : GcmVariant) : Gather.ToFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared :=
  .ofPrepared ⟨"vg_aes_gcm_stream_encrypt_to_prepared" ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2232 3
        (Impl.AesGcm.X86_64.StreamTo.encrypt (blkToR v).fn (encFnR v).fn)⟩
    (StreamTo.streamEncryptToPrepared_framed (blkToR v) (encFnR v))
    (X86_64.withStackArgScratch_spSafe (StreamTo.encrypt_spAll (blkToR v) (encFnR v)))
    (StreamTo.framed_xdepth (StreamTo.encrypt_xdepth (blkToR v) (encFnR v)))
    (StreamTo.framed_mx (StreamTo.encrypt_mx (blkToR v) (encFnR v)))

/-- The instance of `vg_aes_gcm_seal_prepared` of a variant. -/
def sealFnR (v : GcmVariant) : Gather.SealFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared :=
  .ofPrepared ⟨Spec.Gcm.sealPreparedApi.name ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCodeP (v.impl.withBlk (blkR v)))⟩
    (sealSelPrepared_framed v.impl (blkR v) Short.shortFacts)
    (X86_64.withStackArgScratch_spSafe (sealCodeP_spSafe v.impl (blkR v)))
    (StreamTo.framed_xdepth (sealCodeP_xdepth v.impl (blkR v))) (StreamTo.framed_mx (sealCodeP_mx v.impl (blkR v)))

/-- The instance of `vg_aes_gcm_seal_split_prepared` of a variant. -/
def splitFnR (v : GcmVariant) : Gather.SplitFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared :=
  .ofPrepared ⟨"vg_aes_gcm_seal_split_prepared" ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2616 5
        (Impl.AesGcm.X86_64.SealSplit.«seal» (v.impl.splitMidR (v.impl.withBlk (blkR v)) (blkToR v).fn))⟩
    (Split.sealSplitPrepared_framed v.impl (blkR v) (blkToR v) Short.shortFacts)
    (X86_64.withStackArgScratch_spSafe (Split.sealSplitR_spSafe v.impl (blkR v) (blkToR v)))
    (StreamTo.framed_xdepth (Split.sealSplitR_xdepth v.impl (blkR v) (blkToR v)))
    (StreamTo.framed_mx (Split.sealSplitR_mx v.impl (blkR v) (blkToR v)))

/-- The short path of `vg_aes_gcm_seal_gather_prepared` of a variant. -/
def shortFnR (v : GcmVariant) : Gather.ShortFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared :=
  .ofBoth (sealFnR v) (splitFnR v) (copyBelow_lt v) (splitFrom_pos v) (splitFrom_le v)

/-! ## The `_prepared16` artifacts

The 256-bit interleaved loops (`StitchName.vaes`) and the 128-bit ones
(`StitchName.aesniAvx`, which read `H'⁹`–`H'¹⁵`) read only the first eight
pairs of a prepared key context (`StitchR.stitchR_okN 8`,
`StitchAvx8.stitchR_okN 8`); `stitchR16` and `stitchToR16` give them, with
that proof, for the variants that name them,
and `blkR16`, …, `shortFnR16` the instances of the functions their callers
call, as `blkR`, …, `shortFnR` do for the 48 powers. -/

section Prepared16

open Gcm.X86_64.Stitch (CtxMode)

open Gcm.X86_64.Stitch (CtxMode)

/-- Whether a variant's interleaved loops read only the first 16 prepared
powers: the 256-bit and the 128-bit ones. -/
def StitchName.reads16 : StitchName → Bool
  | .vaes => true
  | .vaesAvx512 => false
  | .aesniAvx => true

/-- The loops that read only the first 16 powers, for a key context holding
them. -/
theorem StitchName.okR16 : (n : StitchName) → n.reads16 = true →
    Proof.Gcm.X86_64.Stitch.StitchOkM CtxMode.prepared16 n.encR n.decR
      (if n.fullR then 1 else 16) (if n.fullDR then 1 else 16)
  | .vaes, _ => (Proof.Gcm.X86_64.StitchR.stitchR_okN 8).weaken (by decide) (by decide)
  | .vaesAvx512, h => by cases h
  | .aesniAvx, _ => Proof.Gcm.X86_64.StitchAvx8.stitchR_okN 8

/-- `okR16`'s loops on fewer than 16 blocks. -/
theorem StitchName.okRS16 : (n : StitchName) → n.reads16 = true →
    Proof.Gcm.X86_64.Stitch.StitchOkSmall CtxMode.prepared16 n.encRS n.decRS
      (if n.smallR then 1 else 16) (if n.smallR then 1 else 16)
  | .vaes, _ => (Proof.Gcm.X86_64.StitchR.stitchR_okN 8).small
  | .vaesAvx512, h => by cases h
  | .aesniAvx, _ => Proof.Gcm.X86_64.StitchAvx8.stitchRS_okN 8

/-- The loops of a variant naming ones that read only the first 16 powers,
for a key context of `vg_aes_gcm_prepare16`. -/
def GcmVariant.stitchR16 (v : GcmVariant) : Option (StitchCode CtxMode.prepared16 true) :=
  v.stitch.bind fun p => if h : p.name.reads16 = true then p.pieceR.map fun q =>
      ⟨p.name.encR, p.name.decR, p.name.fullR, p.name.fullDR, p.name.smallR, p.name.smallR, p.name.small4R,
        p.name.encRS, p.name.decRS, p.name.okR16 h, p.name.okRS16 h, q.enc, q.dec,
        (p.name.pieceRS q).1, (p.name.pieceRS q).2⟩
    else none

/-- Whether an out-of-place loop reads only the first 16 prepared powers. -/
def StitchToName.reads16 : StitchToName → Bool
  | .vaes => true
  | .vaesAvx512 => false
  | .aesniAvx => true

/-- The out-of-place loops that read only the first 16 powers, for a key
context holding them. -/
theorem StitchToName.okR16 : (n : StitchToName) → n.reads16 = true →
    Proof.Gcm.X86_64.Stitch.StitchToOkM CtxMode.prepared16 n.encR (if n.fullR then 1 else 16)
  | .vaes, _ => Proof.Gcm.X86_64.StitchR.stitchTo_okN 8
  | .vaesAvx512, h => by cases h
  | .aesniAvx, _ => Proof.Gcm.X86_64.StitchAvx8.stitchToR_okN 8

def GcmVariant.stitchToR16 (v : GcmVariant) : Option (StitchToCode CtxMode.prepared16 true) :=
  (v.stitch.bind (·.toPart)).bind fun p => if h : p.name.reads16 = true then
      p.pieceR.map fun q => ⟨p.name.encR, p.name.fullR, p.name.okR16 h, q.enc⟩
    else none

/-- What the `_prepared16` instances of a variant need besides loops that
read only the first 16 powers: no short path, whose table of powers is copied from all 48, and no
one-pass loop that reads more than 16 (`StitchZHTo.encN`). -/
structure R16 (v : GcmVariant) : Prop where
  short : v.impl.short = false
  onePass : ∀ n, v.impl.onePass = some n → n ≠ .z

/-- Whether a variant's prepared instances read only the first 16 powers:
its loops read no other (`stitchR16`), and `R16` holds. -/
def GcmVariant.r16 (v : GcmVariant) : Option (PLift (R16 v)) :=
  if h : v.stitchR16.isSome = true ∧ v.impl.short = false ∧ v.impl.onePass ≠ some .z then
    some ⟨⟨h.2.1, fun _ hn hz => h.2.2 (hz ▸ hn)⟩⟩
  else none

/-- Whole-block implementations for a key context of `vg_aes_gcm_prepare16`. -/
def blkR16 (v : GcmVariant) : BlkFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 :=
  v.impl.blkM v.stitchR16 ("vg_aes_gcm_encrypt_blocks_prepared16" ++ v.impl.suffix)
    ("vg_aes_gcm_decrypt_blocks_prepared16" ++ v.impl.suffix)

def blkToR16 (v : GcmVariant) : StreamTo.BlkToFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 :=
  .ofBlocks ("vg_aes_gcm_encrypt_blocks_to_prepared16" ++ v.impl.suffix) (blkR16 v) v.stitchToR16

def encFnR16 (v : GcmVariant) : StreamTo.EncFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 :=
  .ofPrepared16 ⟨Spec.Gcm.streamEncryptPrepared16Api.name ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2584 1
        (Impl.AesGcm.X86_64.streamEncrypt (v.impl.withBlk (blkR16 v)))⟩
    (streamEncryptPrepared16_framed v.impl (blkR16 v)) (X86_64.withStackArgScratch_spSafe (streamEncryptM_spSafe v.impl (blkR16 v)))
    (StreamTo.framed_xdepth (streamEncryptM_xdepth v.impl (blkR16 v))) (StreamTo.framed_mx (streamEncryptM_mx v.impl (blkR16 v)))

def toFnR16 (v : GcmVariant) : Gather.ToFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 :=
  .ofPrepared16 ⟨"vg_aes_gcm_stream_encrypt_to_prepared16" ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2232 3
        (Impl.AesGcm.X86_64.StreamTo.encrypt (blkToR16 v).fn (encFnR16 v).fn)⟩
    (StreamTo.streamEncryptToPrepared16_framed (blkToR16 v) (encFnR16 v))
    (X86_64.withStackArgScratch_spSafe (StreamTo.encrypt_spAll (blkToR16 v) (encFnR16 v)))
    (StreamTo.framed_xdepth (StreamTo.encrypt_xdepth (blkToR16 v) (encFnR16 v)))
    (StreamTo.framed_mx (StreamTo.encrypt_mx (blkToR16 v) (encFnR16 v)))

/-- The instance of `vg_aes_gcm_seal_prepared16` of a variant. -/
def sealFnR16 (v : GcmVariant) (hs : v.impl.short = false) : Gather.SealFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 :=
  .ofPrepared16 ⟨Spec.Gcm.sealPrepared16Api.name ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2600 3 (v.impl.sealCodeP (v.impl.withBlk (blkR16 v)))⟩
    (sealSelPrepared16_framed v.impl (blkR16 v) Short.shortFacts hs)
    (X86_64.withStackArgScratch_spSafe (sealCodeP_spSafe v.impl (blkR16 v)))
    (StreamTo.framed_xdepth (sealCodeP_xdepth v.impl (blkR16 v))) (StreamTo.framed_mx (sealCodeP_mx v.impl (blkR16 v)))

/-- The instance of `vg_aes_gcm_seal_split_prepared16` of a variant. -/
def splitFnR16 (v : GcmVariant) (hz : ∀ n, v.impl.onePass = some n → n ≠ .z) : Gather.SplitFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 :=
  .ofPrepared16 ⟨"vg_aes_gcm_seal_split_prepared16" ++ v.impl.suffix,
      Impl.StackScratch.X86_64.withStackArgScratch 2616 5
        (Impl.AesGcm.X86_64.SealSplit.«seal» (v.impl.splitMidR (v.impl.withBlk (blkR16 v)) (blkToR16 v).fn))⟩
    (Split.sealSplitPrepared16_framed v.impl (blkR16 v) (blkToR16 v) Short.shortFacts hz)
    (X86_64.withStackArgScratch_spSafe (Split.sealSplitR_spSafe v.impl (blkR16 v) (blkToR16 v)))
    (StreamTo.framed_xdepth (Split.sealSplitR_xdepth v.impl (blkR16 v) (blkToR16 v)))
    (StreamTo.framed_mx (Split.sealSplitR_mx v.impl (blkR16 v) (blkToR16 v)))

/-- The short path of `vg_aes_gcm_seal_gather_prepared16` of a variant. -/
def shortFnR16 (v : GcmVariant) (hs : v.impl.short = false) (hz : ∀ n, v.impl.onePass = some n → n ≠ .z) : Gather.ShortFn Proof.Gcm.X86_64.Stitch.CtxMode.prepared16 :=
  .ofBoth (sealFnR16 v hs) (splitFnR16 v hz) (copyBelow_lt v) (splitFrom_pos v) (splitFrom_le v)

end Prepared16

end VG.Proof.AesGcm.X86_64
