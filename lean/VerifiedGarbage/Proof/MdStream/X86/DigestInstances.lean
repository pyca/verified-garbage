module

public import VerifiedGarbage.Proof.MdStream.X86.Digest
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hashes
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Sha224
public import VerifiedGarbage.Spec.Sha1.Contract
public import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeyCT
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Calls
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.MdStream.X86.Digest
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hashes
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Sha1
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Sha224
meta import VerifiedGarbage.Spec.Sha1.Contract
meta import VerifiedGarbage.Spec.Sha512.Contract
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.AnyKeyCT
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Calls
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# The one-shot SHA-1 and SHA-2 digests on x86 (32-bit): the instances

The generic proof (`Digest.lean`) at each hash function's streaming functions
(`Proof/Pbkdf2/Stream/X86/Hashes.lean`, `Sha1.lean`, `Sha256.lean`,
`Sha224.lean`): SHA-1's, SHA-224's and SHA-256's for any of their backends'
`update` and `finalize`. The taint checks, and that the code keeps `esp`,
depend only on the sizes, so they are evaluated once for each hash function,
on its shape (`sha1Shape`, …); states satisfy the contracts (`digestSat`,
`digestFrameSat`); and the function runs in a frame of its own, which it
wipes (`digested`) and which keeps `esp` (`digestSp`).
-/

@[expose] public section

namespace VG.Proof.MdStream.X86.Digest

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Impl.MdStream.X86.Digest (dbytes dframe digestMain digest)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK Sha1Stream Sha256Stream sha1H sha1OK sha224H sha224OK sha256H sha256OK
  sha384H sha384OK sha512H' sha512OK sha512_224H sha512_224OK sha512_256H sha512_256OK)
open Spec.Sha256 (digestSig digestPost)

/-! ## For any hash function -/

variable {H : Hash}

/-- No instruction of `digestMain` writes `esp` but its frames' pushes and
pops, from its shape's and the functions it calls. -/
theorem noEsp (hH : HashOK H)
    (hb : (digestMain (shapeOf H)).allInstrs (fun i => !Taint.clobbers i .esp) = true) :
    (digestMain H).allInstrs (fun i => !Taint.clobbers i .esp) = true :=
  digestMain_allInstrs hb (Pbkdf2.Whole.X86.Any.allInstrs_of_noSp hH.initSp)
    (Pbkdf2.Whole.X86.Any.allInstrs_of_noSp hH.updSp) (Pbkdf2.Whole.X86.Any.allInstrs_of_noSp hH.finSp)

/-- `digest`, verified, from the checks of its shape and states satisfying
the contracts. -/
theorem digested (hH : HashOK H) (hc : Checks (shapeOf H))
    (hb : (digestMain (shapeOf H)).allInstrs (fun i => !Taint.clobbers i .esp) = true)
    (hsat : ∃ s, (digestScratch H.D hH.SH.H.hash (nw H)).pre s)
    (hfsat : ∃ s, (Spec.Sha256.digestContract X86.abi H.D hH.SH.H.hash (48 + dframe H)).pre s) :
    Verified X86.target (digest H) (Spec.Sha256.digestContract X86.abi H.D hH.SH.H.hash (48 + dframe H)) :=
  framed hH (verified hH (checks_of_shape hc) hsat) hfsat (noEsp hH hb)

/-- `digest` keeps `esp`, given that its frame does, for its shape's sizes
(decided for each hash function). -/
theorem digestSp (hH : HashOK H)
    (hb : (digestMain (shapeOf H)).allInstrs (fun i => !Taint.clobbers i .esp) = true)
    (hw : (Code.block (Impl.StackScratch.X86.wipe (8 + 4 * 3) (dbytes (shapeOf H) / 4)) : Prog isa).all
      (fun i => !isa.writesSp i) = true)
    (hf : (Impl.StackScratch.X86.withStackScratch (dframe (shapeOf H)) 3 (.block [])).all
      (fun i => !isa.writesSp i) = true) :
    (digest H).all (fun i => !isa.writesSp i) = true :=
  Pbkdf2.Whole.X86.Any.withStackScratchWiped_spSafe (by
    rw [Pbkdf2.Whole.X86.Any.all_writesSp_eq]; exact noEsp hH hb) hw hf

/-! ## The shapes

The sizes of each hash function's streaming functions on x86, with no code:
the taint checks, and that the code keeps `esp`, are evaluated on them. -/

/-- SHA-1's sizes. -/
def sha1Shape : Hash := ⟨64, 84, 20, 20, 20, "", .block [], "", .block [], "", .block []⟩

/-- SHA-256's sizes, with a `D`-byte digest. -/
def sha256Shape (D : Nat) : Hash := ⟨64, 96, D, 32, 20, "", .block [], "", .block [], "", .block []⟩

/-- The SHA-512 family's sizes, with a `D`-byte digest. -/
def sha512Shape (D : Nat) : Hash := ⟨128, 192, D, 64, 34, "", .block [], "", .block [], "", .block []⟩

theorem sha1Shape_checks : Checks (sha1Shape) := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha1Shape_noEsp : (digestMain (sha1Shape)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  decide +kernel

theorem sha1Shape_wipe :
    (Code.block (Impl.StackScratch.X86.wipe (8 + 4 * 3) (dbytes (sha1Shape) / 4)) : Prog isa).all
      (fun i => !isa.writesSp i) = true := by
  decide +kernel

theorem sha1Shape_frame : (Impl.StackScratch.X86.withStackScratch (dframe (sha1Shape)) 3 (.block [])).all
    (fun i => !isa.writesSp i) = true := by
  decide +kernel

theorem sha224Shape_checks : Checks (sha256Shape 28) := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha224Shape_noEsp : (digestMain (sha256Shape 28)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  decide +kernel

theorem sha224Shape_wipe :
    (Code.block (Impl.StackScratch.X86.wipe (8 + 4 * 3) (dbytes (sha256Shape 28) / 4)) : Prog isa).all
      (fun i => !isa.writesSp i) = true := by
  decide +kernel

theorem sha224Shape_frame : (Impl.StackScratch.X86.withStackScratch (dframe (sha256Shape 28)) 3 (.block [])).all
    (fun i => !isa.writesSp i) = true := by
  decide +kernel

theorem sha256Shape_checks : Checks (sha256Shape 32) := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha256Shape_noEsp : (digestMain (sha256Shape 32)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  decide +kernel

theorem sha256Shape_wipe :
    (Code.block (Impl.StackScratch.X86.wipe (8 + 4 * 3) (dbytes (sha256Shape 32) / 4)) : Prog isa).all
      (fun i => !isa.writesSp i) = true := by
  decide +kernel

theorem sha256Shape_frame : (Impl.StackScratch.X86.withStackScratch (dframe (sha256Shape 32)) 3 (.block [])).all
    (fun i => !isa.writesSp i) = true := by
  decide +kernel

theorem sha384Shape_checks : Checks (sha512Shape 48) := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha384Shape_noEsp : (digestMain (sha512Shape 48)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  decide +kernel

theorem sha384Shape_wipe :
    (Code.block (Impl.StackScratch.X86.wipe (8 + 4 * 3) (dbytes (sha512Shape 48) / 4)) : Prog isa).all
      (fun i => !isa.writesSp i) = true := by
  decide +kernel

theorem sha384Shape_frame : (Impl.StackScratch.X86.withStackScratch (dframe (sha512Shape 48)) 3 (.block [])).all
    (fun i => !isa.writesSp i) = true := by
  decide +kernel

theorem sha512Shape_checks : Checks (sha512Shape 64) := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha512Shape_noEsp : (digestMain (sha512Shape 64)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  decide +kernel

theorem sha512Shape_wipe :
    (Code.block (Impl.StackScratch.X86.wipe (8 + 4 * 3) (dbytes (sha512Shape 64) / 4)) : Prog isa).all
      (fun i => !isa.writesSp i) = true := by
  decide +kernel

theorem sha512Shape_frame : (Impl.StackScratch.X86.withStackScratch (dframe (sha512Shape 64)) 3 (.block [])).all
    (fun i => !isa.writesSp i) = true := by
  decide +kernel

theorem sha512_224Shape_checks : Checks (sha512Shape 28) := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha512_224Shape_noEsp : (digestMain (sha512Shape 28)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  decide +kernel

theorem sha512_224Shape_wipe :
    (Code.block (Impl.StackScratch.X86.wipe (8 + 4 * 3) (dbytes (sha512Shape 28) / 4)) : Prog isa).all
      (fun i => !isa.writesSp i) = true := by
  decide +kernel

theorem sha512_224Shape_frame : (Impl.StackScratch.X86.withStackScratch (dframe (sha512Shape 28)) 3 (.block [])).all
    (fun i => !isa.writesSp i) = true := by
  decide +kernel

theorem sha512_256Shape_checks : Checks (sha512Shape 32) := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha512_256Shape_noEsp : (digestMain (sha512Shape 32)).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  decide +kernel

theorem sha512_256Shape_wipe :
    (Code.block (Impl.StackScratch.X86.wipe (8 + 4 * 3) (dbytes (sha512Shape 32) / 4)) : Prog isa).all
      (fun i => !isa.writesSp i) = true := by
  decide +kernel

theorem sha512_256Shape_frame : (Impl.StackScratch.X86.withStackScratch (dframe (sha512Shape 32)) 3 (.block [])).all
    (fun i => !isa.writesSp i) = true := by
  decide +kernel

/-! ## SHA-1, for any backend -/

theorem sha1_sat (hash : List Byte → List Byte) : ∃ s, (digestScratch sha1Shape.D hash (nw sha1Shape)).pre s := by
  sig_implies_sat [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, digestSig, digestPost,
    nw, dbytes, Hash.buf, sha1Shape, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [digestSat, digestMem]
    using digestSat 20 280

theorem sha1_frameSat (v : Sha1Stream) :
    ∃ s, (Spec.Sha256.digestContract X86.abi (sha1H v).D (sha1OK v).SH.H.hash (48 + dframe (sha1H v))).pre s := by
  implies_sat [Spec.Sha256.digestContract, digestSig, digestPost, dframe, dbytes, Hash.buf, sha1H,
      Sha1.X86.Variants.hmacHash, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [digestFrameSat, digestMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using digestFrameSat 20

theorem sha1_digest (v : Sha1Stream) :
    Verified X86.target (digest (sha1H v)) (Spec.Sha1.digestContract X86.abi (48 + dframe (sha1H v))) :=
  digested (sha1OK v) sha1Shape_checks sha1Shape_noEsp (sha1_sat _) (sha1_frameSat v)

theorem sha1_digestSp (v : Sha1Stream) : (digest (sha1H v)).all (fun i => !isa.writesSp i) = true :=
  digestSp (sha1OK v) sha1Shape_noEsp sha1Shape_wipe sha1Shape_frame

/-! ## SHA-224, for any backend -/

theorem sha224_sat (hash : List Byte → List Byte) :
    ∃ s, (digestScratch (sha256Shape 28).D hash (nw (sha256Shape 28))).pre s := by
  sig_implies_sat [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, digestSig, digestPost,
    nw, dbytes, Hash.buf, sha256Shape, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [digestSat, digestMem]
    using digestSat 28 304

theorem sha224_frameSat (v : Sha256Stream) :
    ∃ s, (Spec.Sha256.digestContract X86.abi (sha224H v).D (sha224OK v).SH.H.hash (48 + dframe (sha224H v))).pre s := by
  implies_sat [Spec.Sha256.digestContract, digestSig, digestPost, dframe, dbytes, Hash.buf, sha224H,
      Sha256.X86.Variants.hmacHash224, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [digestFrameSat, digestMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using digestFrameSat 28

theorem sha224_digest (v : Sha256Stream) :
    Verified X86.target (digest (sha224H v))
      (Spec.Sha256.digestContract X86.abi 28 Spec.Sha256.sha224 (48 + dframe (sha224H v))) :=
  digested (sha224OK v) sha224Shape_checks sha224Shape_noEsp (sha224_sat _) (sha224_frameSat v)

theorem sha224_digestSp (v : Sha256Stream) : (digest (sha224H v)).all (fun i => !isa.writesSp i) = true :=
  digestSp (sha224OK v) sha224Shape_noEsp sha224Shape_wipe sha224Shape_frame

/-! ## SHA-256, for any backend -/

theorem sha256_sat (hash : List Byte → List Byte) :
    ∃ s, (digestScratch (sha256Shape 32).D hash (nw (sha256Shape 32))).pre s := by
  sig_implies_sat [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, digestSig, digestPost,
    nw, dbytes, Hash.buf, sha256Shape, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [digestSat, digestMem]
    using digestSat 32 304

theorem sha256_frameSat (v : Sha256Stream) :
    ∃ s, (Spec.Sha256.digestContract X86.abi (sha256H v).D (sha256OK v).SH.H.hash (48 + dframe (sha256H v))).pre s := by
  implies_sat [Spec.Sha256.digestContract, digestSig, digestPost, dframe, dbytes, Hash.buf, sha256H,
      Sha256.X86.Variants.hmacHash, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [digestFrameSat, digestMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using digestFrameSat 32

theorem sha256_digest (v : Sha256Stream) :
    Verified X86.target (digest (sha256H v))
      (Spec.Sha256.digestContract X86.abi 32 Spec.Sha256.hash (48 + dframe (sha256H v))) :=
  digested (sha256OK v) sha256Shape_checks sha256Shape_noEsp (sha256_sat _) (sha256_frameSat v)

theorem sha256_digestSp (v : Sha256Stream) : (digest (sha256H v)).all (fun i => !isa.writesSp i) = true :=
  digestSp (sha256OK v) sha256Shape_noEsp sha256Shape_wipe sha256Shape_frame

/-! ## SHA-384 -/

theorem sha384_sat : ∃ s, (digestScratch sha384H.D sha384OK.SH.H.hash (nw sha384H)).pre s := by
  sig_implies_sat [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, digestSig, digestPost,
    nw, dbytes, Hash.buf, sha384H, Pbkdf2.Stream.X86.sha512H, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [digestSat, digestMem] using digestSat 48 544

theorem sha384_frameSat : ∃ s, (Spec.Sha256.digestContract X86.abi sha384H.D sha384OK.SH.H.hash (48 + dframe sha384H)).pre s := by
  implies_sat [Spec.Sha256.digestContract, digestSig, digestPost, dframe, dbytes, Hash.buf, sha384H,
      Pbkdf2.Stream.X86.sha512H, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [digestFrameSat, digestMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using digestFrameSat 48

theorem sha384_digest :
    Verified X86.target (digest sha384H) (Spec.Sha512.digestContract X86.abi 48 Spec.Sha512.sha384 (48 + dframe sha384H)) :=
  digested sha384OK sha384Shape_checks sha384Shape_noEsp sha384_sat sha384_frameSat

theorem sha384_digestSp : (digest sha384H).all (fun i => !isa.writesSp i) = true :=
  digestSp sha384OK sha384Shape_noEsp sha384Shape_wipe sha384Shape_frame

/-! ## SHA-512 -/

theorem sha512_sat : ∃ s, (digestScratch sha512H'.D sha512OK.SH.H.hash (nw sha512H')).pre s := by
  sig_implies_sat [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, digestSig, digestPost,
    nw, dbytes, Hash.buf, sha512H', Pbkdf2.Stream.X86.sha512H, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [digestSat, digestMem] using digestSat 64 544

theorem sha512_frameSat : ∃ s, (Spec.Sha256.digestContract X86.abi sha512H'.D sha512OK.SH.H.hash (48 + dframe sha512H')).pre s := by
  implies_sat [Spec.Sha256.digestContract, digestSig, digestPost, dframe, dbytes, Hash.buf, sha512H',
      Pbkdf2.Stream.X86.sha512H, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [digestFrameSat, digestMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using digestFrameSat 64

theorem sha512_digest :
    Verified X86.target (digest sha512H') (Spec.Sha512.digestContract X86.abi 64 Spec.Sha512.sha512 (48 + dframe sha512H')) :=
  digested sha512OK sha512Shape_checks sha512Shape_noEsp sha512_sat sha512_frameSat

theorem sha512_digestSp : (digest sha512H').all (fun i => !isa.writesSp i) = true :=
  digestSp sha512OK sha512Shape_noEsp sha512Shape_wipe sha512Shape_frame

/-! ## SHA-512/224 -/

theorem sha512_224_sat : ∃ s, (digestScratch sha512_224H.D sha512_224OK.SH.H.hash (nw sha512_224H)).pre s := by
  sig_implies_sat [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, digestSig, digestPost,
    nw, dbytes, Hash.buf, sha512_224H, Pbkdf2.Stream.X86.sha512H, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [digestSat, digestMem] using digestSat 28 544

theorem sha512_224_frameSat : ∃ s, (Spec.Sha256.digestContract X86.abi sha512_224H.D sha512_224OK.SH.H.hash (48 + dframe sha512_224H)).pre s := by
  implies_sat [Spec.Sha256.digestContract, digestSig, digestPost, dframe, dbytes, Hash.buf, sha512_224H,
      Pbkdf2.Stream.X86.sha512H, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [digestFrameSat, digestMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using digestFrameSat 28

theorem sha512_224_digest :
    Verified X86.target (digest sha512_224H) (Spec.Sha512.digestContract X86.abi 28 Spec.Sha512.sha512_224 (48 + dframe sha512_224H)) :=
  digested sha512_224OK sha512_224Shape_checks sha512_224Shape_noEsp sha512_224_sat sha512_224_frameSat

theorem sha512_224_digestSp : (digest sha512_224H).all (fun i => !isa.writesSp i) = true :=
  digestSp sha512_224OK sha512_224Shape_noEsp sha512_224Shape_wipe sha512_224Shape_frame

/-! ## SHA-512/256 -/

theorem sha512_256_sat : ∃ s, (digestScratch sha512_256H.D sha512_256OK.SH.H.hash (nw sha512_256H)).pre s := by
  sig_implies_sat [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, digestSig, digestPost,
    nw, dbytes, Hash.buf, sha512_256H, Pbkdf2.Stream.X86.sha512H, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [digestSat, digestMem] using digestSat 32 544

theorem sha512_256_frameSat : ∃ s, (Spec.Sha256.digestContract X86.abi sha512_256H.D sha512_256OK.SH.H.hash (48 + dframe sha512_256H)).pre s := by
  implies_sat [Spec.Sha256.digestContract, digestSig, digestPost, dframe, dbytes, Hash.buf, sha512_256H,
      Pbkdf2.Stream.X86.sha512H, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [digestFrameSat, digestMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using digestFrameSat 32

theorem sha512_256_digest :
    Verified X86.target (digest sha512_256H) (Spec.Sha512.digestContract X86.abi 32 Spec.Sha512.sha512_256 (48 + dframe sha512_256H)) :=
  digested sha512_256OK sha512_256Shape_checks sha512_256Shape_noEsp sha512_256_sat sha512_256_frameSat

theorem sha512_256_digestSp : (digest sha512_256H).all (fun i => !isa.writesSp i) = true :=
  digestSp sha512_256OK sha512_256Shape_noEsp sha512_256Shape_wipe sha512_256Shape_frame

end VG.Proof.MdStream.X86.Digest
