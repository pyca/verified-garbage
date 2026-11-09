module

public import VerifiedGarbage.Proof.MdStream.Arm.Digest
public import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Hashes
public import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Sha256
public import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Sha224
public import VerifiedGarbage.Spec.Sha1.Contract
public import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.MdStream.Arm.Digest
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Hashes
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Sha256
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Sha224
meta import VerifiedGarbage.Spec.Sha1.Contract
meta import VerifiedGarbage.Spec.Sha512.Contract
meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# The one-shot SHA-1 and SHA-2 digests on 32-bit ARM: the instances

The generic proof (`Digest.lean`) at each hash function's streaming functions
(`Proof/Pbkdf2/Stream/Arm/Hashes.lean`, `Sha256.lean`, `Sha224.lean`): the
taint checks are evaluated by the kernel, states satisfy the contracts
(`digestSat`, `digestFrameSat`), and the function runs in a frame of its own,
which it wipes (`framed`).
-/

@[expose] public section

namespace VG.Proof.MdStream.Arm.Digest

open VG.Arm
open VG.Impl.MdStream.Arm.Digest (dbytes digest)
open VG.Proof.Pbkdf2.Stream.Arm (sha1H sha1OK sha224H sha224OK sha256H sha256OK sha384H sha384OK sha512H'
  sha512OK sha512_224H sha512_224OK sha512_256H sha512_256OK)

/-! ## SHA-1 -/

theorem sha1_checks : Checks sha1H := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha1_sat : ∃ s, (digestScratch sha1H.D sha1OK.SH.H.hash (nw sha1H)).pre s := by
  inst_sat [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sha256.digestSig,
    Spec.Sha256.digestPost, nw, dbytes, Impl.Pbkdf2.Stream.Arm.Hash.buf, sha1H, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using digestSat 20 304

theorem sha1_frameSat : ∃ s, (Spec.Sha256.digestContract Arm.abi sha1H.D sha1OK.SH.H.hash (16 + dbytes sha1H)).pre s := by
  inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, dbytes,
    Impl.Pbkdf2.Stream.Arm.Hash.buf, sha1H, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] using digestFrameSat 20

theorem sha1_digest : Verified Arm.target (digest sha1H) (Spec.Sha1.digestContract Arm.abi (16 + dbytes sha1H)) :=
  framed sha1OK (verified sha1OK sha1_checks sha1_sat) sha1_frameSat

/-! ## SHA-224 -/

theorem sha224_checks : Checks sha224H := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha224_sat : ∃ s, (digestScratch sha224H.D sha224OK.SH.H.hash (nw sha224H)).pre s := by
  inst_sat [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sha256.digestSig,
    Spec.Sha256.digestPost, nw, dbytes, Impl.Pbkdf2.Stream.Arm.Hash.buf, sha224H, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using digestSat 28 328

theorem sha224_frameSat : ∃ s, (Spec.Sha256.digestContract Arm.abi sha224H.D sha224OK.SH.H.hash (16 + dbytes sha224H)).pre s := by
  inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, dbytes,
    Impl.Pbkdf2.Stream.Arm.Hash.buf, sha224H, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] using digestFrameSat 28

theorem sha224_digest : Verified Arm.target (digest sha224H) (Spec.Sha256.digestContract Arm.abi 28 Spec.Sha256.sha224 (16 + dbytes sha224H)) :=
  framed sha224OK (verified sha224OK sha224_checks sha224_sat) sha224_frameSat

/-! ## SHA-256 -/

theorem sha256_checks : Checks sha256H := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha256_sat : ∃ s, (digestScratch sha256H.D sha256OK.SH.H.hash (nw sha256H)).pre s := by
  inst_sat [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sha256.digestSig,
    Spec.Sha256.digestPost, nw, dbytes, Impl.Pbkdf2.Stream.Arm.Hash.buf, sha256H, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using digestSat 32 328

theorem sha256_frameSat : ∃ s, (Spec.Sha256.digestContract Arm.abi sha256H.D sha256OK.SH.H.hash (16 + dbytes sha256H)).pre s := by
  inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, dbytes,
    Impl.Pbkdf2.Stream.Arm.Hash.buf, sha256H, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] using digestFrameSat 32

theorem sha256_digest : Verified Arm.target (digest sha256H) (Spec.Sha256.digestContract Arm.abi 32 Spec.Sha256.hash (16 + dbytes sha256H)) :=
  framed sha256OK (verified sha256OK sha256_checks sha256_sat) sha256_frameSat

/-! ## SHA-384 -/

theorem sha384_checks : Checks sha384H := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha384_sat : ∃ s, (digestScratch sha384H.D sha384OK.SH.H.hash (nw sha384H)).pre s := by
  inst_sat [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sha256.digestSig,
    Spec.Sha256.digestPost, nw, dbytes, Impl.Pbkdf2.Stream.Arm.Hash.buf, sha384H, Pbkdf2.Stream.Arm.sha512H, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using digestSat 48 568

theorem sha384_frameSat : ∃ s, (Spec.Sha256.digestContract Arm.abi sha384H.D sha384OK.SH.H.hash (16 + dbytes sha384H)).pre s := by
  inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, dbytes,
    Impl.Pbkdf2.Stream.Arm.Hash.buf, sha384H, Pbkdf2.Stream.Arm.sha512H, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] using digestFrameSat 48

theorem sha384_digest : Verified Arm.target (digest sha384H) (Spec.Sha512.digestContract Arm.abi 48 Spec.Sha512.sha384 (16 + dbytes sha384H)) :=
  framed sha384OK (verified sha384OK sha384_checks sha384_sat) sha384_frameSat

/-! ## SHA-512 -/

theorem sha512_checks : Checks sha512H' := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha512_sat : ∃ s, (digestScratch sha512H'.D sha512OK.SH.H.hash (nw sha512H')).pre s := by
  inst_sat [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sha256.digestSig,
    Spec.Sha256.digestPost, nw, dbytes, Impl.Pbkdf2.Stream.Arm.Hash.buf, sha512H', Pbkdf2.Stream.Arm.sha512H, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using digestSat 64 568

theorem sha512_frameSat : ∃ s, (Spec.Sha256.digestContract Arm.abi sha512H'.D sha512OK.SH.H.hash (16 + dbytes sha512H')).pre s := by
  inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, dbytes,
    Impl.Pbkdf2.Stream.Arm.Hash.buf, sha512H', Pbkdf2.Stream.Arm.sha512H, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] using digestFrameSat 64

theorem sha512_digest : Verified Arm.target (digest sha512H') (Spec.Sha512.digestContract Arm.abi 64 Spec.Sha512.sha512 (16 + dbytes sha512H')) :=
  framed sha512OK (verified sha512OK sha512_checks sha512_sat) sha512_frameSat

/-! ## SHA-512/224 -/

theorem sha512_224_checks : Checks sha512_224H := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha512_224_sat : ∃ s, (digestScratch sha512_224H.D sha512_224OK.SH.H.hash (nw sha512_224H)).pre s := by
  inst_sat [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sha256.digestSig,
    Spec.Sha256.digestPost, nw, dbytes, Impl.Pbkdf2.Stream.Arm.Hash.buf, sha512_224H, Pbkdf2.Stream.Arm.sha512H, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using digestSat 28 568

theorem sha512_224_frameSat : ∃ s, (Spec.Sha256.digestContract Arm.abi sha512_224H.D sha512_224OK.SH.H.hash (16 + dbytes sha512_224H)).pre s := by
  inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, dbytes,
    Impl.Pbkdf2.Stream.Arm.Hash.buf, sha512_224H, Pbkdf2.Stream.Arm.sha512H, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] using digestFrameSat 28

theorem sha512_224_digest : Verified Arm.target (digest sha512_224H) (Spec.Sha512.digestContract Arm.abi 28 Spec.Sha512.sha512_224 (16 + dbytes sha512_224H)) :=
  framed sha512_224OK (verified sha512_224OK sha512_224_checks sha512_224_sat) sha512_224_frameSat

/-! ## SHA-512/256 -/

theorem sha512_256_checks : Checks sha512_256H := by
  constructor <;> refine ⟨?_, ?_⟩
  taint_decide_all

theorem sha512_256_sat : ∃ s, (digestScratch sha512_256H.D sha512_256OK.SH.H.hash (nw sha512_256H)).pre s := by
  inst_sat [digestScratch, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Spec.Sha256.digestSig,
    Spec.Sha256.digestPost, nw, dbytes, Impl.Pbkdf2.Stream.Arm.Hash.buf, sha512_256H, Pbkdf2.Stream.Arm.sha512H, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using digestSat 32 568

theorem sha512_256_frameSat : ∃ s, (Spec.Sha256.digestContract Arm.abi sha512_256H.D sha512_256OK.SH.H.hash (16 + dbytes sha512_256H)).pre s := by
  inst_sat [Spec.Sha256.digestContract, Spec.Sha256.digestSig, Spec.Sha256.digestPost, dbytes,
    Impl.Pbkdf2.Stream.Arm.Hash.buf, sha512_256H, Pbkdf2.Stream.Arm.sha512H, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] using digestFrameSat 32

theorem sha512_256_digest : Verified Arm.target (digest sha512_256H) (Spec.Sha512.digestContract Arm.abi 32 Spec.Sha512.sha512_256 (16 + dbytes sha512_256H)) :=
  framed sha512_256OK (verified sha512_256OK sha512_256_checks sha512_256_sat) sha512_256_frameSat

end VG.Proof.MdStream.Arm.Digest
