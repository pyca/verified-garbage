module

public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Impl.X448.AArch64.Base
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Table
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
public import VerifiedGarbage.Proof.Ed448.AArch64.PublicKey.Verified
public import VerifiedGarbage.Proof.Ed448.AArch64.SignCached.Verified
public import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Verified
import VerifiedGarbage.Proof.Ed448.AArch64.BaseVerified
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Verified
import VerifiedGarbage.Proof.Ed448.Facts
import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Main
import VerifiedGarbage.Proof.Sha3.AArch64.Scrub
public import VerifiedGarbage.Impl.Ed448.AArch64.PublicKey
public import VerifiedGarbage.Impl.Ed448.AArch64.SignCached
public import VerifiedGarbage.Impl.Ed448.AArch64.Verify
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Ed448.WholeLocal

/-!
# Ed448 on AArch64, without secret residue

The postconditions of `vg_ed448_public_key` and `vg_ed448_sign_cached` read
the memory on return only within their outputs, and that of
`vg_ed448_verify` not at all (`ScrubAll.ScrubAllOk`, from
`Proof.Ed448.WholeLocal`): each function as emitted
(`Impl.Ed448.AArch64.Fn`), generic over the Keccak permutation it calls,
returns with every register it may leave secret cleared and its whole stack
zeroed. `Fn` below has the theorem of each, which its registration binds.

What the cleanup needs of the code (`ScrubAll.scrubSide`) is proved of each
function's own instructions here, once, with a permutation that does nothing
in its place (`Proof.Sha3.AArch64.Scrub.stub`), of the sponge's functions it
calls in `Proof.Sha3.AArch64.Scrub`, and of each implementation of the
permutation where it is defined (`Permutation.scrub`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll

theorem publicKeyOk : ScrubAllOk
    (Spec.Ed448.publicKeyContract (AArch64.abi.withConsts Impl.X448.AArch64.Base.combConsts) 352)
    352 (Spec.Ed448.publicKeySig.retBits AArch64.abi.ptrBits) :=
  scrubAllOk_consts (sig := Spec.Ed448.publicKeySig)
    (c₀ := (Impl.X448.AArch64.Base.combSym, Impl.X448.AArch64.Base.combWords)) (cs := []) (W := 352)
    (by decide) (by decide) (Nat.le_refl _) (WholeLocal.publicKeyPostOut_local _)

theorem signCachedOk : ScrubAllOk
    (Spec.Ed448.signCachedContract (AArch64.abi.withConsts Impl.X448.AArch64.Base.combConsts) 352)
    352 (Spec.Ed448.signCachedSig.retBits AArch64.abi.ptrBits) :=
  scrubAllOk_consts (sig := Spec.Ed448.signCachedSig)
    (c₀ := (Impl.X448.AArch64.Base.combSym, Impl.X448.AArch64.Base.combWords)) (cs := []) (W := 352)
    (by decide) (by decide) (Nat.le_refl _) (WholeLocal.signCachedPostOut_local _)

theorem verifyOk : ScrubAllOk
    (Spec.Ed448.verifyContract (AArch64.abi.withConsts Impl.Ed448.AArch64.Sparse.baseConsts) 352)
    352 (Spec.Ed448.verifySig.retBits AArch64.abi.ptrBits) :=
  scrubAllOk_consts (sig := Spec.Ed448.verifySig)
    (c₀ := (Impl.Ed448.AArch64.Sparse.baseSym, Impl.Ed448.AArch64.Sparse.baseWords)) (cs := []) (W := 352)
    (by decide) (by decide) (Nat.le_refl _) (WholeLocal.verifyPostOut_local _)

/-! ## What the cleanup needs of the code -/

open VG.Proof.Sha3.AArch64 (Permutation)
open VG.Proof.Sha3.AArch64.Scrub (stub absorbWith_side padWith_side squeezeWith_side)
open VG.Impl.Ed448.AArch64

private theorem publicKey_all {p : Instr → Bool} (c : Impl.Sha3.AArch64.Callee)
    (h0 : sideAll p (PublicKey.publicKeyWith stub) = true)
    (ha : sideAll p (Impl.Sha3.AArch64.Stream.absorbWith c) = true)
    (hp : sideAll p (Impl.Sha3.AArch64.Stream.padWith c) = true)
    (hs : sideAll p (Impl.Sha3.AArch64.Stream.squeezeWith c) = true) :
    sideAll p (PublicKey.publicKeyWith c) = true := by
  simp only [PublicKey.publicKeyWith, Impl.Ed25519.AArch64.Whole.wrap, PublicKey.body, PublicKey.hash,
    Impl.Ed25519.AArch64.Whole.callWith, sideAll, Bool.and_eq_true] at h0 ⊢
  simp only [h0, ha, hp, hs, and_self]

private theorem signCached_all {p : Instr → Bool} (c : Impl.Sha3.AArch64.Callee)
    (h0 : sideAll p (SignCached.signCachedWith stub) = true)
    (ha : sideAll p (Impl.Sha3.AArch64.Stream.absorbWith c) = true)
    (hp : sideAll p (Impl.Sha3.AArch64.Stream.padWith c) = true)
    (hs : sideAll p (Impl.Sha3.AArch64.Stream.squeezeWith c) = true) :
    sideAll p (SignCached.signCachedWith c) = true := by
  simp only [SignCached.signCachedWith, Impl.Ed25519.AArch64.Whole.wrap, SignCached.body,
    SignCached.seedHash, SignCached.nonceHash, SignCached.chalHash, Impl.Ed448.AArch64.Whole.zeroSt,
    Impl.Ed448.AArch64.Whole.kabs, Impl.Ed448.AArch64.Whole.kpad, Impl.Ed448.AArch64.Whole.ksqz,
    Impl.Ed448.AArch64.Whole.callS, sideAll, Bool.and_eq_true] at h0 ⊢
  simp only [h0, ha, hp, hs, and_self]

private theorem verify_all {p : Instr → Bool} (c : Impl.Sha3.AArch64.Callee)
    (h0 : sideAll p (Verify.verifyWith stub) = true)
    (ha : sideAll p (Impl.Sha3.AArch64.Stream.absorbWith c) = true)
    (hp : sideAll p (Impl.Sha3.AArch64.Stream.padWith c) = true)
    (hs : sideAll p (Impl.Sha3.AArch64.Stream.squeezeWith c) = true) :
    sideAll p (Verify.verifyWith c) = true := by
  simp only [Verify.verifyWith, Impl.Ed25519.AArch64.Whole.wrap, Verify.body, Verify.hash,
    Impl.Ed448.AArch64.Whole.zeroSt, Impl.Ed448.AArch64.Whole.kabs, Impl.Ed448.AArch64.Whole.kpad,
    Impl.Ed448.AArch64.Whole.ksqz, Impl.Ed448.AArch64.Whole.callS, sideAll, Bool.and_eq_true] at h0 ⊢
  simp only [h0, ha, hp, hs, and_self]

/-! The functions' own instructions write only the registers `Impl/` states
(`Impl.Ed448.AArch64.Fn.own`). -/

private theorem publicKey_own :
    calleeSide (PublicKey.publicKeyWith stub) Impl.Ed448.AArch64.Fn.own = true := by
  lit_decide

private theorem signCached_own :
    calleeSide (SignCached.signCachedWith stub) Impl.Ed448.AArch64.Fn.own = true := by
  lit_decide

private theorem verify_own :
    calleeSide (Verify.verifyWith stub) Impl.Ed448.AArch64.Fn.own = true := by
  lit_decide

theorem publicKey_side (v : Permutation) :
    scrubSide (PublicKey.publicKeyWith v.callee) 352 0
      (Impl.Ed448.AArch64.Fn.own.union v.callee.clear) [] = true := by
  refine scrubSide_union (by decide) ?_ (by decide)
    (publicKey_all v.callee (sideAll_union_left publicKey_own) (absorbWith_side v (by decide))
      (padWith_side v (by decide)) (squeezeWith_side v (by decide))) (by decide)
  simp only [PublicKey.publicKeyWith, Impl.Ed25519.AArch64.Whole.wrap, Code.aarch64Depth,
    Instr.frameUnits, Nat.zero_max, Nat.reduceDiv]
  exact Nat.le_trans (Nat.mul_le_mul_left 16
    (Nat.add_le_add_right (Nat.add_le_add_right (Proof.Ed448.AArch64.PublicKey.body_depth v) 20) 1))
    (by decide)

theorem signCached_side (v : Permutation) :
    scrubSide (SignCached.signCachedWith v.callee) 352 0
      (Impl.Ed448.AArch64.Fn.own.union v.callee.clear) [] = true := by
  refine scrubSide_union (by decide) ?_ (by decide)
    (signCached_all v.callee (sideAll_union_left signCached_own) (absorbWith_side v (by decide))
      (padWith_side v (by decide)) (squeezeWith_side v (by decide))) (by decide)
  simp only [SignCached.signCachedWith, Impl.Ed25519.AArch64.Whole.wrap, Code.aarch64Depth,
    Instr.frameUnits, Nat.zero_max, Nat.reduceDiv]
  exact Nat.le_trans (Nat.mul_le_mul_left 16
    (Nat.add_le_add_right (Nat.add_le_add_right (Proof.Ed448.AArch64.SignCached.body_depth v) 20) 1))
    (by decide)

theorem verify_side (v : Permutation) :
    scrubSide (Verify.verifyWith v.callee) 352 32
      (Impl.Ed448.AArch64.Fn.own.union v.callee.clear) [] = true := by
  refine scrubSide_union (by decide) ?_ (by decide)
    (verify_all v.callee (sideAll_union_left verify_own) (absorbWith_side v (by decide))
      (padWith_side v (by decide)) (squeezeWith_side v (by decide))) (by decide)
  simp only [Verify.verifyWith, Impl.Ed25519.AArch64.Whole.wrap, Code.aarch64Depth,
    Instr.frameUnits, Nat.zero_max, Nat.max_zero, Nat.reduceDiv]
  exact Nat.le_trans (Nat.mul_le_mul_left 16
    (Nat.add_le_add_right (Nat.add_le_add_right (Proof.Ed448.AArch64.Verify.body_depth v) 20) 1))
    (by decide)

end VG.Proof.Ed448.AArch64.Scrub

/-! ## The functions

Of each function `Artifacts/Ed448/AArch64.lean` registers, with the
implementation `v` of the permutation: the code that is emitted
(`Impl.Ed448.AArch64.Fn`) meets the function's contract in constant time and
returns without secret residue. -/

namespace VG.Proof.Ed448.AArch64.Fn

open VG.AArch64 VG.AArch64.ScrubAll
open VG.Proof.Sha3.AArch64 (Permutation)

theorem publicKey (v : Permutation) :
    VerifiedScrubbed target (Impl.Ed448.AArch64.Fn.publicKey v.callee)
      (Spec.Ed448.publicKeyContract (abi.withConsts Impl.X448.AArch64.Base.combConsts) 352) 0 :=
  verifiedScrubbed (api := Spec.Ed448.publicKeyApi)
    { code := Impl.Ed448.AArch64.PublicKey.publicKeyWith v.callee,
      verified := Proof.Ed448.AArch64.PublicKey.publicKey_verified v Proof.Ed448.AArch64.scalarBase_baseOk }
    _ Scrub.publicKeyOk (Scrub.publicKey_side v)

theorem signCached (v : Permutation) :
    VerifiedScrubbed target (Impl.Ed448.AArch64.Fn.signCached v.callee)
      (Spec.Ed448.signCachedContract (abi.withConsts Impl.X448.AArch64.Base.combConsts) 352) 0 :=
  verifiedScrubbed (api := Spec.Ed448.signCachedApi)
    { code := Impl.Ed448.AArch64.SignCached.signCachedWith v.callee,
      verified := Proof.Ed448.AArch64.SignCached.signCached_verified v Proof.Ed448.AArch64.scalarBase_baseOk }
    _ Scrub.signCachedOk (Scrub.signCached_side v)

theorem verify (v : Permutation) :
    VerifiedScrubbed target (Impl.Ed448.AArch64.Fn.verify v.callee)
      (Spec.Ed448.verifyContract (abi.withConsts Impl.Ed448.AArch64.Sparse.baseConsts) 352) 32 :=
  verifiedScrubbed (api := Spec.Ed448.verifyApi)
    { code := Impl.Ed448.AArch64.Verify.verifyWith v.callee,
      verified := Proof.Ed448.AArch64.Verify.verify_verified v
        (Proof.Ed448.AArch64.Sparse.verified_eqOk Proof.Ed448.recover_ok) }
    _ Scrub.verifyOk (Scrub.verify_side v)

end VG.Proof.Ed448.AArch64.Fn
