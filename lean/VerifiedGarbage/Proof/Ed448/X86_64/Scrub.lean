module

public import VerifiedGarbage.Impl.Ed448.X86_64.PublicKey
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.HashCT
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.CT
public import VerifiedGarbage.Impl.Ed448.X86_64.Verify
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Verified
import VerifiedGarbage.Proof.X448.X86_64.Pow223
import VerifiedGarbage.Proof.X448.X86_64.Main
import VerifiedGarbage.Proof.X448.X86_64.Freeze
import VerifiedGarbage.Proof.X448.X86_64.Bits
import VerifiedGarbage.Proof.X448.X86_64.Adx.Sqr
import VerifiedGarbage.Proof.X448.X86_64.Adx.Mul
import VerifiedGarbage.Proof.X448.X86_64.AddSub
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed448.X86_64.Words57
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Write
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Math
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Loop
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Load
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Joint
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Init
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Digit
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Coords
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Table
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Register
import VerifiedGarbage.Proof.Ed448.X86_64.Window.DirectKey
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyMain
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyDecode
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyChecks
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Hash
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Calls
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Prune
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.HashCT
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Correct
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.CT
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarVerified
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarMulAdd
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarIO
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.AddSmall
import VerifiedGarbage.Proof.Ed448.X86_64.BaseVerified
import VerifiedGarbage.Proof.Ed448.X86_64.BaseMain
import VerifiedGarbage.Proof.Ed448.X86_64.BaseField
import VerifiedGarbage.Proof.Ed448.X86_64.BaseEncode
import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
import VerifiedGarbage.Proof.Ed448.Wnaf.Recoding
import VerifiedGarbage.Proof.Ed448.VerifyEq
import VerifiedGarbage.Proof.Ed448.Recover
import VerifiedGarbage.Proof.Ed448.Group.Decode
import VerifiedGarbage.Proof.Ed448.DecodeBytes
import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Correct
import VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Layout
import VerifiedGarbage.Proof.Sha3.X86_64.Round
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarLit
public import VerifiedGarbage.Impl.Ed448.X86_64.SignCached
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyVerified
import VerifiedGarbage.Proof.Ed448.X86_64.VariantLit
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLit
import VerifiedGarbage.Proof.Ed448.X86_64.VariantVerified
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Verified
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Variants.Curve448Field.X86_64
import VerifiedGarbage.Proof.X448.X86_64.Lit
import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Order.Field.Basic
import VerifiedGarbage.Proof.Ed448.Facts
import VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Verified
import VerifiedGarbage.Proof.Ed448.X86_64.VariantForLit
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Framework.X86_64.ScrubProved
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Ed448.WholeLocal

/-!
# Ed448 on x86-64, without secret residue

The postconditions of `vg_ed448_public_key` and `vg_ed448_sign_cached` read
the memory on return only within their outputs, and that of
`vg_ed448_verify` not at all (`X86_64.Scrub.PostOut`): each implementation
returns with its whole stack wiped (`X86_64.Scrub.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub
open VG.Proof.Ed448.WholeLocal (bytesAt_congr)

variable (stack : Nat)

theorem publicKeyOut :
    PostOut (Spec.Ed448.publicKeyContract X86_64.abi stack) (Spec.Ed448.publicKeySig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, sd, sc], _ =>
      simp only [Spec.Ed448.publicKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Ed448.bytesAt m₂ o 57 = _
      rw [bytesAt_congr hb.1]
      exact h

theorem signCachedOut :
    PostOut (Spec.Ed448.signCachedContract X86_64.abi stack) (Spec.Ed448.signCachedSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [o, sd, pk, ctx, cl, msg, len, sc], _ =>
      simp only [Spec.Ed448.signCachedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      show Spec.Ed448.bytesAt m₂ o 114 = _
      rw [bytesAt_congr hb.1]
      exact h

theorem verifyOut :
    PostOut (Spec.Ed448.verifyContract X86_64.abi stack) (Spec.Ed448.verifySig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [_, _, _, _, _, _, _], _ => exact h


/-! ## The functions as emitted -/

theorem publicKey_codeSp (v : Impl.Ed448.X86_64.FieldVariant) :
    (Impl.Ed448.X86_64.publicKeyFor v).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  cases v <;> sp_safe

/-- `vg_ed448_public_key` as emitted (`Impl.Ed448.X86_64.Fn.publicKey`), its cleanup included, meets its contract
in constant time and returns without secret residue. -/
theorem publicKey_scrubbed (v : Impl.Ed448.X86_64.FieldVariant) :
    VerifiedScrubbed X86_64.target (Impl.Ed448.X86_64.Fn.publicKey v)
      (Spec.Ed448.publicKeyApi.contract X86_64.abi 104) 0 := by
  cases v
  · exact X86_64.Scrub.verifiedScrubbedAll (api := Spec.Ed448.publicKeyApi)
      { code := _
        stack := 104
        verified := Proof.Ed448.X86_64.PublicKey.publicKey_verified (v := .scalar) Proof.Ed448.baseLadder_ok
        spSafe := publicKey_codeSp .scalar } .sse (publicKeyOut _)
  · exact X86_64.Scrub.verifiedScrubbedAll (api := Spec.Ed448.publicKeyApi)
      { code := _
        stack := 104
        verified := Proof.Ed448.X86_64.PublicKey.publicKey_verified (v := .adx) Proof.Ed448.baseLadder_ok
        spSafe := publicKey_codeSp .adx } .sse (publicKeyOut _)

theorem publicKey_spSafe (v : Impl.Ed448.X86_64.FieldVariant) :
    (Impl.Ed448.X86_64.Fn.publicKey v).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe (publicKey_codeSp v)

theorem signCached_codeSp (v : Impl.Ed448.X86_64.FieldVariant) :
    (Impl.Ed448.X86_64.SignCached.signCachedFor v).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  cases v <;> sp_safe

/-- `vg_ed448_sign_cached` as emitted (`Impl.Ed448.X86_64.SignCached.Fn.signCached`), its cleanup included, meets its contract
in constant time and returns without secret residue. -/
theorem signCached_scrubbed (v : Impl.Ed448.X86_64.FieldVariant) :
    VerifiedScrubbed X86_64.target (Impl.Ed448.X86_64.SignCached.Fn.signCached v)
      (Spec.Ed448.signCachedApi.contract X86_64.abi 464) 0 := by
  cases v
  · exact X86_64.Scrub.verifiedScrubbedAll (api := Spec.Ed448.signCachedApi)
      { code := _
        stack := 464
        verified := Proof.Ed448.X86_64.SignCached.signCached_verified (Proof.Ed448.X86_64.scalarBaseFor_ok .scalar Proof.Ed448.baseLadder_ok) (Proof.Ed448.X86_64.scalarBaseFor_ct .scalar)
        spSafe := signCached_codeSp .scalar } .sse (signCachedOut _)
  · exact X86_64.Scrub.verifiedScrubbedAll (api := Spec.Ed448.signCachedApi)
      { code := _
        stack := 464
        verified := Proof.Ed448.X86_64.SignCached.signCached_verified (Proof.Ed448.X86_64.scalarBaseFor_ok .adx Proof.Ed448.baseLadder_ok) (Proof.Ed448.X86_64.scalarBaseFor_ct .adx)
        spSafe := signCached_codeSp .adx } .sse (signCachedOut _)

theorem signCached_spSafe (v : Impl.Ed448.X86_64.FieldVariant) :
    (Impl.Ed448.X86_64.SignCached.Fn.signCached v).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe (signCached_codeSp v)

theorem verify_codeSp (v : Impl.Ed448.X86_64.FieldVariant) :
    (Impl.Ed448.X86_64.Verify.verifyFor v).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  cases v <;> sp_safe

/-- `vg_ed448_verify` as emitted (`Impl.Ed448.X86_64.Verify.Fn.verify`), its cleanup included, meets its contract
in constant time and returns without secret residue. -/
theorem verify_scrubbed (v : Impl.Ed448.X86_64.FieldVariant) :
    VerifiedScrubbed X86_64.target (Impl.Ed448.X86_64.Verify.Fn.verify v)
      (Spec.Ed448.verifyApi.contract X86_64.abi 272) 32 := by
  cases v
  · exact X86_64.Scrub.verifiedScrubbedAll (api := Spec.Ed448.verifyApi)
      { code := _
        stack := 272
        verified := Proof.Ed448.X86_64.Verify.verify_verified (Proof.Ed448.X86_64.verifyEquationFor_ok .scalar Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok) (Proof.Ed448.X86_64.verifyEquationFor_ct .scalar Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok)
        spSafe := verify_codeSp .scalar } .sse (verifyOut _)
  · exact X86_64.Scrub.verifiedScrubbedAll (api := Spec.Ed448.verifyApi)
      { code := _
        stack := 272
        verified := Proof.Ed448.X86_64.Verify.verify_verified (Proof.Ed448.X86_64.verifyEquationFor_ok .adx Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok) (Proof.Ed448.X86_64.verifyEquationFor_ct .adx Proof.Ed448.recover_ok Proof.Ed448.verifyEq_ok)
        spSafe := verify_codeSp .adx } .sse (verifyOut _)

theorem verify_spSafe (v : Impl.Ed448.X86_64.FieldVariant) :
    (Impl.Ed448.X86_64.Verify.Fn.verify v).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe (verify_codeSp v)

end VG.Proof.Ed448.X86_64.Scrub
