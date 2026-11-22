module

public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Rsa.X86.ScrubOut
public import VerifiedGarbage.Impl.Dsa.X86.Fn
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Proof.Dsa.X86.CheckingVerified
public import VerifiedGarbage.Proof.Dsa.X86.DerivingVerified
public import VerifiedGarbage.Proof.Dsa.X86.Comb.KeyVerified
public import VerifiedGarbage.Proof.Dsa.X86.RandomSignInstance
public import VerifiedGarbage.Proof.Dsa.X86.PrevalidatedVerified
public import VerifiedGarbage.Proof.Dsa.X86.ValidatePrivateVerified
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Init
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Verified
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Rsa.X86.ScrubOut
meta import VerifiedGarbage.Impl.Dsa.X86.Fn
meta import VerifiedGarbage.Spec.Dsa.Prevalidated
meta import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
meta import VerifiedGarbage.Spec.Dsa.Generate
meta import VerifiedGarbage.Spec.Dsa.Derive
meta import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
meta import VerifiedGarbage.Proof.Dsa.X86.CheckingVerified
meta import VerifiedGarbage.Proof.Dsa.X86.DerivingVerified
meta import VerifiedGarbage.Proof.Dsa.X86.Comb.KeyVerified
meta import VerifiedGarbage.Proof.Dsa.X86.RandomSignInstance
meta import VerifiedGarbage.Proof.Dsa.X86.PrevalidatedVerified
meta import VerifiedGarbage.Proof.Dsa.X86.ValidatePrivateVerified
meta import VerifiedGarbage.Proof.Dsa.X86.Generation.Init
meta import VerifiedGarbage.Proof.Dsa.X86.Generation.Verified
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# DSA on x86 (32-bit), without secret residue

Each of DSA's functions is emitted with its cleanup (`Impl.Dsa.X86.Fn`):
`vg_dsa_parameter_search_init`, which calls nothing and has no frame, with
the tail that clears the registers (`Impl.Scrub.X86.scrub`), and the others,
which have frames and calls, also with the zeroing of the stack their
contracts reserve (`Impl.Scrub.X86.scrubAll`). Each returns without secret
residue (`<f>_scrubbed`, the theorem its registration binds).

The postconditions of the validations and of the verification do not read
the memory on return; those of key generation, key derivation and signing
read it only at `out` (as many octets as `out_len`, the buffer's size) and,
but for derivation, at `used`; that of the parameter search at `out`, `used`
and `state` (`X86.Scrub.PostOut`).

The parameter search is generic over SHA-1's and SHA-256's implementations
and the Miller–Rabin round's. What its cleanup needs of its code holds of it
with every implementation (`search_scrub`): its code with holes where each
implementation's code goes, of the stack each states (`holeStub`: 0 bytes for
the compression functions, 96 for the round), which the kernel evaluates
once (`search_side`), and `FillB` (`search_fill`). The round is called off
the search's deepest stack path, so the holes have their own budgets.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.Rsa.X86.Scrub

/-! ## Postconditions -/

theorem validatePublicKeyOut (stack : Nat) :
    PostOut (Spec.Dsa.validatePublicKeyContract abi stack) (Spec.Dsa.validatePublicKeySig.retBits 32) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [_, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem validatePrivateKeyOut (stack : Nat) :
    PostOut (Spec.Dsa.validatePrivateKeyContract abi stack) (Spec.Dsa.validatePrivateKeySig.retBits 32) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [_, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem verifyPrevalidatedOut (stack : Nat) :
    PostOut (Spec.Dsa.verifyPrevalidatedContract abi stack) (Spec.Dsa.verifySig.retBits 32) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [_, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem randomSignPrevalidatedOut (stack : Nat) :
    PostOut (Spec.Dsa.randomSignPrevalidatedContract abi stack) (Spec.Dsa.randomSignSig.retBits 32) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [out, outLen, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.randomSignSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [bytesAt_of hb.1 (toNat_sw_le abi ScrubAbi.plain outLen), wordsAt_of hb.2.1]
      exact h

theorem generateKeyOut (stack : Nat) :
    PostOut (Spec.Dsa.generateKeyContract abi stack) (Spec.Dsa.generateKeySig.retBits 32) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [out, outLen, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.generateKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [bytesAt_of hb.1 (toNat_sw_le abi ScrubAbi.plain outLen), wordsAt_of hb.2.1]
      exact h

theorem deriveKeyOut (stack : Nat) :
    PostOut (Spec.Dsa.deriveKeyContract abi stack) (Spec.Dsa.deriveKeySig.retBits 32) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [out, outLen, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.deriveKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [bytesAt_of hb.1 (toNat_sw_le abi ScrubAbi.plain outLen)]
      exact h

theorem parameterSearchOut {A : Abi isa} (hA : ScrubAbi A) (stack : Nat) :
    PostOut (Spec.Dsa.parameterSearchContract A stack) (Spec.Dsa.parameterSearchSig.retBits A.ptrBits) :=
  postOut_of_local (leak := some _) hA fun
    | [out, outLen, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Dsa.parameterSearchSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [bytesAt_of hb.1 (toNat_sw_le A hA outLen), wordsAt_of hb.2.1, wordsAt_of hb.2.2.2.2]
      exact h

/-! ## The functions that call no implementation of a variant -/

theorem generateKey_sp : Impl.Dsa.X86.Comb.generateKey.all (fun i => !isa.writesSp i) = true := by sp_safe

theorem deriveKey_sp : Impl.Dsa.X86.Generate.deriveKey.all (fun i => !isa.writesSp i) = true := by sp_safe

theorem validatePrivateKey_sp :
    Impl.Dsa.X86.PrevalidatedSign.validate.all (fun i => !isa.writesSp i) = true := by sp_safe

theorem randomSignPrevalidated_sp :
    (Impl.Dsa.X86.RandomSign.code prevalidatedSignFn.name prevalidatedSignFn.code).all
      (fun i => !isa.writesSp i) = true := by sp_safe

theorem validatePublicKey_sp : Impl.Dsa.X86.Prevalidated.validate.all (fun i => !isa.writesSp i) = true := by
  sp_safe

theorem verifyPrevalidated_sp : Impl.Dsa.X86.Prevalidated.verify.all (fun i => !isa.writesSp i) = true := by
  sp_safe

theorem parameterInit_sp : Impl.Dsa.X86.Generation.init.all (fun i => !isa.writesSp i) = true := by sp_safe

/-- `vg_dsa_generate_key`, with its cleanup, returns without secret residue. -/
theorem generateKey_scrubbed :
    VerifiedScrubbed target Impl.Dsa.X86.Fn.generateKey (Spec.Dsa.generateKeyContract abi 232) 32 :=
  verifiedScrubbedAll (api := Spec.Dsa.generateKeyApi)
    { code := Impl.Dsa.X86.Comb.generateKey
      verified := Proof.Dsa.X86.Comb.key_verified
      spSafe := generateKey_sp }
    (generateKeyOut _)

theorem generateKey_spSafe : Impl.Dsa.X86.Fn.generateKey.all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe generateKey_sp

/-- `vg_dsa_derive_key`, with its cleanup, returns without secret residue. -/
theorem deriveKey_scrubbed :
    VerifiedScrubbed target Impl.Dsa.X86.Fn.deriveKey (Spec.Dsa.deriveKeyContract abi 108) 32 :=
  verifiedScrubbedAll (api := Spec.Dsa.deriveKeyApi)
    { code := Impl.Dsa.X86.Generate.deriveKey
      verified := Proof.Dsa.X86.deriving_verified
      spSafe := deriveKey_sp }
    (deriveKeyOut _)

theorem deriveKey_spSafe : Impl.Dsa.X86.Fn.deriveKey.all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe deriveKey_sp

/-- `vg_dsa_validate_private_key`, with its cleanup, returns without secret residue. -/
theorem validatePrivateKey_scrubbed :
    VerifiedScrubbed target Impl.Dsa.X86.Fn.validatePrivateKey (Spec.Dsa.validatePrivateKeyContract abi 108) 32 :=
  verifiedScrubbedAll (api := Spec.Dsa.validatePrivateKeyApi)
    { code := Impl.Dsa.X86.PrevalidatedSign.validate
      verified := Proof.Dsa.X86.privateValidating_verified
      spSafe := validatePrivateKey_sp }
    (validatePrivateKeyOut _)

theorem validatePrivateKey_spSafe : Impl.Dsa.X86.Fn.validatePrivateKey.all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe validatePrivateKey_sp

/-- `vg_dsa_sign_random_prevalidated`, with its cleanup, returns without secret residue. -/
theorem randomSignPrevalidated_scrubbed :
    VerifiedScrubbed target Impl.Dsa.X86.Fn.randomSignPrevalidated
      (Spec.Dsa.randomSignPrevalidatedContract abi 232) 32 :=
  verifiedScrubbedAll (api := Spec.Dsa.randomSignPrevalidatedApi)
    { code := Impl.Dsa.X86.RandomSign.code prevalidatedSignFn.name prevalidatedSignFn.code
      verified := Proof.Dsa.X86.randomSigningPrevalidated_verified
      spSafe := randomSignPrevalidated_sp }
    (randomSignPrevalidatedOut _)

theorem randomSignPrevalidated_spSafe :
    Impl.Dsa.X86.Fn.randomSignPrevalidated.all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe randomSignPrevalidated_sp

/-- `vg_dsa_validate_public_key`, with its cleanup, returns without secret residue. -/
theorem validatePublicKey_scrubbed :
    VerifiedScrubbed target Impl.Dsa.X86.Fn.validatePublicKey (Spec.Dsa.validatePublicKeyContract abi 108) 32 :=
  verifiedScrubbedAll (api := Spec.Dsa.validatePublicKeyApi)
    { code := Impl.Dsa.X86.Prevalidated.validate
      verified := Proof.Dsa.X86.validating_verified
      spSafe := validatePublicKey_sp }
    (validatePublicKeyOut _)

theorem validatePublicKey_spSafe : Impl.Dsa.X86.Fn.validatePublicKey.all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe validatePublicKey_sp

/-- `vg_dsa_verify_prevalidated`, with its cleanup, returns without secret residue. -/
theorem verifyPrevalidated_scrubbed :
    VerifiedScrubbed target Impl.Dsa.X86.Fn.verifyPrevalidated (Spec.Dsa.verifyPrevalidatedContract abi 108) 32 :=
  verifiedScrubbedAll (api := Spec.Dsa.verifyPrevalidatedApi)
    { code := Impl.Dsa.X86.Prevalidated.verify
      verified := Proof.Dsa.X86.prevalidated_verified
      spSafe := verifyPrevalidated_sp }
    (verifyPrevalidatedOut _)

theorem verifyPrevalidated_spSafe : Impl.Dsa.X86.Fn.verifyPrevalidated.all (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe verifyPrevalidated_sp

/-- `vg_dsa_parameter_search_init`, with its cleanup, returns without secret residue. -/
theorem parameterInit_scrubbed :
    VerifiedScrubbed target Impl.Dsa.X86.Fn.parameterInit (Spec.Dsa.parameterInitContract abi) 32 :=
  verifiedScrubbed (api := Spec.Dsa.parameterInitApi)
    { code := Impl.Dsa.X86.Generation.init
      verified := Proof.Dsa.X86.Generation.Init.init_verified
      spSafe := parameterInit_sp }

theorem parameterInit_spSafe : Impl.Dsa.X86.Fn.parameterInit.all (fun i => !isa.writesSp i) = true :=
  scrub_spSafe parameterInit_sp

/-! ## The parameter search, whatever the implementations -/

open VG.Impl.Dsa.X86.Generation (Geo)
open VG.Proof.Dsa.X86.Generation (geo1 geo256)
open VG.Proof.MillerRabin.X86 (RoundImpl montName montCode)

/-- The geometry `(pLen, qLen)` of the search with holes: the hash `H`'s
compression function and the Miller–Rabin round `round` (`geo` with any
implementation, its names empty). -/
def geoStub (pLen qLen : Nat) (H : Impl.Pbkdf2.Md.X86.Hash) (iv : List (BitVec 32)) (round : Prog isa) : Geo where
  pLen := pLen
  qLen := qLen
  e := (8 * pLen - 8 * qLen) / 32 + 1
  H := H
  iv := iv
  qName := ""
  qCode := Impl.Dsa.X86.ProbablePrime.code (8 * qLen) montName montCode "" round
  pName := ""
  pCode := Impl.Dsa.X86.ProbablePrime.code (8 * pLen) montName montCode "" round
  checkName := "vg_dsa_check_parameters"
  checkCode := Impl.Dsa.X86.Generate.checkParameters

/-- `vg_dsa_parameter_search` with holes for SHA-1's and SHA-256's
compression functions (no stack) and the Miller–Rabin round (96 bytes). -/
def searchStub : Prog isa :=
  Impl.Dsa.X86.Generation.code
    (geoStub 128 20 (Proof.Sha1.X86.Variants.mdHash "" "" (holeStub 0) (.block []) (.block []))
      Spec.Sha1.H0.toList (holeStub 96))
    (geoStub 256 32 (Proof.Sha256.X86.Variants.mdHash "" "" (holeStub 0) (.block []) (.block []))
      Spec.Sha256.H0.toList (holeStub 96))
    (geoStub 384 32 (Proof.Sha256.X86.Variants.mdHash "" "" (holeStub 0) (.block []) (.block []))
      Spec.Sha256.H0.toList (holeStub 96))

-- The stub as a literal, for the kernel's evaluation.
theorem search_side : scrubFSide searchStub [] 216 = true := by lit_decide

/-- `FillB` of a sequence, from `FillB` of its elements. -/
theorem fillB_seqs : ∀ {l l' : List (Prog isa)}, List.Forall₂ FillB l l' →
    FillB (Impl.Dsa.X86.Generation.seqs l) (Impl.Dsa.X86.Generation.seqs l')
  | [], [], .nil => FillB.refl _
  | [_], [_], .cons h .nil => h
  | _ :: _ :: _, _ :: _ :: _, .cons h t => FillB.seq h (fillB_seqs t)

theorem forall₂_map_append {f f' : Nat → Prog isa} {x x' : Prog isa} (h : ∀ j, FillB (f j) (f' j))
    (hx : FillB x x') : ∀ L : List Nat, List.Forall₂ FillB (L.map f ++ [x]) (L.map f' ++ [x'])
  | [] => .cons hx .nil
  | j :: L => .cons (h j) (forall₂_map_append h hx L)

/-- `FillB` of the hashes of p's candidate (`Geo.pX`), from `FillB` of their loop's hash. -/
theorem pX_fill {g g' : Geo} (hc : g.count = g'.count) (hl : g.pLen = g'.pLen) (hq : g.qLen = g'.qLen)
    (hh : FillB g.pHash g'.pHash) : FillB g.pX g'.pX := by
  unfold Impl.Dsa.X86.Generation.Geo.pX Impl.Dsa.X86.Generation.Geo.pNext
  rw [hc, hl, hq]
  exact FillB.seq (FillB.refl _) (FillB.seq (FillB.loop _ (FillB.seq hh (FillB.refl _))) (FillB.refl _))

/-- `g` with the implementations it calls, and their names, replaced: the
compression function, SHA's streaming functions (which the search does not
call), and the probable-prime tests (which call the Miller–Rabin round). -/
def fillGeo (g : Geo) (cN : String) (cC : Prog isa) (st : Impl.Pbkdf2.Stream.X86.Hash)
    (qN : String) (qC : Prog isa) (pN : String) (pC : Prog isa) : Geo :=
  { g with H := { g.H with st := st, compN := cN, compC := cC }, qName := qN, qCode := qC, pName := pN, pCode := pC }

/-- The search of one geometry, whatever the implementations it calls: walked
once, over any geometry, so that the kernel compares only the code that
differs. -/
theorem generate_fill (g : Geo) {cN qN pN : String} {cC qC pC : Prog isa} {st : Impl.Pbkdf2.Stream.X86.Hash}
    (hc : FillB g.H.compC cC) (hq : FillB g.qCode qC) (hp : FillB g.pCode pC) :
    FillB g.generate (fillGeo g cN cC st qN qC pN pC).generate := by
  unfold Impl.Dsa.X86.Generation.Geo.generate
  repeat' (first
    | with_reducible exact FillB.refl _
    | exact hc
    | exact hq
    | exact hp
    | exact pX_fill rfl rfl rfl (by
        unfold Impl.Dsa.X86.Generation.Geo.pHash
        repeat' (first
          | with_reducible exact FillB.refl _
          | exact hc
          | refine FillB.seq ?_ ?_
          | refine FillB.ite _ ?_ ?_
          | refine FillB.loop _ ?_
          | refine FillB.call _ _ ?_
          | refine FillB.frame _ _ ?_
          | exact FillB.refl _))
    | refine FillB.seq ?_ ?_
    | refine FillB.ite _ ?_ ?_
    | refine FillB.loop _ ?_
    | refine FillB.call _ _ ?_
    | refine FillB.frame _ _ ?_
    | exact FillB.refl _)

/-- The search, from the search of each geometry. -/
theorem code_fill {g1 g2 g3 g1' g2' g3' : Geo} (h1 : FillB g1.generate g1'.generate)
    (h2 : FillB g2.generate g2'.generate) (h3 : FillB g3.generate g3'.generate) :
    FillB (Impl.Dsa.X86.Generation.code g1 g2 g3) (Impl.Dsa.X86.Generation.code g1' g2' g3') :=
  .frame _ _ (.seq (.seq (.refl _) (.seq (.refl _) (.seq (.refl _) (.ite _ h1 (.seq (.refl _) (.ite _ h2 h3))))))
    (.refl _))

/-- A probable-prime test, whatever the Miller–Rabin round it calls. -/
theorem probablePrime_fill (bits : Nat) (mN : String) (mC : Prog isa) {rN rN' : String} {r r' : Prog isa}
    (hr : FillB r r') :
    FillB (Impl.Dsa.X86.ProbablePrime.code bits mN mC rN r) (Impl.Dsa.X86.ProbablePrime.code bits mN mC rN' r') := by
  unfold Impl.Dsa.X86.ProbablePrime.code
  repeat' (first
    | with_reducible exact FillB.refl _
    | exact hr
    | refine FillB.seq ?_ ?_
    | refine FillB.ite _ ?_ ?_
    | refine FillB.loop _ ?_
    | refine FillB.call _ _ ?_
    | refine FillB.frame _ _ ?_
    | exact FillB.refl _)

theorem search_fill (v1 : Proof.Sha1.X86.Variants.Backend) (v256 : Proof.Sha256.X86.Variants.Backend)
    (v : RoundImpl) (h1 : calleeSide v1.cmpC 0 = true) (h256 : calleeSide v256.cmpC 0 = true)
    (hr : calleeSide v.code 96 = true) :
    FillB searchStub (Impl.Dsa.X86.Generation.code (geo1 v1 v) (geo256 256 v256 v) (geo256 384 v256 v)) := by
  obtain hr' : FillB (holeStub 96) v.code := .hole hr
  exact code_fill
    (generate_fill (cN := v1.cmpN) (st := (geo1 v1 v).H.st) (qN := (geo1 v1 v).qName) (pN := (geo1 v1 v).pName)
      _ (.hole h1) (probablePrime_fill _ _ _ hr') (probablePrime_fill _ _ _ hr'))
    (generate_fill (cN := v256.cmpN) (st := (geo256 256 v256 v).H.st) (qN := (geo256 256 v256 v).qName)
      (pN := (geo256 256 v256 v).pName) _ (.hole h256) (probablePrime_fill _ _ _ hr') (probablePrime_fill _ _ _ hr'))
    (generate_fill (cN := v256.cmpN) (st := (geo256 384 v256 v).H.st) (qN := (geo256 384 v256 v).qName)
      (pN := (geo256 384 v256 v).pName) _ (.hole h256) (probablePrime_fill _ _ _ hr') (probablePrime_fill _ _ _ hr'))

/-- `scrubFSide` of `vg_dsa_parameter_search`, whatever the implementations
of SHA-1, SHA-256 and the Miller–Rabin round. -/
theorem search_scrub (v1 : Proof.Sha1.X86.Variants.Backend) (v256 : Proof.Sha256.X86.Variants.Backend)
    (v : RoundImpl) :
    scrubFSide (Impl.Dsa.X86.Generation.code (geo1 v1 v) (geo256 256 v256 v) (geo256 384 v256 v)) [] 216 = true :=
  scrubFSide_of_fillB (search_fill v1 v256 v (calleeSide_of_eq v1.cmpStack v1.cmpScrub)
    (calleeSide_of_eq v256.cmpStack v256.cmpScrub) (calleeSide_of_le v.stack v.scrub)) search_side

/-- `vg_dsa_parameter_search`, with its cleanup, returns without secret
residue, whatever the implementations `v1` of SHA-1, `v256` of SHA-256 and
`v` of the Miller–Rabin round. -/
theorem parameterSearch_scrubbed (v1 : Proof.Sha1.X86.Variants.Backend)
    (v256 : Proof.Sha256.X86.Variants.Backend) (v : RoundImpl) :
    VerifiedScrubbed target
      (Impl.Dsa.X86.Fn.parameterSearch (geo1 v1 v) (geo256 256 v256 v) (geo256 384 v256 v))
      Proof.Dsa.X86.Generation.genContract 32 :=
  verifiedScrubbedAll (api := Spec.Dsa.parameterSearchApi)
    { code := Impl.Dsa.X86.Generation.code (geo1 v1 v) (geo256 256 v256 v) (geo256 384 v256 v)
      verified := Proof.Dsa.X86.Generation.verified v1 v256 v
      spSafe := Proof.Dsa.X86.Generation.code_all v1 v256 v }
    (parameterSearchOut (ScrubAbi.consts Impl.RsaKeyGen.TrialTable32.consts) 216) (hs := search_scrub v1 v256 v)

/-- `vg_dsa_parameter_search`, with its cleanup, writes `esp` only by its frames. -/
theorem parameterSearch_spSafe (v1 : Proof.Sha1.X86.Variants.Backend)
    (v256 : Proof.Sha256.X86.Variants.Backend) (v : RoundImpl) :
    (Impl.Dsa.X86.Fn.parameterSearch (geo1 v1 v) (geo256 256 v256 v) (geo256 384 v256 v)).all
      (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.Dsa.X86.Generation.code_all v1 v256 v)

end VG.Proof.Dsa.X86.Scrub
