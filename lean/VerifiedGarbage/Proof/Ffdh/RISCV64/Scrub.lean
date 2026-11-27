module

public import VerifiedGarbage.Impl.Ffdh.RISCV64.Fn
public import VerifiedGarbage.Proof.Ffdh.ParameterPublic
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubCall
public import VerifiedGarbage.Proof.Variants.MillerRabin.RISCV64
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.PcCT
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.SearchProof.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.CheckPrivate.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Domain.CheckPublic
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Generation.Init
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Generation.Search.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.KeyGeneration.Init
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Verified
public import VerifiedGarbage.Proof.Ffdh.RISCV64.VettedValidation.Verified
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Rsa.RISCV64.Scrub

/-!
# FFDH on RISC-V, without secret residue

The postconditions read the memory on return only within the outputs
(`RISCV64.Scrub.PostOut`): the checks not at all, the others the octets at
their outputs and the words at `ctx`, `used` and `state`.

Each function as emitted (`Impl.Ffdh.RISCV64.Fn`) meets its contract in
constant time and returns without secret residue (`VerifiedScrubbed`, by
`RISCV64.Scrub.verifiedScrubbedAll`). What the cleanups need of the code
(`Scrub.scrubSide`) is evaluated in one declaration (`sides`), so that the
kernel walks what the functions share once. The parameter search is generic
over the Miller–Rabin round (`Proof.Variants.MillerRabin.RISCV64`): its side
condition is evaluated with a stub of 96 bytes of stack in the round's place,
and the code with a round is that code filled (`Scrub.Fill`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub
open VG.Proof.Rsa.RISCV64.Scrub (bytesAt_of wordsAt_of toNat_sw)
open VG.Proof.MillerRabin.RISCV64 (RoundImpl)

/-! ## Postconditions -/

theorem written_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} {r : BitVec 32} {v : Option (List Byte)}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (h : Spec.Rsa.written m₁ o n r v) :
    Spec.Rsa.written m₂ o n r v := by
  cases v <;> simpa only [Spec.Rsa.written, e] using h

theorem parameterInitOut :
    PostOut (Proof.Ffdh.parameterInitAskedContract abi) (Spec.Ffdh.parameterInitSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun
    | [_, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Ffdh.parameterInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [wordsAt_of hb]
      exact h

theorem keyInitOut :
    PostOut (Spec.Ffdh.keyInitContract abi) (Spec.Ffdh.keyInitSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun
    | [_, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Ffdh.keyInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [wordsAt_of hb]
      exact h

theorem checkDomainOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.checkDomainContract (abi.withConsts cs) stack) (Spec.Ffdh.checkDomainSig.retBits 64) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun
    | [_, _, _, _, _], _, _, _, _, _, _, h => h

theorem checkPublicOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.checkPublicContract (abi.withConsts cs) stack) (Spec.Ffdh.checkPublicSig.retBits 64) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun
    | [_, _, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem checkPrivateOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.checkPrivateContract (abi.withConsts cs) stack) (Spec.Ffdh.checkPrivateSig.retBits 64) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun
    | [_, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem exchangeOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.exchangeContract (abi.withConsts cs) stack) (Spec.Ffdh.exchangeSig.retBits 64) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun
    | [out, outLen, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Ffdh.exchangeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      have e := bytesAt_of hb.1
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      exact fun hd hp => written_of (by rw [toNat_sw (ScrubAbi.consts cs)]; exact e) (h hd hp)

theorem derivePublicOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.derivePublicContract (abi.withConsts cs) stack) (Spec.Ffdh.derivePublicSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) (ScrubAbi.consts cs) fun
    | [y, yLen, _, _, pLen, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.Ffdh.derivePublicSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = yLen.toNat → Spec.Rsa.bytesAt m₂ y X = Spec.Rsa.bytesAt m₁ y X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ (by rw [← hp.2.2.1]; exact toNat_sw (ScrubAbi.consts cs) yLen)]
      exact h

theorem generationPrecomputeOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.generationPrecomputeContract (abi.withConsts cs) stack)
      (Spec.Ffdh.generationPrecomputeSig.retBits 64) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun
    | [ctx, ctxLen, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Ffdh.generationPrecomputeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = ctxLen.toNat → Spec.Rsa.wordsAt m₂ ctx X = Spec.Rsa.wordsAt m₁ ctx X :=
        fun X hX => hX ▸ wordsAt_of hb.1
      rw [e _ (toNat_sw (ScrubAbi.consts cs) ctxLen)]
      exact h

theorem sievedParameterSearchOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Proof.Ffdh.sievedParameterSearchAskedContract (abi.withConsts cs) stack)
      (Spec.Ffdh.parameterSearchSig.retBits 64) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun
    | [out, outLen, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Ffdh.parameterSearchSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ ?hX, wordsAt_of hb.2.1, wordsAt_of hb.2.2.2.2]
      · exact h
      · exact toNat_sw (ScrubAbi.consts cs) outLen

theorem cachedKeySearchOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.cachedKeySearchContract (abi.withConsts cs) stack)
      (Spec.Ffdh.cachedKeySearchSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) (ScrubAbi.consts cs) fun vs m m₁ m₂ r hlen hp hb h => by
    obtain ⟨x, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 14) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨xLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨y, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨yLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨used, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    iterate 7
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      replace hlen := Nat.succ.inj hlen
    obtain ⟨state, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    iterate 2
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simp only [Spec.Ffdh.cachedKeySearchSig, Spec.Ffdh.keySearchSig, List.cons_append, List.nil_append,
      Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size] at hb
    change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
    change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
    change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
    dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
    have ex : ∀ X, X = xLen.toNat → Spec.Rsa.bytesAt m₂ x X = Spec.Rsa.bytesAt m₁ x X :=
      fun X hX => hX ▸ bytesAt_of hb.1
    have ey : ∀ X, X = yLen.toNat → Spec.Rsa.bytesAt m₂ y X = Spec.Rsa.bytesAt m₁ y X :=
      fun X hX => hX ▸ bytesAt_of hb.2.1
    rw [ex _ (by rw [← hp.2.2.1]; exact toNat_sw (ScrubAbi.consts cs) xLen), ey _ (by rw [← hp.2.2.2.1]; exact toNat_sw (ScrubAbi.consts cs) yLen),
      wordsAt_of hb.2.2.2.2.2.2.1, wordsAt_of hb.2.2.1]
    exact h


/-! ## The functions as emitted -/

/-- What the cleanups need of the code: of the parameter search, with a stub of 96 bytes of stack in the
place of the round. -/
theorem sides :
    scrubSide Impl.Ffdh.RISCV64.Generation.init 0 32 [] = true ∧
    scrubSide Impl.Ffdh.RISCV64.KeyGeneration.init 0 32 [] = true ∧
    scrubSide Impl.Ffdh.RISCV64.Domain.checkPublic 0 32 [] = true ∧
    scrubSide Impl.Ffdh.RISCV64.VettedValidation.code 0 32 [] = true ∧
    scrubSide Impl.Ffdh.RISCV64.exchange 0 32 [] = true ∧
    scrubSide Impl.Ffdh.RISCV64.Derive.derivePublic 0 32 [] = true ∧
    scrubSide Impl.Ffdh.RISCV64.CheckPrivate.checkPrivate 0 32 [] = true ∧
    scrubSide Impl.Ffdh.RISCV64.Cached.Precompute.code 0 32 [] = true ∧
    scrubSide Impl.Ffdh.RISCV64.Fn.cachedKeySearchBody 64 32 [] = true ∧
    scrubSide (Impl.Ffdh.RISCV64.Fn.sievedParameterSearchBody "" (holeStub 96)) 128 32 [] = true := by
  lit_decide

theorem parameterInit_asked :
    VerifiedScrubbed target Impl.Ffdh.RISCV64.Fn.parameterInit
      (Proof.Ffdh.parameterInitAskedContract abi) 32 :=
  verifiedScrubbedAll (api := Proof.Ffdh.parameterInitAskedApi) (W := 0)
    { code := Impl.Ffdh.RISCV64.Generation.init
      verified := Proof.Ffdh.RISCV64.Generation.init_verified }
    parameterInitOut (by exact sides.1)

theorem parameterInit_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.RISCV64.Fn.parameterInit (Spec.Ffdh.parameterInitContract abi) 32 :=
  Proof.Ffdh.parameterInit_imp parameterInit_asked id

theorem parameterInit_public :
    Spec.Ffdh.parameterInitOut.Of abi Impl.Ffdh.RISCV64.Fn.parameterInit (Spec.Ffdh.parameterInitContract abi) :=
  Proof.Ffdh.parameterInit_public parameterInit_asked

theorem keyInit_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.RISCV64.Fn.keyInit
      (Spec.Ffdh.keyInitContract abi) 32 :=
  verifiedScrubbedAll (api := Spec.Ffdh.keyInitApi) (W := 0)
    { code := Impl.Ffdh.RISCV64.KeyGeneration.init
      verified := Proof.Ffdh.RISCV64.KeyGeneration.init_verified }
    keyInitOut (by exact sides.2.1)

theorem checkPublic_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.RISCV64.Fn.checkPublic
      (Spec.Ffdh.checkPublicContract abi) 32 :=
  verifiedScrubbedAll (api := Spec.Ffdh.checkPublicApi) (W := 0)
    { code := Impl.Ffdh.RISCV64.Domain.checkPublic
      verified := Proof.Ffdh.RISCV64.Domain.checkPublic_verified }
    (checkPublicOut _) (by exact sides.2.2.1)

theorem checkDomain_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.RISCV64.Fn.checkDomain
      (Spec.Ffdh.checkDomainContract (abi.withConsts Impl.Ffdh.RISCV64.VettedValidation.tableConsts)) 32 :=
  verifiedScrubbedAll (api := Spec.Ffdh.checkDomainApi) (W := 0)
    { code := Impl.Ffdh.RISCV64.VettedValidation.code
      verified := Proof.Ffdh.RISCV64.VettedValidation.verified
      consts := Impl.Ffdh.RISCV64.VettedValidation.tableConsts }
    (checkDomainOut 0 Impl.Ffdh.RISCV64.VettedValidation.tableConsts) (by exact sides.2.2.2.1)

theorem exchange_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.RISCV64.Fn.exchange
      (Spec.Ffdh.exchangeContract abi) 32 :=
  verifiedScrubbedAll (api := Spec.Ffdh.exchangeApi) (W := 0)
    { code := Impl.Ffdh.RISCV64.exchange
      verified := Proof.Ffdh.RISCV64.exchange_verified }
    (exchangeOut _) (by exact sides.2.2.2.2.1)

theorem derivePublic_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.RISCV64.Fn.derivePublic
      (Spec.Ffdh.derivePublicContract abi) 32 :=
  verifiedScrubbedAll (api := Spec.Ffdh.derivePublicApi) (W := 0)
    { code := Impl.Ffdh.RISCV64.Derive.derivePublic
      verified := Proof.Ffdh.RISCV64.Derive.derivePublic_verified }
    (derivePublicOut _) (by exact sides.2.2.2.2.2.1)

theorem checkPrivate_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.RISCV64.Fn.checkPrivate
      (Spec.Ffdh.checkPrivateContract abi) 32 :=
  verifiedScrubbedAll (api := Spec.Ffdh.checkPrivateApi) (W := 0)
    { code := Impl.Ffdh.RISCV64.CheckPrivate.checkPrivate
      verified := Proof.Ffdh.RISCV64.CheckPrivate.checkPrivate_verified }
    (checkPrivateOut _) (by exact sides.2.2.2.2.2.2.1)

theorem precompute_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.RISCV64.Fn.precompute
      (Spec.Ffdh.generationPrecomputeContract (abi.withConsts Impl.Ffdh.RISCV64.VettedValidation.tableConsts)) 32 :=
  verifiedScrubbedAll (api := Spec.Ffdh.generationPrecomputeApi) (W := 0)
    { code := Impl.Ffdh.RISCV64.Cached.Precompute.code
      verified := Proof.Ffdh.RISCV64.Cached.pc_verified
      consts := Impl.Ffdh.RISCV64.VettedValidation.tableConsts }
    (generationPrecomputeOut 0 Impl.Ffdh.RISCV64.VettedValidation.tableConsts) (by exact sides.2.2.2.2.2.2.2.1)

theorem cachedKeySearch_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.RISCV64.Fn.cachedKeySearch
      (Spec.Ffdh.cachedKeySearchContract abi 64) 32 :=
  verifiedScrubbedAll (api := Spec.Ffdh.cachedKeySearchApi) (W := 64)
    { code := Impl.Ffdh.RISCV64.Fn.cachedKeySearchBody
      verified := Proof.Ffdh.RISCV64.Cached.SearchProof.search_verified }
    (cachedKeySearchOut _) (by exact sides.2.2.2.2.2.2.2.2.1)

/-- The parameter search with the round `round` is its code with the stub,
filled. -/
theorem sievedParameterSearch_fill {round : Prog isa} (suffix : String) (h : calleeSide round 96 = true) :
    Fill 0 [] (Impl.Ffdh.RISCV64.Fn.sievedParameterSearchBody "" (holeStub 96))
      (Impl.Ffdh.RISCV64.Fn.sievedParameterSearchBody suffix round) := by
  fill_calls

theorem sievedParameterSearch_asked (v : RoundImpl) :
    VerifiedScrubbed target (Impl.Ffdh.RISCV64.Fn.sievedParameterSearch v.suffix v.code)
      (Proof.Ffdh.sievedParameterSearchAskedContract (abi.withConsts Generation.tables) 128) 32 :=
  verifiedScrubbedAll (api := Proof.Ffdh.sievedParameterSearchAskedApi)
    { suffix := v.suffix
      code := Impl.Ffdh.RISCV64.Fn.sievedParameterSearchBody v.suffix v.code
      verified := Proof.Ffdh.RISCV64.Generation.search_verified v }
    (sievedParameterSearchOut 128 Generation.tables)
    (scrubSide_of_fill
      (sievedParameterSearch_fill v.suffix (calleeSide_of (depth_le_of_sdepth v.stack) v.icalls))
      sides.2.2.2.2.2.2.2.2.2 (fun _ h => h) (fun _ h => absurd h List.not_mem_nil))

theorem sievedParameterSearch_scrubbed (v : RoundImpl) :
    VerifiedScrubbed target (Impl.Ffdh.RISCV64.Fn.sievedParameterSearch v.suffix v.code)
      (Spec.Ffdh.sievedParameterSearchContract (abi.withConsts Generation.tables) 128) 32 :=
  Proof.Ffdh.sievedParameterSearch_imp (sievedParameterSearch_asked v) id

theorem sievedParameterSearch_public (v : RoundImpl) :
    Spec.Ffdh.sievedParameterSearchOut.Of abi (Impl.Ffdh.RISCV64.Fn.sievedParameterSearch v.suffix v.code)
      (Spec.Ffdh.sievedParameterSearchContract (abi.withConsts Generation.tables) 128) :=
  Proof.Ffdh.sievedParameterSearch_public (sievedParameterSearch_asked v)

end VG.Proof.Ffdh.RISCV64.Scrub
