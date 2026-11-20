module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Spec.Ffdh.SievedContract
public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.Ffdh.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Verified
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Safety
public import VerifiedGarbage.Proof.Ffdh.X86.CheckPublicVerified
public import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivateVerified
public import VerifiedGarbage.Proof.Ffdh.X86.ExchangeVerified
public import VerifiedGarbage.Proof.Ffdh.X86.DeriveVerified
public import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
public import VerifiedGarbage.Proof.Ffdh.X86.ParamInit
public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Verified
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.PreVerified
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Search.Verified
public import VerifiedGarbage.Proof.Ffdh.X86.Shape
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.Ffdh.X86.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Verified
meta import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Safety
meta import VerifiedGarbage.Proof.Ffdh.X86.CheckPublicVerified
meta import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivateVerified
meta import VerifiedGarbage.Proof.Ffdh.X86.ExchangeVerified
meta import VerifiedGarbage.Proof.Ffdh.X86.DeriveVerified
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
meta import VerifiedGarbage.Proof.Ffdh.X86.ParamInit
meta import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Verified
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.PreVerified
meta import VerifiedGarbage.Proof.Ffdh.X86.Cached.Search.Verified
meta import VerifiedGarbage.Proof.Ffdh.X86.Shape

/-!
# FFDH on x86 (32-bit), without secret residue

The postconditions of the domain, key and exchange functions read the memory
on return only within their outputs (`X86.Scrub.PostOut`): the checks not at
all, `vg_ffdh_exchange` and `vg_ffdh_derive_public` the octets at `out` and
`y` (`bytesAt_of`, `written_of`), the precomputation the words at `ctx`
(`wordsAt_of`), the searches their outputs and states. The functions with
frames and calls, as emitted (`Impl.Ffdh.X86.Fn`), zero the stack their
contracts reserve and clear the registers (`X86.Scrub.verifiedScrubbedF`);
the two `init` functions, which call nothing and have no frame, clear the
registers (`X86.Scrub.verifiedScrubbed`).
What the scrub needs of each function's code is one Boolean, which the kernel
evaluates once, on the code's literal (`lit_decide`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Scrub

open VG.X86 VG.X86.Scrub

/-- The byte `k` of a region of more than `k` bytes at `o`. -/
theorem contains_of {o : Addr} {k N : Nat} (hk : k < N) : Region.Contains ⟨o, N⟩ (o + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [BitVec.add_comm o, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
  have := Nat.mod_le k (2 ^ 64)
  omega_using [hk]

/-- The `n` octets at `o` read the memory only within `⟨o, N * 1⟩`, `n ≤ N`. -/
theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n N : Nat}
    (h : ∀ a, Region.Contains ⟨o, N * 1⟩ a 1 → m₁ a = m₂ a) (hn : n ≤ N) :
    Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (contains_of (by omega_using [this, hn]))).symm

/-- An argument word, as the function reads it (its low 32 bits), is at most
the word. -/
theorem toNat_sw_le (cs : List (String × List (BitVec 64))) (x : BitVec 64) :
    (x.setWidth (abi.withConsts cs).ptrBits).toNat ≤ x.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_le _ _

theorem written_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} {r : BitVec 32} {v : Option (List Byte)}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (h : Spec.Rsa.written m₁ o n r v) :
    Spec.Rsa.written m₂ o n r v := by
  cases v <;> simpa only [Spec.Rsa.written, e] using h

/-- The `n` words at `o` read the memory only within `⟨o, N⟩`, `n * 8 ≤ N`. -/
theorem wordsAt_of {m₁ m₂ : Mem} {o : Addr} {n N : Nat}
    (h : ∀ a, Region.Contains ⟨o, N⟩ a 1 → m₁ a = m₂ a) (hN : n * 8 ≤ N := by omega) :
    Spec.Rsa.wordsAt m₂ o n = Spec.Rsa.wordsAt m₁ o n :=
  List.map_congr_left fun i hi => Mem.readW_congr fun t ht => by
    have := List.mem_range.mp hi
    rw [Offset.add_add]
    exact (h _ (contains_of (by simp only [Nat.reduceDiv] at ht; omega_using [hN, ht, this]))).symm

/-! ### The postconditions read only the buffers -/

theorem checkDomainOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.checkDomainContract (abi.withConsts cs) stack) (Spec.Ffdh.checkDomainSig.retBits 32) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun
    | [_, _, _, _, _], _, _, _, _, _, _, h => h

theorem checkPublicOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.checkPublicContract (abi.withConsts cs) stack) (Spec.Ffdh.checkPublicSig.retBits 32) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun
    | [_, _, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem checkPrivateOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.checkPrivateContract (abi.withConsts cs) stack) (Spec.Ffdh.checkPrivateSig.retBits 32) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun
    | [_, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem exchangeOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.exchangeContract (abi.withConsts cs) stack) (Spec.Ffdh.exchangeSig.retBits 32) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun
    | [out, outLen, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Ffdh.exchangeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      exact fun hd hp => written_of (bytesAt_of hb.1 (toNat_sw_le cs outLen)) (h hd hp)

theorem derivePublicOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.derivePublicContract (abi.withConsts cs) stack) (Spec.Ffdh.derivePublicSig.retBits 32) :=
  postOut_of_local_pre (leak := some _) (ScrubAbi.consts cs) fun
    | [y, yLen, _, _, pLen, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.Ffdh.derivePublicSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      rw [bytesAt_of hb.1 (hp.2.2.1 ▸ toNat_sw_le cs yLen)]
      exact h

theorem generationPrecomputeOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.generationPrecomputeContract (abi.withConsts cs) stack)
      (Spec.Ffdh.generationPrecomputeSig.retBits 32) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun
    | [ctx, ctxLen, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Ffdh.generationPrecomputeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have := toNat_sw_le cs ctxLen
      rw [wordsAt_of hb.1]
      exact h

theorem sievedParameterSearchOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.sievedParameterSearchContract (abi.withConsts cs) stack)
      (Spec.Ffdh.parameterSearchSig.retBits 32) :=
  postOut_of_local (leak := some _) (ScrubAbi.consts cs) fun
    | [out, outLen, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Ffdh.parameterSearchSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      rw [bytesAt_of hb.1 (toNat_sw_le cs outLen), wordsAt_of hb.2.1, wordsAt_of hb.2.2.2.2]
      exact h

theorem cachedKeySearchOut (stack : Nat) (cs : List (String × List (BitVec 64)) := []) :
    PostOut (Spec.Ffdh.cachedKeySearchContract (abi.withConsts cs) stack)
      (Spec.Ffdh.cachedKeySearchSig.retBits 32) :=
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
    rw [bytesAt_of hb.1 (hp.2.2.1 ▸ toNat_sw_le cs xLen), bytesAt_of hb.2.1 (hp.2.2.2.1 ▸ toNat_sw_le cs yLen),
      wordsAt_of hb.2.2.2.2.2.2.1, wordsAt_of hb.2.2.1]
    exact h

/-! ### The registrations -/

-- The code as literals, callees first, so that each function's literal
-- refers to its callees' (`lit_decide` evaluates each scrub's side condition
-- on them).
materialize_code ffdhMontMulAt := Impl.Mont.X86.Sse2.atBody
materialize_code ffdhCandidate := Impl.Ffdh.X86.Candidate.code
materialize_code ffdhCachedGenerate := Impl.Ffdh.X86.Cached.Generate.code
materialize_code ffdhCheckDomain := Impl.Ffdh.X86.VettedValidation.code
materialize_code ffdhCheckPublic := Impl.Ffdh.X86.CheckPublic.code
materialize_code ffdhCheckPrivate := Impl.Ffdh.X86.CheckPrivate.code
materialize_code ffdhExchange := Impl.Ffdh.X86.Exchange.code
materialize_code ffdhDerivePublic := Impl.Ffdh.X86.DerivePublic.code
materialize_code ffdhPrecompute := Impl.Ffdh.X86.Cached.Precompute.code
materialize_code ffdhCachedSearch := Impl.Ffdh.X86.Cached.Search.code
materialize_code ffdhParamSearch := Impl.Ffdh.X86.ParamSearch.code
materialize_code ffdhKeyInit := Impl.Ffdh.X86.KeyInit.code
materialize_code ffdhParamInit := Impl.Ffdh.X86.ParamInit.code

/-- `vg_ffdh_check_domain` as emitted. -/
theorem checkDomain_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.X86.Fn.checkDomain
      Proof.Ffdh.X86.VettedValidation.contract 32 :=
  verifiedScrubbedF (api := Spec.Ffdh.checkDomainApi)
    { code := Impl.Ffdh.X86.VettedValidation.code
      verified := Proof.Ffdh.X86.VettedValidation.verified
      spSafe := Proof.Ffdh.X86.VettedValidation.spSafe }
    (checkDomainOut 172 Impl.Ffdh.X86.VettedValidation.tableConsts)

/-- `vg_ffdh_check_public` as emitted. -/
theorem checkPublic_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.X86.Fn.checkPublic
      (Spec.Ffdh.checkPublicContract X86.abi Proof.Ffdh.X86.stack) 32 :=
  verifiedScrubbedF (api := Spec.Ffdh.checkPublicApi)
    { code := Impl.Ffdh.X86.CheckPublic.code
      verified := Proof.Ffdh.X86.CheckPublic.verified
      spSafe := Proof.Ffdh.X86.Shape.checkPublic_spSafe }
    (checkPublicOut _ [])

/-- `vg_ffdh_check_private` as emitted. -/
theorem checkPrivate_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.X86.Fn.checkPrivate
      (Spec.Ffdh.checkPrivateContract X86.abi Proof.Ffdh.X86.stack) 32 :=
  verifiedScrubbedF (api := Spec.Ffdh.checkPrivateApi)
    { code := Impl.Ffdh.X86.CheckPrivate.code
      verified := Proof.Ffdh.X86.CheckPrivate.verified
      spSafe := Proof.Ffdh.X86.Shape.checkPrivate_spSafe }
    (checkPrivateOut _ [])

/-- `vg_ffdh_exchange` as emitted. -/
theorem exchange_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.X86.Fn.exchange
      (Spec.Ffdh.exchangeContract X86.abi Proof.Ffdh.X86.stack) 32 :=
  verifiedScrubbedF (api := Spec.Ffdh.exchangeApi)
    { code := Impl.Ffdh.X86.Exchange.code
      verified := Proof.Ffdh.X86.Exchange.verified
      spSafe := Proof.Ffdh.X86.Shape.exchange_spSafe }
    (exchangeOut _ [])

/-- `vg_ffdh_derive_public` as emitted. -/
theorem derivePublic_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.X86.Fn.derivePublic
      (Spec.Ffdh.derivePublicContract X86.abi Proof.Ffdh.X86.stack) 32 :=
  verifiedScrubbedF (api := Spec.Ffdh.derivePublicApi)
    { code := Impl.Ffdh.X86.DerivePublic.code
      verified := Proof.Ffdh.X86.Derive.verified
      spSafe := Proof.Ffdh.X86.Shape.derivePublic_spSafe }
    (derivePublicOut _ [])

/-- `vg_ffdh_key_generation_init` as emitted. -/
theorem keyInit_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.X86.Fn.keyInit
      (Spec.Ffdh.keyInitContract X86.abi) 32 :=
  verifiedScrubbed (api := Spec.Ffdh.keyInitApi)
    { code := Impl.Ffdh.X86.KeyInit.code
      verified := Proof.Ffdh.X86.KeyInit.verified }

/-- `vg_ffdh_generate_key_precompute` as emitted. -/
theorem generationPrecompute_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.X86.Fn.generationPrecompute
      Proof.Ffdh.X86.Cached.Pre.pcContract 32 :=
  verifiedScrubbedF (api := Spec.Ffdh.generationPrecomputeApi)
    { code := Impl.Ffdh.X86.Cached.Precompute.code
      verified := Proof.Ffdh.X86.Cached.Pre.pc_verified
      spSafe := Proof.Ffdh.X86.Shape.cachedPrecompute_spSafe }
    (generationPrecomputeOut Proof.Ffdh.X86.stack Proof.Ffdh.X86.Cached.Pre.pcConsts)

/-- `vg_ffdh_generate_key_search_cached` as emitted. -/
theorem cachedKeySearch_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.X86.Fn.cachedKeySearch
      (Spec.Ffdh.cachedKeySearchContract X86.abi Proof.Ffdh.X86.Cached.Search.stack) 32 :=
  verifiedScrubbedF (api := Spec.Ffdh.cachedKeySearchApi)
    { code := Impl.Ffdh.X86.Cached.Search.code
      verified := Proof.Ffdh.X86.Cached.Search.verified
      spSafe := Proof.Ffdh.X86.Shape.cachedSearch_spSafe }
    (cachedKeySearchOut _ [])

/-- `vg_ffdh_parameter_generation_init` as emitted. -/
theorem parameterInit_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.X86.Fn.parameterInit
      (Spec.Ffdh.parameterInitContract X86.abi) 32 :=
  verifiedScrubbed (api := Spec.Ffdh.parameterInitApi)
    { code := Impl.Ffdh.X86.ParamInit.code
      verified := Proof.Ffdh.X86.ParamInit.verified }

/-- `vg_ffdh_generate_parameters` as emitted. -/
theorem sievedParameterSearch_scrubbed :
    VerifiedScrubbed target Impl.Ffdh.X86.Fn.sievedParameterSearch
      Proof.Ffdh.X86.PSearch.contract 32 :=
  verifiedScrubbedF (api := Spec.Ffdh.sievedParameterSearchApi)
    { code := Impl.Ffdh.X86.ParamSearch.code
      verified := Proof.Ffdh.X86.PSearch.verified
      spSafe := Proof.Ffdh.X86.Shape.paramSearch_spSafe }
    (sievedParameterSearchOut Proof.Ffdh.X86.PSearch.stack Impl.RsaKeyGen.TrialTable32.consts)

end VG.Proof.Ffdh.X86.Scrub
