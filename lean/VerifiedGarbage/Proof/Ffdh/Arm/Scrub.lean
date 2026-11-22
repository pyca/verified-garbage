module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Framework.Arm.ScrubFill
public import VerifiedGarbage.Proof.Ffdh.Arm.Backend
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyInitVerified
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterInitVerified
public import VerifiedGarbage.Impl.Ffdh.Arm.Fn
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPublicInstances
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedCheckPrivateInstances
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveInstances
public import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeInstances
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeVerified
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedKeyInstances
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Verified
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Verified
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Omega

/-!
# FFDH's functions on ARMv7, without secret residue

Each function as emitted (`Impl.Ffdh.Arm.Fn`) returns with the registers a
callee may change set to constants, and the stack its contract reserves
zeroed if it has frames; `Fn` below has the theorem of each, which its
registration binds.

The initializations have no frames (`Arm.Scrub.verifiedScrubbed`). What the
cleanup of the others needs of their code (`Arm.Scrub.scrubSideF`) is
`CodeOk` of it, and their postconditions read the memory on return only
within their buffers (`Arm.Scrub.PostOut`; `postOut_of_local_pre` where the
length a postcondition reads is one the precondition equates with the
buffer's).

An FFDH `Backend` states `CodeOk` of its own code (`Backend.checkDomain_ok`,
by `lit_decide` where it is defined). The functions generic over the RSA
Montgomery product (`MontBackend`) prove it once for any implementation:
their code with a stub in place of the product (`holeStub 40`) is evaluated
once (`lit_decide`), `fill_holes` proves that the code with any
implementation fills its holes (`FillB`), from the `CodeOk` the
implementation states of its own code (`MontBackend.mulOk`), and the
implementation's rewriting of its callers keeps it (`MontBackend.callerOk`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.ScrubFill VG.Arm.FrameStack

theorem checkDomainOut :
    PostOut (Spec.Ffdh.checkDomainContract (abi.withConsts Impl.Ffdh.Arm.VettedGroups.tableConsts) 128)
      (Spec.Ffdh.checkDomainSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen _ h => by
    iterate 5
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    exact h

theorem checkPrivateOut :
    PostOut (Spec.Ffdh.checkPrivateContract abi 176) (Spec.Ffdh.checkPrivateSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    iterate 9
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    exact h

/-! ## What the postconditions read -/
/-- `postOut_of_local`, for a postcondition that reads the memory on return
only within the buffers given the precondition (a buffer's length that the
precondition equates with another argument). -/
theorem postOut_of_local_pre {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words A.ptrBits).length →
      Curry.apply (sig.words A.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -, -, -, hpre⟩ := hs
    have hpre' : Curry.apply (sig.words A.ptrBits) pre (vals s) (A.mem s) := by
      cases hal : A.alignsBufs
      · simpa only [hal, Bool.cond_false] using hpre
      · simp only [hal, Bool.cond_true] at hpre; exact hpre.1
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hA.mem] at hpre'
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) hpre'
      (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply hA.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← hA.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

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

/-- A 64-bit argument word's value at a narrower width is at most the word's. -/
theorem toNat_sw_le {w : Nat} (x : BitVec 64) : (x.setWidth w).toNat ≤ x.toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_le _ _

/-- The `n` words at `o` read the memory only within `⟨o, N⟩`, `n * 8 ≤ N`. -/
theorem wordsAt_of {m₁ m₂ : Mem} {o : Addr} {n N : Nat}
    (h : ∀ a, Region.Contains ⟨o, N⟩ a 1 → m₁ a = m₂ a) (hN : n * 8 ≤ N := by omega) :
    Spec.Rsa.wordsAt m₂ o n = Spec.Rsa.wordsAt m₁ o n :=
  List.map_congr_left fun i hi => Mem.readW_congr fun t ht => by
    have := List.mem_range.mp hi
    rw [Offset.add_add]
    exact (h _ (contains_of (by simp only [Nat.reduceDiv] at ht; omega_using [hN, ht, this]))).symm

theorem written_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} {r : BitVec 32} {v : Option (List Byte)}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (h : Spec.Rsa.written m₁ o n r v) :
    Spec.Rsa.written m₂ o n r v := by
  cases v <;> simpa only [Spec.Rsa.written, e] using h

theorem checkPublicOut :
    PostOut (Spec.Ffdh.checkPublicContract abi 176) (Spec.Ffdh.checkPublicSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    iterate 7
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    exact h

theorem exchangeOut :
    PostOut (Spec.Ffdh.exchangeContract abi 176) (Spec.Ffdh.exchangeSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 10) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨outLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    iterate 9
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simp only [Spec.Ffdh.exchangeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size] at hb
    have e := bytesAt_of hb.1 (toNat_sw_le (w := abi.ptrBits) outLen)
    change @Curry.apply (Mem → Mem → BitVec (Spec.Ffdh.exchangeSig.retBits 32) → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
    change @Curry.apply (Mem → Mem → BitVec (Spec.Ffdh.exchangeSig.retBits 32) → Prop) [_, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
    dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
    exact fun hd hp => written_of e (h hd hp)

theorem derivePublicOut :
    PostOut (Spec.Ffdh.derivePublicContract abi 176) (Spec.Ffdh.derivePublicSig.retBits 32) :=
  postOut_of_local_pre ScrubAbi.plain fun vs m m₁ m₂ r hlen hp hb h => by
    obtain ⟨y, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 8) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨yLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    iterate 2
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      replace hlen := Nat.succ.inj hlen
    obtain ⟨pLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    iterate 4
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simp only [Spec.Ffdh.derivePublicSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size] at hb
    change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _] _ _ m at hp
    change @Curry.apply (Mem → Mem → BitVec (Spec.Ffdh.derivePublicSig.retBits 32) → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
    change @Curry.apply (Mem → Mem → BitVec (Spec.Ffdh.derivePublicSig.retBits 32) → Prop) [_, _, _, _, _, _, _, _, _] _ _ _ m₂ r
    dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
    rw [bytesAt_of hb.1 (by rw [← hp.2.2.1]; exact toNat_sw_le yLen)]
    exact h

theorem generationPrecomputeOut :
    PostOut (Spec.Ffdh.generationPrecomputeContract (abi.withConsts Impl.Ffdh.Arm.VettedGroups.tableConsts) 176)
      (Spec.Ffdh.generationPrecomputeSig.retBits 32) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 6) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨ctxLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    iterate 5
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simp only [Spec.Ffdh.generationPrecomputeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size] at hb
    change @Curry.apply (Mem → Mem → BitVec (Spec.Ffdh.generationPrecomputeSig.retBits 32) → Prop) [_, _, _, _, _, _, _] _ _ _ m₁ r at h
    change @Curry.apply (Mem → Mem → BitVec (Spec.Ffdh.generationPrecomputeSig.retBits 32) → Prop) [_, _, _, _, _, _, _] _ _ _ m₂ r
    dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
    rw [wordsAt_of (n := (BitVec.setWidth _ ctxLen).toNat) hb.1 (Nat.mul_le_mul_right 8 (toNat_sw_le ctxLen))]
    exact h

theorem cachedKeySearchOut :
    PostOut (Spec.Ffdh.cachedKeySearchContract abi 240) (Spec.Ffdh.cachedKeySearchSig.retBits 32) :=
  postOut_of_local_pre ScrubAbi.plain fun vs m m₁ m₂ r hlen hp hb h => by
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
    change @Curry.apply (Mem → Mem → BitVec (Spec.Ffdh.cachedKeySearchSig.retBits 32) → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
    change @Curry.apply (Mem → Mem → BitVec (Spec.Ffdh.cachedKeySearchSig.retBits 32) → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
    dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
    rw [bytesAt_of hb.1 (by rw [← hp.2.2.1]; exact toNat_sw_le xLen),
      bytesAt_of hb.2.1 (by rw [← hp.2.2.2.1]; exact toNat_sw_le yLen),
      wordsAt_of hb.2.2.2.2.2.2.1, wordsAt_of hb.2.2.1]
    exact h

theorem sievedParameterSearchOut :
    PostOut (Spec.Ffdh.sievedParameterSearchContract abi 232) (Spec.Ffdh.parameterSearchSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 9) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨outLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    iterate 8
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simp only [Spec.Ffdh.parameterSearchSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size] at hb
    change @Curry.apply (Mem → Mem → BitVec (Spec.Ffdh.parameterSearchSig.retBits 32) → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
    change @Curry.apply (Mem → Mem → BitVec (Spec.Ffdh.parameterSearchSig.retBits 32) → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
    dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
    rw [bytesAt_of hb.1 (toNat_sw_le (w := abi.ptrBits) outLen), wordsAt_of hb.2.1, wordsAt_of hb.2.2.2.2]
    exact h

/-! ## `CodeOk` of the functions generic over the Montgomery product -/

open VG.Arm.FrameStack VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

theorem checkPublicStub : CodeOk (Impl.Ffdh.Arm.SharedCheckPublic.code (MontCall.op "" (holeStub 40))) 176 := by
  lit_decide

theorem checkPublicOk (b : MontBackend) : CodeOk (SharedCheckPublic.calledCode b) 176 :=
  b.callerOk _ _ ((show FillB _ (SharedCheckPublic.code b) by have := b.mulOk; fill_holes).codeOk checkPublicStub)

theorem checkPrivateStub :
    CodeOk (Impl.Ffdh.Arm.SharedCheckPrivate.code (MontCall.op "" (holeStub 40))) 176 := by
  lit_decide

theorem checkPrivateOk (b : MontBackend) : CodeOk (SharedCheckPrivate.calledCode b) 176 :=
  b.callerOk _ _ ((show FillB _ (SharedCheckPrivate.code b) by have := b.mulOk; fill_holes).codeOk checkPrivateStub)

theorem deriveStub : CodeOk (Impl.Ffdh.Arm.SharedDerive.code (MontCall.op "" (holeStub 40))) 176 := by
  lit_decide

theorem deriveOk (b : MontBackend) : CodeOk (SharedDerive.calledCode b) 176 :=
  b.callerOk _ _ ((show FillB _ (SharedDerive.code b) by have := b.mulOk; fill_holes).codeOk deriveStub)

theorem exchangeStub : CodeOk (Impl.Ffdh.Arm.SharedExchange.code (MontCall.op "" (holeStub 40))) 176 := by
  lit_decide

theorem exchangeOk (b : MontBackend) : CodeOk (SharedExchange.calledCode b) 176 :=
  b.callerOk _ _ ((show FillB _ (SharedExchange.code b) by have := b.mulOk; fill_holes).codeOk exchangeStub)

theorem precomputeStub :
    CodeOk (Impl.Ffdh.Arm.CombPrecompute.code (MontCall.op "" (holeStub 40)) VettedBound.code) 176 := by
  lit_decide

theorem precomputeOk (b : MontBackend) : CodeOk (combPrecomputeCalledCode b) 176 :=
  b.callerOk _ _ ((show FillB _ (Impl.Ffdh.Arm.CombPrecompute.code (MontCall.op b.name b.mul) VettedBound.code)
    by have := b.mulOk; fill_holes).codeOk precomputeStub)

theorem cachedAttemptStub : CodeOk (Impl.Ffdh.Arm.CachedKeyGenerate.code CachedKeyGenerate.prepare
    CachedKeyGenerate.sample
    (Impl.Ffdh.Arm.KeyGenerate.tail (Impl.Ffdh.Arm.CachedPower.code (MontCall.op "" (holeStub 40))))) 176 := by
  lit_decide

/-- The cached key-generation attempt, which `vg_ffdh_generate_key_search_cached` calls. -/
theorem cachedAttemptOk (b : MontBackend) : CodeOk (CachedKeyGenerate.native b) 176 :=
  b.callerOk _ _ ((show FillB _ (CachedKeyGenerate.code b) by have := b.mulOk; fill_holes).codeOk cachedAttemptStub)

theorem cachedSearchStub :
    CodeOk (Impl.Ffdh.Arm.KeySearch.codeFor GenerationPolicy.cached.cachedContext (.call "" (holeStub 176))) 240 := by
  lit_decide

theorem cachedSearchOk (b : MontBackend) : CodeOk (KeySearch.calledCode (CachedKeyGenerate.backend b)) 240 :=
  (show FillB _ (KeySearch.calledCode (CachedKeyGenerate.backend b)) by
    have : CodeOk (CachedKeyGenerate.backend b).generateKey 176 := cachedAttemptOk b
    fill_holes).codeOk cachedSearchStub

/-! ## `CodeOk` of the parameter search, generic over the Miller–Rabin round -/

open VG.Proof.MillerRabin.Arm in
/-- What the cleanup needs of a round: its `stack` and `icallFree`, which
each implementation states of its own code. -/
theorem roundOk (v : RoundImpl) : CodeOk v.code 56 := ⟨v.stack, v.icallFree⟩

theorem rowU_noIcall : noIcall Impl.Bignum.Arm.rowU = true := by lit_decide

theorem downRowU_noIcall : noIcall Impl.Bignum.Arm.DownRow.codeU = true := by lit_decide

/-- The UMAAL rows the candidate's own Montgomery conversions take
(`callerRows`) keep what the cleanup needs of its code. -/
theorem callerRows_codeOk {c : Prog isa} {n : Nat} (h : CodeOk c n) :
    CodeOk (Impl.Ffdh.Arm.callerRows c) n := by
  refine ⟨Nat.le_trans (CallerRows.stack c) h.1, ?_⟩
  have h2 := h.2
  clear h
  induction c with
  | block _ =>
    simp only [Impl.Ffdh.Arm.callerRows]
    split
    · exact rowU_noIcall
    · split
      · exact downRowU_noIcall
      · exact h2
  | seq x y ihx ihy =>
    simp only [noIcall, Bool.and_eq_true] at h2
    simp only [Impl.Ffdh.Arm.callerRows]
    split
    · exact rowU_noIcall
    · split
      · exact downRowU_noIcall
      · simp only [noIcall, ihx h2.1, ihy h2.2, Bool.and_self]
  | ite _ t e iht ihe =>
    simp only [noIcall, Bool.and_eq_true] at h2
    simp only [Impl.Ffdh.Arm.callerRows]
    split
    · exact rowU_noIcall
    · split
      · exact downRowU_noIcall
      · simp only [noIcall, iht h2.1, ihe h2.2, Bool.and_self]
  | loop x _ ih =>
    simp only [noIcall] at h2
    simp only [Impl.Ffdh.Arm.callerRows]
    split
    · exact rowU_noIcall
    · split
      · exact downRowU_noIcall
      · simp only [noIcall, ih h2]
  | call _ _ _ => exact h2
  | icall => exact h2
  | frame _ x _ ih =>
    simp only [noIcall] at h2
    simp only [Impl.Ffdh.Arm.callerRows]
    split
    · exact rowU_noIcall
    · split
      · exact downRowU_noIcall
      · simp only [noIcall, ih h2]

theorem candidateStub : CodeOk (Impl.Ffdh.Arm.ParameterCandidate.code "" (holeStub 56)) 184 := by
  lit_decide

open VG.Proof.MillerRabin.Arm in
/-- The sieved candidate, which `vg_ffdh_generate_parameters` calls, with the round `v`. -/
theorem candidateOk (v : RoundImpl) : CodeOk (parameterBackend v).candidate 184 := by
  have hc : CodeOk (Impl.Ffdh.Arm.ParameterCandidate.code v.name v.code) 184 :=
    (show FillB _ (Impl.Ffdh.Arm.ParameterCandidate.code v.name v.code) by
      have := roundOk v; fill_holes).codeOk candidateStub
  change CodeOk (Impl.Ffdh.Arm.ParameterCandidate.optimizedCode _ v.name v.code) 184
  unfold Impl.Ffdh.Arm.ParameterCandidate.optimizedCode
  split
  · exact callerRows_codeOk hc
  · exact hc

theorem parameterSearchStub : CodeOk (Impl.Ffdh.Arm.ParameterSearch.code (.call "" (holeStub 184))) 232 := by
  lit_decide

open VG.Proof.MillerRabin.Arm in
theorem parameterSearchOk (v : RoundImpl) :
    CodeOk (Impl.Ffdh.Arm.ParameterSearch.code
      (.call (parameterBackend v).candidateName (parameterBackend v).candidate)) 232 :=
  (show FillB _ (Impl.Ffdh.Arm.ParameterSearch.code
      (.call (parameterBackend v).candidateName (parameterBackend v).candidate)) by
    have := candidateOk v; fill_holes).codeOk parameterSearchStub

theorem frameOk_128 : FrameOk 128 := by decide

theorem frameOk_176 : FrameOk 176 := by decide

theorem frameOk_240 : FrameOk 240 := by decide

theorem frameOk_232 : FrameOk 232 := by decide

end VG.Proof.Ffdh.Arm.Scrub

namespace VG.Proof.Ffdh.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ffdh_key_generation_init`. -/
theorem keyInit : VerifiedScrubbed target Impl.Ffdh.Arm.Fn.keyInit (Spec.Ffdh.keyInitContract abi) 32 :=
  verifiedScrubbed (api := Spec.Ffdh.keyInitApi)
    { code := Impl.Ffdh.Arm.KeyGeneration.init, verified := Proof.Ffdh.Arm.keyInit_verified } rfl

/-- `vg_ffdh_parameter_generation_init`. -/
theorem parameterInit :
    VerifiedScrubbed target Impl.Ffdh.Arm.Fn.parameterInit (Spec.Ffdh.parameterInitContract abi) 32 :=
  verifiedScrubbed (api := Spec.Ffdh.parameterInitApi)
    { code := Impl.Ffdh.Arm.Generation.init, verified := Proof.Ffdh.Arm.parameterInit_verified } rfl

/-- `vg_ffdh_check_domain`, with the implementation `v`. -/
theorem checkDomain (v : Backend) :
    VerifiedScrubbed target (Impl.Ffdh.Arm.Fn.checkDomain v.checkDomain)
      (Spec.Ffdh.checkDomainContract (abi.withConsts Impl.Ffdh.Arm.VettedGroups.tableConsts) 128) 32 :=
  verifiedScrubbedAll (api := Spec.Ffdh.checkDomainApi)
    { code := v.checkDomain, verified := v.checkDomain_verified }
    Scrub.checkDomainOut (scrubSideF_of v.checkDomain_ok Scrub.frameOk_128 _)

open VG.Proof.Bignum.Arm in
/-- `vg_ffdh_check_private`, with the Montgomery product `b`. -/
theorem checkPrivate (b : MontBackend) :
    VerifiedScrubbed target (Impl.Ffdh.Arm.Fn.checkPrivate (SharedCheckPrivate.calledCode b))
      (Spec.Ffdh.checkPrivateContract abi 176) 32 :=
  verifiedScrubbedAll (api := Spec.Ffdh.checkPrivateApi)
    { code := SharedCheckPrivate.calledCode b, verified := SharedCheckPrivate.called_verified b }
    Scrub.checkPrivateOut (scrubSideF_of (Scrub.checkPrivateOk b) Scrub.frameOk_176 _)

open VG.Proof.Bignum.Arm in
/-- `vg_ffdh_check_public`, with the Montgomery product `b`. -/
theorem checkPublic (b : MontBackend) :
    VerifiedScrubbed target (Impl.Ffdh.Arm.Fn.checkPublic (SharedCheckPublic.calledCode b))
      (Spec.Ffdh.checkPublicContract abi 176) 32 :=
  verifiedScrubbedAll (api := Spec.Ffdh.checkPublicApi)
    { code := SharedCheckPublic.calledCode b, verified := SharedCheckPublic.called_verified b }
    Scrub.checkPublicOut (scrubSideF_of (Scrub.checkPublicOk b) Scrub.frameOk_176 _)

open VG.Proof.Bignum.Arm in
/-- `vg_ffdh_derive_public`, with the Montgomery product `b`. -/
theorem derivePublic (b : MontBackend) :
    VerifiedScrubbed target (Impl.Ffdh.Arm.Fn.derivePublic (SharedDerive.calledCode b))
      (Spec.Ffdh.derivePublicContract abi 176) 32 :=
  verifiedScrubbedAll (api := Spec.Ffdh.derivePublicApi)
    { code := SharedDerive.calledCode b, verified := SharedDerive.called_verified b }
    Scrub.derivePublicOut (scrubSideF_of (Scrub.deriveOk b) Scrub.frameOk_176 _)

open VG.Proof.Bignum.Arm in
/-- `vg_ffdh_exchange`, with the Montgomery product `b`. -/
theorem exchange (b : MontBackend) :
    VerifiedScrubbed target (Impl.Ffdh.Arm.Fn.exchange (SharedExchange.calledCode b))
      (Spec.Ffdh.exchangeContract abi 176) 32 :=
  verifiedScrubbedAll (api := Spec.Ffdh.exchangeApi)
    { code := SharedExchange.calledCode b, verified := SharedExchange.called_verified b }
    Scrub.exchangeOut (scrubSideF_of (Scrub.exchangeOk b) Scrub.frameOk_176 _)

open VG.Proof.Bignum.Arm in
/-- `vg_ffdh_generate_key_precompute`, with the Montgomery product `b`. -/
theorem generationPrecompute (b : MontBackend) :
    VerifiedScrubbed target (Impl.Ffdh.Arm.Fn.generationPrecompute (combPrecomputeCalledCode b))
      (Spec.Ffdh.generationPrecomputeContract (abi.withConsts Impl.Ffdh.Arm.VettedGroups.tableConsts) 176) 32 :=
  verifiedScrubbedAll (api := Spec.Ffdh.generationPrecomputeApi)
    { code := combPrecomputeCalledCode b, verified := combPrecomputeCalled_verified b }
    Scrub.generationPrecomputeOut (scrubSideF_of (Scrub.precomputeOk b) Scrub.frameOk_176 _)

open VG.Proof.Bignum.Arm in
/-- `vg_ffdh_generate_key_search_cached`, with the Montgomery product `b`. -/
theorem cachedKeySearch (b : MontBackend) :
    VerifiedScrubbed target (Impl.Ffdh.Arm.Fn.cachedKeySearch (KeySearch.calledCode (CachedKeyGenerate.backend b)))
      (Spec.Ffdh.cachedKeySearchContract abi 240) 32 :=
  verifiedScrubbedAll (api := Spec.Ffdh.cachedKeySearchApi)
    { code := KeySearch.calledCode (CachedKeyGenerate.backend b)
      verified := KeySearch.verified (CachedKeyGenerate.backend b) }
    Scrub.cachedKeySearchOut (scrubSideF_of (Scrub.cachedSearchOk b) Scrub.frameOk_240 _)

open VG.Proof.MillerRabin.Arm in
/-- `vg_ffdh_generate_parameters`, with the Miller–Rabin round `v`. -/
theorem sievedParameterSearch (v : RoundImpl) :
    VerifiedScrubbed target
      (Impl.Ffdh.Arm.Fn.sievedParameterSearch (Impl.Ffdh.Arm.ParameterSearch.code
        (.call (parameterBackend v).candidateName (parameterBackend v).candidate)))
      (Spec.Ffdh.sievedParameterSearchContract abi 232) 32 :=
  verifiedScrubbedAll (api := Spec.Ffdh.sievedParameterSearchApi)
    { code := Impl.Ffdh.Arm.ParameterSearch.code
        (.call (parameterBackend v).candidateName (parameterBackend v).candidate)
      verified := ParameterSearch.verified (parameterBackend v) }
    Scrub.sievedParameterSearchOut (scrubSideF_of (Scrub.parameterSearchOk v) Scrub.frameOk_232 _)

end VG.Proof.Ffdh.Arm.Fn
