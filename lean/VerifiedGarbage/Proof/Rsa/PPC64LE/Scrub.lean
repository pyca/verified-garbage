module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreVerified
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PrivPreVerified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvVerified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcVerified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdVerified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.IbInverse
public import VerifiedGarbage.Proof.Divstep.TcSBounds
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit

/-!
# RSA's key functions on PPC64LE, without secret residue

`vg_rsa_public_precompute`, `vg_rsa_private_precompute`,
`vg_rsa_crt_values`, `vg_rsa_check_key` and `vg_rsa_recover_primes_det`,
each followed by `Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.verifiedScrubbed`).
None has a frame, so the tail only clears the volatile registers each may
write. Their postconditions read the memory on return only within their
outputs (`PPC64LE.Scrub.PostOut`), as on x86-64
(`Proof/Rsa/X86_64/Scrub.lean`) and AArch64 (`Proof/Rsa/AArch64/Scrub.lean`):
the key check not at all, the others the words at `pre`, or the octets at
`p` and `q`, or at `dp`, `dq` and `qinv` (`bytesAt_of`, `wordsAt_of`).

The lemmas before them are those of RSA's other functions on PPC64LE too
(key generation, PKCS #1 v1.5, OAEP and PSS).
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

/-! ## Reading memory only within the buffers -/

/-- `postOut_of_local`, for a postcondition that reads the memory on return
only within the buffers when the precondition holds, as on x86-64
(`X86_64.Scrub.postOut_of_local_pre`). -/
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
      · rw [hal] at hpre; exact hpre
      · rw [hal] at hpre; exact hpre.1
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hA.mem] at hpre'
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) hpre' (fun b hb a ha => ?_) hp
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

/-- The `n` octets at `o` read the memory only within `⟨o, n * 1⟩`. -/
theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨o, n * 1⟩ a 1 → m₁ a = m₂ a) :
    Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (contains_of (by omega_using [this]))).symm

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

theorem toNat_sw (x : BitVec 64) : (x.setWidth abi.ptrBits).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, ScrubAbi.plain.ptrBits]
  exact Nat.mod_eq_of_lt x.isLt

theorem toNat_swC (cs : List (String × List (BitVec 64))) (x : BitVec 64) :
    (x.setWidth (abi.withConsts cs).ptrBits).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, (ScrubAbi.consts cs).ptrBits]
  exact Nat.mod_eq_of_lt x.isLt

theorem toNat_swT (sig : Sig) (ts : List (String × List FnTable)) (x : BitVec 64) :
    (x.setWidth (abi.withTables sig ts).ptrBits).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, (ScrubAbi.plain.tables sig ts).ptrBits]
  exact Nat.mod_eq_of_lt x.isLt

/-! ## Postconditions -/

theorem publicPrecomputeOut (stack : Nat) :
    PostOut (Spec.Rsa.publicPrecomputeContract abi stack) (Spec.Rsa.publicPrecomputeSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [pre, preLen, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Rsa.publicPrecomputeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = preLen.toNat → Spec.Rsa.wordsAt m₂ pre X = Spec.Rsa.wordsAt m₁ pre X :=
        fun X hX => hX ▸ wordsAt_of hb.1
      rw [e _ (toNat_sw preLen)]
      exact h

theorem privatePrecomputeOut (stack : Nat) :
    PostOut (Spec.Rsa.privatePrecomputeContract abi stack) (Spec.Rsa.privatePrecomputeSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [pre, preLen, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Rsa.privatePrecomputeSig, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e := wordsAt_of (n := (preLen.setWidth abi.ptrBits).toNat) hb.1 (by rw [toNat_sw])
      revert h
      split
      · exact fun h => ⟨h.1, e.trans h.2⟩
      · exact fun h => ⟨h.1, e.trans h.2⟩

theorem crtValuesOut (stack : Nat) :
    PostOut (Spec.Rsa.crtValuesContract abi stack) (Spec.Rsa.crtValuesSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain fun
    | [dp, dpLen, dq, dqLen, qinv, qinvLen, _, _, _, pLen, _, qLen, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.Rsa.crtValuesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      obtain ⟨-, -, -, -, -, hdp, hqi, hdq, -⟩ := hp
      have e₁ : ∀ X, X = dpLen.toNat → Spec.Rsa.bytesAt m₂ dp X = Spec.Rsa.bytesAt m₁ dp X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have e₂ : ∀ X, X = dqLen.toNat → Spec.Rsa.bytesAt m₂ dq X = Spec.Rsa.bytesAt m₁ dq X :=
        fun X hX => hX ▸ bytesAt_of hb.2.1
      have e₃ : ∀ X, X = qinvLen.toNat → Spec.Rsa.bytesAt m₂ qinv X = Spec.Rsa.bytesAt m₁ qinv X :=
        fun X hX => hX ▸ bytesAt_of hb.2.2.1
      revert h
      generalize Option.map _ _ = v
      rw [toNat_sw] at hdp hdq hqi
      have ep := e₁ _ hdp.symm
      have eq := e₂ _ hdq.symm
      have ei := e₃ _ hqi.symm
      cases v <;> simp only [Spec.Rsa.writtenAll, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, ep, eq, ei] <;> exact id

theorem checkKeyOut (stack : Nat) :
    PostOut (Spec.Rsa.checkKeyContract abi stack) (Spec.Rsa.checkKeySig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem recoverPrimesDetOut (stack : Nat) :
    PostOut (Spec.Rsa.recoverPrimesDetContract abi stack) (Spec.Rsa.recoverPrimesDetSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain fun
    | [p, pLen, q, qLen, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.Rsa.recoverPrimesDetSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      obtain ⟨-, hpl, hql, -⟩ := hp
      have e₁ : ∀ X, X = pLen.toNat → Spec.Rsa.bytesAt m₂ p X = Spec.Rsa.bytesAt m₁ p X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have e₂ : ∀ X, X = qLen.toNat → Spec.Rsa.bytesAt m₂ q X = Spec.Rsa.bytesAt m₁ q X :=
        fun X hX => hX ▸ bytesAt_of hb.2.1
      revert h
      generalize Option.map _ _ = v
      rw [toNat_sw] at hpl hql
      have ep := e₁ _ hpl.symm
      have eq := e₂ _ hql.symm
      cases v <;> simp only [Spec.Rsa.writtenAll, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, ep, eq] <;> exact id

/-! ## The functions as emitted -/

/-- `vg_rsa_public_precompute` as emitted (`Impl.Rsa.PPC64LE.Fn.publicPrecompute`)
meets its contract in constant time and returns without secret residue. -/
theorem publicPrecompute_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Rsa.PPC64LE.Fn.publicPrecompute
      (Spec.Rsa.publicPrecomputeContract PPC64LE.abi) 32 :=
  verifiedScrubbed (api := Spec.Rsa.publicPrecomputeApi) {
      code := Impl.Bignum.PPC64LE.Precompute.precompute
      verified := Proof.Bignum.PPC64LE.Pre.precompute_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (publicPrecomputeOut _)
    (by dsimp only; lit_decide)

/-- `vg_rsa_private_precompute` as emitted
(`Impl.Rsa.PPC64LE.Fn.privatePrecompute`) meets its contract in constant time
and returns without secret residue. -/
theorem privatePrecompute_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Rsa.PPC64LE.Fn.privatePrecompute
      (Spec.Rsa.privatePrecomputeContract PPC64LE.abi) 32 :=
  verifiedScrubbed (api := Spec.Rsa.privatePrecomputeApi) {
      code := Impl.Bignum.PPC64LE.PrivPre.code
      verified := Proof.Bignum.PPC64LE.PrivPre.pp_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (privatePrecomputeOut _)
    (by dsimp only; lit_decide)

/-- `vg_rsa_crt_values` as emitted (`Impl.Rsa.PPC64LE.Fn.crtValues`) meets its
contract in constant time and returns without secret residue. -/
theorem crtValues_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Rsa.PPC64LE.Fn.crtValues
      (Spec.Rsa.crtValuesContract PPC64LE.abi) 32 :=
  verifiedScrubbed (api := Spec.Rsa.crtValuesApi) {
      code := Impl.Rsa.PPC64LE.CrtValues.code
      verified := Proof.Rsa.PPC64LE.CrtValues.cv_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (crtValuesOut _)
    (by dsimp only; lit_decide)

/-- `vg_rsa_check_key` as emitted (`Impl.Rsa.PPC64LE.Fn.checkKey`) meets its
contract in constant time and returns without secret residue. -/
theorem checkKey_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Rsa.PPC64LE.Fn.checkKey
      (Spec.Rsa.checkKeyContract PPC64LE.abi) 32 :=
  verifiedScrubbed (api := Spec.Rsa.checkKeyApi) {
      code := Impl.Rsa.PPC64LE.CheckKey.code
      verified := Proof.Rsa.PPC64LE.KeyCheck.ck_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (checkKeyOut _)
    (by dsimp only; lit_decide)

/-- `vg_rsa_recover_primes_det` as emitted
(`Impl.Rsa.PPC64LE.Fn.recoverPrimesDet`) meets its contract in constant time
and returns without secret residue. -/
theorem recoverPrimesDet_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Rsa.PPC64LE.Fn.recoverPrimesDet
      (Spec.Rsa.recoverPrimesDetContract PPC64LE.abi) 32 :=
  verifiedScrubbed (api := Spec.Rsa.recoverPrimesDetApi) {
      code := Impl.Rsa.PPC64LE.RecoverDet.code
      verified := Proof.Rsa.PPC64LE.RecDet.rd_verified }
    0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (recoverPrimesDetOut _)
    (by dsimp only; lit_decide)

end VG.Proof.Rsa.PPC64LE.Scrub
