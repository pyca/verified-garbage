module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
import VerifiedGarbage.Proof.Ffdh.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSA's precomputation and key generation on AArch64, without secret residue

The postconditions of `vg_rsa_public_precompute`, `vg_rsa_generate_init` and
`vg_rsa_generate` read the memory on return only within their outputs
(`ScrubAll.ScrubAllOk`, as x86-64's `Proof/Rsa/X86_64/Scrub.lean` and
`Proof/RsaKeyGen/X86_64/KeyInitScrub.lean` prove them): each implementation
returns with every register it may leave secret cleared, and its whole stack
zeroed, if it has one (`Impl.Residue.AArch64.scrubAll`, in the function as emitted).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Proof.Ffdh.AArch64.Scrub

theorem publicPrecomputeOk (stack : Nat) :
    ScrubAllOk (Spec.Rsa.publicPrecomputeContract abi stack) stack
      (Spec.Rsa.publicPrecomputeSig.retBits abi.ptrBits) :=
  scrubAllOk_any (sig := Spec.Rsa.publicPrecomputeSig) (Nat.le_of_ble_eq_true rfl) fun
    | [pre, preLen, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Rsa.publicPrecomputeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec (Spec.Rsa.publicPrecomputeSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.Rsa.publicPrecomputeSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e : ∀ X, X = preLen.toNat → Spec.Rsa.wordsAt m₂ pre X = Spec.Rsa.wordsAt m₁ pre X :=
        fun X hX => hX ▸ wordsAt_of hb.1
      rw [e _ (toNat_sw preLen)]
      exact h

/-- `n` words at `q` are the same in two memories that agree on the `N`
bytes at `q`, `8 * n ≤ N`. -/
theorem wordsAt_congr {m₁ m₂ : Mem} {q : Addr} {k N : Nat} (hk : 8 * k ≤ N) (hN : N < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    Spec.Rsa.wordsAt m₂ q k = Spec.Rsa.wordsAt m₁ q k :=
  List.map_congr_left fun i hi => Mem.readW_congr fun t ht => by
    have := List.mem_range.mp hi
    rw [Offset.add_add]
    exact (h _ (Offset.contains_base _ (by omega_using [hk, ht, this]) (by omega_using [hk, hN, ht, this]))).symm

theorem keyInitOk :
    ScrubAllOk (Spec.RsaKeyGen.keyInitContract abi) 0 (Spec.RsaKeyGen.keyInitSig.retBits abi.ptrBits) :=
  scrubAllOk_regs0 (sig := Spec.RsaKeyGen.keyInitSig) (Nat.le_of_ble_eq_true rfl) fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨a0, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨a1, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨a2, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨a3, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.RsaKeyGen.keyInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size] at hb
    have h7 := wordsAt_congr (k := 7) (by decide) (by decide) hb.1
    have h6 := wordsAt_congr (k := 6) (by decide) (by decide) hb.1
    have hB : Spec.Rsa.bytesAt m₂ (a0 + 48) 8 = Spec.Rsa.bytesAt m₁ (a0 + 48) 8 := by
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have := List.mem_range.mp hi
      rw [show (a0 + 48 : Addr) = a0 + BitVec.ofNat 64 48 from rfl, Offset.add_add]
      exact (hb.1 _ (Offset.contains_base _ (by omega_using [this]) (by omega_using [this]))).symm
    change @Curry.apply (Mem → Mem → BitVec (Spec.RsaKeyGen.keyInitSig.retBits abi.ptrBits) → Prop) [_, _, _, _] _ _ _ m₁ r at h
    change @Curry.apply (Mem → Mem → BitVec (Spec.RsaKeyGen.keyInitSig.retBits abi.ptrBits) → Prop) [_, _, _, _] _ _ _ m₂ r
    dsimp only [Curry.apply] at h ⊢
    rw [show ArgWord.addr.ofRaw a0 = a0 from rfl, h7, h6, hB]; exact h

/-- The 8 octets at `state + 48` lie in the 56 bytes of `state`. -/
theorem bytesAt48_of {m₁ m₂ : Mem} {o : Addr}
    (h : ∀ a, Region.Contains ⟨o, 7 * 8⟩ a 1 → m₁ a = m₂ a) :
    Spec.Rsa.bytesAt m₂ (o + 48) 8 = Spec.Rsa.bytesAt m₁ (o + 48) 8 := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  have e : o + 48 + BitVec.ofNat 64 i = o + BitVec.ofNat 64 (48 + i) := Offset.add_add o 48 i
  rw [e]
  exact (h _ (contains_of (by omega))).symm

theorem keySearchOk (stack : Nat) (hW : 0 < stack := by decide) :
    ScrubAllOk (Spec.RsaKeyGen.keySearchContract abi stack) stack
      (Spec.RsaKeyGen.keySearchSig.retBits abi.ptrBits) :=
  scrubAllOk_regs_pre (sig := Spec.RsaKeyGen.keySearchSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _) fun
    | [key, keyLen, used, _, _, _, _, state], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaKeyGen.keySearchSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaKeyGen.keySearchSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaKeyGen.keySearchSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = keyLen.toNat → Spec.Rsa.bytesAt m₂ key X = Spec.Rsa.bytesAt m₁ key X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ (by rw [← hp.2.1]; exact toNat_sw keyLen), wordsAt_of hb.2.1, wordsAt_of hb.2.2.2.2,
        bytesAt48_of hb.2.2.2.2]
      exact h

/-! ## With arguments on the stack -/

theorem crtValuesOk (stack : Nat) :
    ScrubAllOk (Spec.Rsa.crtValuesContract abi stack) stack (Spec.Rsa.crtValuesSig.retBits abi.ptrBits) :=
  scrubAllOk_args_pre_any (sig := Spec.Rsa.crtValuesSig) fun
    | [dp, dpLen, dq, dqLen, qinv, qinvLen, _, _, _, pLen, _, qLen, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.Rsa.crtValuesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec (Spec.Rsa.crtValuesSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.Rsa.crtValuesSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
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

theorem checkKeyOk (stack : Nat) :
    ScrubAllOk (Spec.Rsa.checkKeyContract abi stack) stack (Spec.Rsa.checkKeySig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.Rsa.checkKeySig) fun
    | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem recoverPrimesDetOk (stack : Nat) :
    ScrubAllOk (Spec.Rsa.recoverPrimesDetContract abi stack) stack (Spec.Rsa.recoverPrimesDetSig.retBits abi.ptrBits) :=
  scrubAllOk_args_pre_any (sig := Spec.Rsa.recoverPrimesDetSig) fun
    | [p, pLen, q, qLen, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.Rsa.recoverPrimesDetSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec (Spec.Rsa.recoverPrimesDetSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.Rsa.recoverPrimesDetSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
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


theorem writtenRandom_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} {r : BitVec 32} {v : Option (List Byte)}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (h : Spec.RsaPkcs1Enc.writtenRandom m₁ o n r v) :
    Spec.RsaPkcs1Enc.writtenRandom m₂ o n r v := by
  cases v <;> simpa only [Spec.RsaPkcs1Enc.writtenRandom, e] using h

theorem pkcs1EncryptRandomOk (stack : Nat) :
    ScrubAllOk (Spec.RsaPkcs1Enc.encryptRandomContract abi stack) stack (Spec.RsaPkcs1Enc.encryptRandomSig.retBits abi.ptrBits) :=
  scrubAllOk_args_pre_any (sig := Spec.RsaPkcs1Enc.encryptRandomSig) fun
    | [out, outLen, tape, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaPkcs1Enc.encryptRandomSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaPkcs1Enc.encryptRandomSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaPkcs1Enc.encryptRandomSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have hol := hp.2.1
      rw [toNat_sw] at hol
      have e' := e _ hol.symm
      rw [wordsAt_of hb.2.1]
      refine ⟨h.1, ?_⟩
      have h2 := h.2
      revert h2
      generalize (Spec.RsaPkcs1Enc.padSearch _ _).outcome = o
      match o with
      | .accepted _ => exact fun h2 hP => writtenRandom_of e' (h2 hP)
      | .entropy .. => simp only [e']; exact id
      | .exhausted => simp only [e']; exact id

theorem pkcs1VerifyOk (stack : Nat) :
    ScrubAllOk (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi stack) stack (Spec.RsaPkcs1Sig.verifyPrecomputedSig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.RsaPkcs1Sig.verifyPrecomputedSig) fun
    | [_, _, _, _, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem pkcs1RecoverOk (stack : Nat) :
    ScrubAllOk (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi stack) stack (Spec.RsaPkcs1Sig.recoverPrecomputedSig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.RsaPkcs1Sig.recoverPrecomputedSig) fun
    | [out, outLen, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.RsaPkcs1Sig.recoverPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaPkcs1Sig.recoverPrecomputedSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaPkcs1Sig.recoverPrecomputedSig.retBits abi.ptrBits) → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e := bytesAt_of hb.1
      exact fun hP H hH => written_of (by rw [toNat_sw]; exact e) (h hP H hH)

theorem privatePrecomputeOk (stack : Nat) :
    ScrubAllOk (Spec.Rsa.privatePrecomputeContract abi stack) stack
      (Spec.Rsa.privatePrecomputeSig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := Spec.Rsa.privatePrecomputeSig) fun
    | [pre, preLen, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.Rsa.privatePrecomputeSig, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec (Spec.Rsa.privatePrecomputeSig.retBits abi.ptrBits) → Prop)
        [_, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.Rsa.privatePrecomputeSig.retBits abi.ptrBits) → Prop)
        [_, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e := wordsAt_of (n := (preLen.setWidth abi.ptrBits).toNat) hb.1 (by rw [toNat_sw])
      revert h
      split
      · exact fun h => ⟨h.1, e.trans h.2⟩
      · exact fun h => ⟨h.1, e.trans h.2⟩

theorem writtenMsg_of {m₁ m₂ : Mem} {o l : Addr} {n : Nat} {r : BitVec 32} {v : Spec.Rsa.Outcome}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (el : Spec.Rsa.wordsAt m₂ l 1 = Spec.Rsa.wordsAt m₁ l 1)
    (h : Spec.RsaPkcs1Enc.writtenMsg m₁ o l n r v) : Spec.RsaPkcs1Enc.writtenMsg m₂ o l n r v := by
  cases v <;> simpa only [Spec.RsaPkcs1Enc.writtenMsg, e, el] using h

theorem pkcs1DecryptOk (stack : Nat) :
    ScrubAllOk (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stack) stack
      (Spec.RsaPkcs1Enc.decryptPrecomputedSig.retBits abi.ptrBits) :=
  scrubAllOk_args_pre_any (sig := Spec.RsaPkcs1Enc.decryptPrecomputedSig) fun
    | [out, outLen, ml, _, nLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaPkcs1Enc.decryptPrecomputedSig, Spec.RsaPkcs1Enc.decryptSig, List.cons_append,
        List.nil_append, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaPkcs1Enc.decryptPrecomputedSig.retBits abi.ptrBits) → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaPkcs1Enc.decryptPrecomputedSig.retBits abi.ptrBits) → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have hol := hp.2.1
      rw [toNat_sw, toNat_sw] at hol
      exact writtenMsg_of (e _ (by rw [toNat_sw]; exact hol.symm)) (wordsAt_of hb.2.1) h

theorem writtenOutcome_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} {r : BitVec 32} {v : Spec.Rsa.Outcome}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (h : Spec.Rsa.writtenOutcome m₁ o n r v) :
    Spec.Rsa.writtenOutcome m₂ o n r v := by
  cases v <;> simpa only [Spec.Rsa.writtenOutcome, e] using h

theorem pkcs1SignOk (stack : Nat) :
    ScrubAllOk (Spec.RsaPkcs1Sig.signPrecomputedContract abi stack) stack
      (Spec.RsaPkcs1Sig.signPrecomputedSig.retBits abi.ptrBits) :=
  scrubAllOk_args_pre_any (sig := Spec.RsaPkcs1Sig.signPrecomputedSig) fun
    | [out, outLen, _, nLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaPkcs1Sig.signPrecomputedSig, Spec.RsaPkcs1Sig.signSig, List.cons_append,
        List.nil_append, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaPkcs1Sig.signPrecomputedSig.retBits abi.ptrBits) → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec (Spec.RsaPkcs1Sig.signPrecomputedSig.retBits abi.ptrBits) → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have hol := hp.2.1
      rw [toNat_sw, toNat_sw] at hol
      exact writtenOutcome_of (e _ (by rw [toNat_sw]; exact hol.symm)) h

end VG.Proof.Rsa.AArch64.Scrub
