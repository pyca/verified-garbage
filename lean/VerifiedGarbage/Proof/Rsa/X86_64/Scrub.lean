module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
public import VerifiedGarbage.Spec.RsaPss.MdTable
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Ffdh.X86_64.Scrub
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSA's public-key, key-checking and key-generation functions on x86-64, without secret residue

The postconditions of RSA's public-key operations, its key checks and
conversions, and its key search read the memory on return only within
their outputs (`X86_64.Scrub.PostOut`): verification and the key check not
at all, the others the octets at `out` (or the key's buffer, or `p` and
`q`, or `dp`, `dq` and `qinv`), the words at `pre`, and the words of `tape`,
`used` and `state` (`Ffdh.X86_64.Scrub.bytesAt_of`, `wordsAt_of`). Each
implementation returns with its whole stack wiped
(`X86_64.Scrub.withScrubAll` and the routes built on it).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Proof.Ffdh.X86_64.Scrub

/-- `postOut_of_local`, given the number of the signature's words: the patterns of `hl` are then
matched against that numeral, not against the signature's evaluated length once for each. -/
theorem postOut_of_local_len {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (n : Nat) (hn : (sig.words A.ptrBits).length = n)
    (hl : ∀ vs m m₁ m₂ r, vs.length = n →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) :=
  postOut_of_local hA fun vs m m₁ m₂ r hv => hl vs m m₁ m₂ r (hv.trans hn)

/-- `postOut_of_local_pre`, given the number of the signature's words. -/
theorem postOut_of_local_pre_len {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (n : Nat) (hn : (sig.words A.ptrBits).length = n)
    (hl : ∀ vs m m₁ m₂ r, vs.length = n →
      Curry.apply (sig.words A.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) :=
  postOut_of_local_pre hA fun vs m m₁ m₂ r hv => hl vs m m₁ m₂ r (hv.trans hn)

theorem toNat_sw0 (x : BitVec 64) : (x.setWidth abi.ptrBits).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, ScrubAbi.plain.ptrBits]
  exact Nat.mod_eq_of_lt x.isLt

theorem toNat_swT (sig : Sig) (ts : List (String × List FnTable)) (x : BitVec 64) :
    (x.setWidth (abi.withTables sig ts).ptrBits).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, (ScrubAbi.plain.tables sig ts).ptrBits]
  exact Nat.mod_eq_of_lt x.isLt

/-! ## `Spec.Rsa` -/

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
      rw [e _ (toNat_sw0 preLen)]
      exact h

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
      rw [toNat_sw0] at hdp hdq hqi
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
      rw [toNat_sw0] at hpl hql
      have ep := e₁ _ hpl.symm
      have eq := e₂ _ hql.symm
      cases v <;> simp only [Spec.Rsa.writtenAll, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, ep, eq] <;> exact id

/-! ## Key generation -/

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

theorem keySearchOut (stack : Nat) :
    PostOut (Spec.RsaKeyGen.keySearchContract abi stack) (Spec.RsaKeyGen.keySearchSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain fun
    | [key, keyLen, used, _, _, _, _, state], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaKeyGen.keySearchSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = keyLen.toNat → Spec.Rsa.bytesAt m₂ key X = Spec.Rsa.bytesAt m₁ key X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      rw [e _ (by rw [← hp.2.1]; exact toNat_sw [] keyLen), wordsAt_of hb.2.1, wordsAt_of hb.2.2.2.2,
        bytesAt48_of hb.2.2.2.2]
      exact h

/-! ## Public-key operations -/

theorem oaepEncryptOut (ts : List FnTable) (stack : Nat) :
    PostOut (Spec.RsaOaep.encryptMdTablesContract
        (abi.withTables Spec.RsaOaep.encryptMdTablesSig [("hash", ts), ("mgf1", ts)]) stack)
      (Spec.RsaOaep.encryptMdTablesSig.retBits 64) :=
  postOut_of_local_pre_len (leak := some _) (ScrubAbi.plain.tables _ _) 18 rfl fun
    | [out, outLen, _, nLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaOaep.encryptMdTablesSig, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have hol := hp.2.1
      rw [toNat_swT] at hol
      have e' := e _ hol.symm
      exact fun H G hH hG hP => written_of e' (h H G hH hG hP)

theorem writtenRandom_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} {r : BitVec 32} {v : Option (List Byte)}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (h : Spec.RsaPkcs1Enc.writtenRandom m₁ o n r v) :
    Spec.RsaPkcs1Enc.writtenRandom m₂ o n r v := by
  cases v <;> simpa only [Spec.RsaPkcs1Enc.writtenRandom, e] using h

theorem pkcs1EncryptRandomOut (stack : Nat) :
    PostOut (Spec.RsaPkcs1Enc.encryptRandomContract abi stack) (Spec.RsaPkcs1Enc.encryptRandomSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain fun
    | [out, outLen, tape, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaPkcs1Enc.encryptRandomSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have hol := hp.2.1
      rw [toNat_sw0] at hol
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

theorem pkcs1VerifyOut (stack : Nat) :
    PostOut (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi stack)
      (Spec.RsaPkcs1Sig.verifyPrecomputedSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [_, _, _, _, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

theorem pkcs1RecoverOut (stack : Nat) :
    PostOut (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi stack)
      (Spec.RsaPkcs1Sig.recoverPrecomputedSig.retBits 64) :=
  postOut_of_local (leak := some _) ScrubAbi.plain fun
    | [out, outLen, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hb, h => by
      simp only [Spec.RsaPkcs1Sig.recoverPrecomputedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at h ⊢
      have e := bytesAt_of hb.1
      exact fun hP H hH => written_of (by rw [toNat_sw0]; exact e) (h hP H hH)

theorem pssVerifyOut (tsH tsG : List FnTable) (stack : Nat) :
    PostOut (Spec.RsaPss.verifyPrecomputedMdTableContract
        (abi.withTables Spec.RsaPss.verifyPrecomputedMdTableSig [("hash", tsH), ("mgf1", tsG)]) stack)
      (Spec.RsaPss.verifyPrecomputedMdTableSig.retBits 64) :=
  postOut_of_local_len (leak := some _) (ScrubAbi.plain.tables _ _) 16 rfl fun
    | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _, _, _, _, _, _, h => h

end VG.Proof.Rsa.X86_64.Scrub
