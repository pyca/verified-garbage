module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.Front
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_rsa_pkcs1_decrypt_precomputed_front` on PPC64LE, without secret residue

The function as emitted (`Impl.RsaPkcs1Enc.PPC64LE.Fn.decryptPrecomputedFront`):
`Front.code`, calling `vg_rsa_pkcs1_decrypt_precomputed`'s code before its
cleanup (`Decrypt.codeP`) as an internal function of its own
(`Front.bodyName`), then the cleanup of the 3920 bytes of stack it and its
callee use and of every volatile register, as for
`vg_rsa_pkcs1_decrypt_precomputed` (`Scrub.lean`). Its postcondition reads
the memory on return only within `out` and `msg_len` (`frontOut`).
-/

-- separate module: the kernel's evaluation of the cleanup's side condition over the callee's code, which a registration file may not hold

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Front

open VG VG.PPC64LE

open VG.PPC64LE.Scrub

/-- `postOut_of_local`, for a postcondition that reads the memory on return
only within the buffers when the precondition holds (as
`Proof.Rsa.PPC64LE.Scrub.postOut_of_local_pre`, whose module imports the
algebra of the modular inverse). -/
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

theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨o, n * 1⟩ a 1 → m₁ a = m₂ a) :
    Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (contains_of (by omega_using [this]))).symm

theorem wordsAt_of {m₁ m₂ : Mem} {o : Addr} {n N : Nat}
    (h : ∀ a, Region.Contains ⟨o, N⟩ a 1 → m₁ a = m₂ a) (hN : n * 8 ≤ N := by omega) :
    Spec.Rsa.wordsAt m₂ o n = Spec.Rsa.wordsAt m₁ o n :=
  List.map_congr_left fun i hi => Mem.readW_congr fun t ht => by
    have := List.mem_range.mp hi
    rw [Offset.add_add]
    exact (h _ (contains_of (by simp only [Nat.reduceDiv] at ht; omega_using [hN, ht, this]))).symm

theorem toNat_sw (x : BitVec 64) : (x.setWidth abi.ptrBits).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, ScrubAbi.plain.ptrBits]
  exact Nat.mod_eq_of_lt x.isLt

theorem writtenMsgFront_of {m₁ m₂ : Mem} {o l : Addr} {n : Nat} {r : BitVec 32} {v : Spec.Rsa.Outcome}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (el : Spec.Rsa.wordsAt m₂ l 1 = Spec.Rsa.wordsAt m₁ l 1)
    (h : Spec.RsaPkcs1Enc.writtenMsgFront m₁ o l n r v) : Spec.RsaPkcs1Enc.writtenMsgFront m₂ o l n r v := by
  cases v <;> simpa only [Spec.RsaPkcs1Enc.writtenMsgFront, e, el] using h

/-- The postcondition reads the memory on return only in `out` and
`msg_len`. -/
theorem frontOut (stack : Nat) :
    PostOut (Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract abi stack)
      (Spec.RsaPkcs1Enc.decryptPrecomputedSig.retBits 64) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain fun
    | [out, outLen, ml, _, nLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaPkcs1Enc.decryptPrecomputedSig, Spec.RsaPkcs1Enc.decryptSig, List.cons_append,
        List.nil_append, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e : ∀ X, X = outLen.toNat → Spec.Rsa.bytesAt m₂ out X = Spec.Rsa.bytesAt m₁ out X :=
        fun X hX => hX ▸ bytesAt_of hb.1
      have hol := hp.2.1
      rw [toNat_sw, toNat_sw] at hol
      exact writtenMsgFront_of (e _ (by rw [toNat_sw]; exact hol.symm)) (wordsAt_of hb.2.1) h

/-- The stack `vg_rsa_pkcs1_decrypt_precomputed`'s code uses. -/
theorem codeP_sdepth : sdepth Impl.RsaPkcs1Enc.PPC64LE.Decrypt.codeP ≤ 3648 := by lit_decide

/-- `vg_rsa_pkcs1_decrypt_precomputed_front` as emitted
(`Impl.RsaPkcs1Enc.PPC64LE.Fn.decryptPrecomputedFront`) meets its contract
in constant time and returns without secret residue. -/
theorem front_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.RsaPkcs1Enc.PPC64LE.Fn.decryptPrecomputedFront
      (Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract PPC64LE.abi fStack) 32 :=
  verifiedScrubbedAll (api := Spec.RsaPkcs1Enc.decryptPrecomputedFrontApi) {
      code := Impl.RsaPkcs1Enc.PPC64LE.Front.code Impl.RsaPkcs1Enc.PPC64LE.Front.bodyName
        Impl.RsaPkcs1Enc.PPC64LE.Decrypt.codeP
      verified := front_verified Dec.codeP_verified codeP_sdepth }
    3920 Impl.Scrub.PPC64LE.Clear.all
    (frontOut _)
    (by dsimp only; lit_decide)

end VG.Proof.RsaPkcs1Enc.PPC64LE.Front
