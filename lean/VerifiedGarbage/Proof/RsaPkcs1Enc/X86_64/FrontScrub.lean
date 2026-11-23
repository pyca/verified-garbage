module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86_64.Front
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Front
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.QualifiedName
import VerifiedGarbage.Proof.Sha256.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_rsa_pkcs1_decrypt_precomputed_front` on x86-64, without secret residue

The function as emitted (`Impl.RsaPkcs1Enc.X86_64.Fn.decryptPrecomputedFront`)
over any implementation of SHA-256's compression function and of the private
CRT operation: `Front.code`, calling `vg_rsa_pkcs1_decrypt_precomputed`'s
code before its cleanup as an internal function of its own (`bodyName`), then
the cleanup of the 3784 bytes of stack it and its callee use, at the level of
the callee's cleanup. Its code is its code with a stub for the callee
(`frontStub`), evaluated once, and the callee's code meets what the cleanup
needs of a callee (`calleeSide`) by what `Scrub.lean` evaluates of
decryption's code with stubs (`dec_stub0`, `dec_stub112`, `dec_stub560`).
-/

-- separate module: the kernel's evaluation of the cleanup's side condition, which a registration file may not hold

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Front

open VG VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.RsaPkcs1Enc.X86_64.Scrub (decStub decLevel dec_fill dec_stub0 dec_stub112 dec_stub560 init_side)

/-- The name of `vg_rsa_pkcs1_decrypt_precomputed`'s code before its
cleanup, calling `h` and `c`, an internal function. -/
def bodyName (h : Proof.Sha256.X86_64.Compress) (c : CrtImpl) : String :=
  "vg_rsa_pkcs1_decrypt_precomputed_body" ++ qualifiedName "" [("sha256", h.suffix), ("crt", c.suffix)]

/-- `vg_rsa_pkcs1_decrypt_precomputed`'s code before its cleanup, over `h`
and `c`. -/
abbrev decCode (h : Proof.Sha256.X86_64.Compress) (c : CrtImpl) : Prog isa :=
  Impl.RsaPkcs1Enc.X86_64.Decrypt.codeP (Dec.HH h) (Dec.privNameP c) (Dec.privCodeP c)

/-- The function's code with a stub in its callee's place. -/
def frontStub : Prog isa := Impl.RsaPkcs1Enc.X86_64.Front.code "body" (.block [])

/-- The stack the callee needs. -/
def frontStack : String → Nat := fun _ => 3480

theorem front_stub : stubSide frontStub VecLevel.sse.level frontStack 3784 [] = true := by lit_decide

theorem stubCallee_of_side {a : Prog isa} {k : Nat} {n : String → Nat} {m : Nat}
    (h : stubSide a k n m [] = true) : stubCallee a k n m = true := by
  simp only [stubSide, stubCallee, tablesCall, Bool.and_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  obtain ⟨-, hi⟩ := h
  rw [List.isEmpty_iff]
  rw [List.all_eq_true] at hi
  match hn : UpperLock.inames a, hi with
  | [], _ => rfl
  | f :: _, hi => exact absurd (of_decide_eq_true (hi f (List.mem_cons_self ..))) (by simp [tableFns])

/-- What the cleanup needs of the callee, at the level of decryption's
cleanup. -/
theorem dec_side (h : Proof.Sha256.X86_64.Compress) (c : CrtImpl) :
    calleeSide (decCode h c) (decLevel h c).level 3480 = true := by
  have hk₁ := level_join_left h.level (c.level.join c.pubOp.level)
  have hk₂ := level_join_right h.level (c.level.join c.pubOp.level)
  have hh := calleeSide_mono hk₁ (Nat.le_refl _) h.side
  have hc := calleeSide_mono (Nat.le_trans (level_join_left _ _) hk₂) (Nat.le_refl _) c.sideP
  have hp := calleeSide_mono (Nat.le_trans (level_join_right _ _) hk₂) (Nat.le_refl _) c.pubOp.side
  have hi : calleeSide Impl.Sha256.X86_64.Stream.init (decLevel h c).level 0 = true :=
    calleeSide_mono (Nat.zero_le _) (Nat.le_refl _) init_side
  rcases h.hso with e | e | e
  · exact calleeSide_of_fill (dec_fill h c e hh hi hc hp) (Nat.zero_le _) (stubCallee_of_side dec_stub0)
  · exact calleeSide_of_fill (dec_fill h c e hh hi hc hp) (Nat.zero_le _) (stubCallee_of_side dec_stub112)
  · exact calleeSide_of_fill (dec_fill h c e hh hi hc hp) (Nat.zero_le _) (stubCallee_of_side dec_stub560)

theorem dec_depth (h : Proof.Sha256.X86_64.Compress) (c : CrtImpl) : (decCode h c).x86_64Depth ≤ 3480 := by
  have := dec_side h c
  simp only [calleeSide, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.1

/-- It writes `rsp` only in its frames, and its callee's. -/
theorem front_spSafe {name : String} {callee : Prog isa} (h : callee.all (fun i => !isa.writesSp i) = true) :
    (Impl.RsaPkcs1Enc.X86_64.Front.code name callee).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.RsaPkcs1Enc.X86_64.Front.code, Impl.RsaPkcs1Enc.X86_64.Front.body,
    Impl.RsaPkcs1Enc.X86_64.Front.tail, Impl.RsaPkcs1Enc.X86_64.Front.toBuf, Impl.Mgf1.X86_64.seqs, Code.all, h,
    Bool.true_and]
  decide

/-- The postcondition reads the memory on return only in `out` and
`msg_len`. -/
theorem front_postOut (stack : Nat) :
    VG.X86_64.Scrub.PostOut (Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract abi stack)
      (Spec.RsaPkcs1Enc.decryptPrecomputedSig.retBits 64) := by
  rw [fK_eq]
  refine VG.X86_64.Scrub.postOut_of_local_pre (leak := some _) VG.X86_64.Scrub.ScrubAbi.plain
    fun vs m m₁ m₂ r hlen hpre hb h => ?_
  obtain ⟨o, oL, ml, n, nL, e, eL, d, dL, i, iL, p, pL, q, qL, dp, dpL, dq, dqL, qi, qiL, sc, scL, pre, preL, rfl⟩ :=
    vs25 hlen
  simp only [sig, Spec.RsaPkcs1Enc.decryptPrecomputedSig, Spec.RsaPkcs1Enc.decryptSig, Sig.bufs, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size,
    Nat.mul_one] at hb
  obtain ⟨bo, bm, -⟩ := hb
  replace hpre : preP o oL ml n nL e eL d dL i iL p pL q qL dp dpL dq dqL qi qiL sc scL pre preL m := hpre
  simp only [preP, toNat_ptr] at hpre
  have hol := hpre.2.1
  replace h : postFP o oL ml n nL e eL d dL i iL p pL q qL dp dpL dq dqL qi qiL sc scL pre preL m m₁ r := h
  show postFP o oL ml n nL e eL d dL i iL p pL q qL dp dpL dq dqL qi qiL sc scL pre preL m m₂ r
  simp only [postFP, toNat_ptr] at h ⊢
  have hby : Spec.Rsa.bytesAt m₂ o nL.toNat = Spec.Rsa.bytesAt m₁ o nL.toNat :=
    bytes_ag (k := nL.toNat) bo (by omega_arith)
  have hw : Spec.Rsa.wordsAt m₂ ml 1 = Spec.Rsa.wordsAt m₁ ml 1 := words_ag (k := 1) bm (by omega_arith)
  revert h
  generalize Spec.RsaPkcs1Enc.decrypt _ _ _ _ _ _ _ _ _ = oc
  cases oc <;> simp only [Spec.RsaPkcs1Enc.writtenMsgFront, hby, hw] <;> exact id

/-- `vg_rsa_pkcs1_decrypt_precomputed_front` over `h` and `c`, before its
cleanup. -/
def frontPlain (h : Proof.Sha256.X86_64.Compress) (c : CrtImpl) :
    Unscrubbed Spec.RsaPkcs1Enc.decryptPrecomputedFrontApi target where
  code := Impl.RsaPkcs1Enc.X86_64.Front.code (bodyName h c) (decCode h c)
  verified := front_verified (Dec.decryptPrecomputed_verified h c) (Dec.decP_spSafe h c) (dec_depth h c)
  spSafe := front_spSafe (Dec.decP_spSafe h c)

theorem front_fill (h : Proof.Sha256.X86_64.Compress) (c : CrtImpl) :
    Fill (decLevel h c).level frontStack frontStub
      (Impl.RsaPkcs1Enc.X86_64.Front.code (bodyName h c) (decCode h c)) := by
  refine Fill.frame _ _ (Fill.seq (Fill.block _) (Fill.seq (Fill.hole _ _ (dec_side h c)) (Fill.seq (Fill.block _) ?_)))
  unfold Impl.RsaPkcs1Enc.X86_64.Front.tail Impl.RsaPkcs1Enc.X86_64.Front.toBuf
  fill_calls

/-- `Spec.RsaPkcs1Enc.decryptPrecomputedFrontApi`'s function as emitted over
`h` and `c` meets its contract in constant time and returns without secret
residue. -/
theorem front_scrubbed (h : Proof.Sha256.X86_64.Compress) (c : CrtImpl) :
    VerifiedScrubbed target
      (Impl.RsaPkcs1Enc.X86_64.Fn.decryptPrecomputedFront (decLevel h c) (bodyName h c) (decCode h c))
      (Spec.RsaPkcs1Enc.decryptPrecomputedFrontApi.contract X86_64.abi 3784) 32 :=
  verifiedScrubbedAllFill (frontPlain h c) _ (front_postOut _) (front_fill h c) (Nat.zero_le _) (Nat.le_refl _)
    (ha := front_stub)

theorem front_scrubbed_spSafe (h : Proof.Sha256.X86_64.Compress) (c : CrtImpl) :
    (Impl.RsaPkcs1Enc.X86_64.Fn.decryptPrecomputedFront (decLevel h c) (bodyName h c) (decCode h c)).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (front_spSafe (Dec.decP_spSafe h c))

end VG.Proof.RsaPkcs1Enc.X86_64.Front
