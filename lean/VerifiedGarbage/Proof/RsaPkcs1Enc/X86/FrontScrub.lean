module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.Front
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.Scrub
public import VerifiedGarbage.Proof.Framework.QualifiedName
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
public import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.Front
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.QualifiedName
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety

/-!
# `vg_rsa_pkcs1_decrypt_precomputed_front` on x86, without secret residue

The function as emitted (`Impl.RsaPkcs1Enc.X86.Fn.decryptPrecomputedFront`)
over any implementation of SHA-256 (`Backend`) and of the private-key
operation (`CrtImpl`): `Front.code`, calling
`vg_rsa_pkcs1_decrypt_precomputed`'s code before its cleanup as an internal
function of its own (`bodyName`), then the cleanup of the 3732 bytes of
stack it and its callee use. Its code is its code with a hole of 3568 bytes
of stack for the callee (`frontStub`, `holeStub`), evaluated once
(`front_side`), and the callee's code meets what the cleanup needs of a
callee (`calleeSide`) by what `Scrub.lean` evaluates of decryption's code
(`decrypt_scrub`).
-/

-- separate module: the kernel's evaluation of the cleanup's side condition, which a registration file may not hold

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Front

open VG VG.X86 VG.X86.Scrub VG.Proof.Rsa.X86.Scrub
open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl crtPBaseline)

/-- The name of `vg_rsa_pkcs1_decrypt_precomputed`'s code before its
cleanup, over `v` and `c`, an internal function. -/
def bodyName (v : Backend) (c : CrtImpl) : String :=
  "vg_rsa_pkcs1_decrypt_precomputed_body" ++ qualifiedName "" [("sha256", v.stream.suffix), ("crt", c.suffix)]

/-- `vg_rsa_pkcs1_decrypt_precomputed`'s code before its cleanup, over `v`
and `c`. -/
abbrev decCode (v : Backend) (c : CrtImpl) : Prog isa :=
  Proof.RsaPkcs1Enc.X86.Dec.decryptCodeP v c crtPBaseline

/-- The function's code with a hole of the callee's stack in its place. -/
def frontStub : Prog isa := Impl.RsaPkcs1Enc.X86.Front.code "" (holeStub 3568)

-- The stub as a literal, for the kernel's evaluation.
materialize_code frontStub

theorem front_side : scrubFSide frontStub [] 3732 = true := by lit_decide

theorem noIcall_of_inames : ∀ {c : Prog isa}, inames c = [] → noIcall c = true
  | .block _, _ => rfl
  | .seq a b, h => by
    simp only [inames, List.append_eq_nil_iff] at h
    simp only [noIcall, noIcall_of_inames h.1, noIcall_of_inames h.2, Bool.and_self]
  | .ite _ t e, h => by
    simp only [inames, List.append_eq_nil_iff] at h
    simp only [noIcall, noIcall_of_inames h.1, noIcall_of_inames h.2, Bool.and_self]
  | .loop b _, h => noIcall_of_inames (c := b) h
  | .call _ b, h => noIcall_of_inames (c := b) h
  | .frame _ b _, h => noIcall_of_inames (c := b) h
  | .icall .., h => by simp [inames] at h

/-- What the cleanup needs of the callee, from what decryption's cleanup
needs of its code. -/
theorem dec_side (v : Backend) (c : CrtImpl) : calleeSide (decCode v c) 3568 = true := by
  obtain ⟨hs, ht, hm, -⟩ := of_scrubFSide (Proof.RsaPkcs1Enc.X86.Scrub.decrypt_scrub v c)
  have hi : inames (decCode v c) = [] := by
    simp only [tablesCall, List.all_eq_true] at ht
    match e : inames (decCode v c), ht with
    | [], _ => rfl
    | f :: _, ht => exact absurd (of_decide_eq_true (ht f (by simp))) (by simp [tableFns])
  simp only [calleeSide, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hs, (calleeOk_iff _).mpr ⟨noIcall_of_inames hi, hm⟩⟩

theorem dec_stack (v : Backend) (c : CrtImpl) : stackUse (decCode v c) ≤ 3568 :=
  (of_scrubFSide (Proof.RsaPkcs1Enc.X86.Scrub.decrypt_scrub v c)).1

theorem front_fill (v : Backend) (c : CrtImpl) :
    FillB frontStub (Impl.RsaPkcs1Enc.X86.Front.code (bodyName v c) (decCode v c)) := by
  have hd := dec_side v c
  unfold frontStub Impl.RsaPkcs1Enc.X86.Front.code Impl.RsaPkcs1Enc.X86.Front.body
  fillB_calls

/-- `scrubFSide` of the function, whatever the implementations. -/
theorem front_scrub (v : Backend) (c : CrtImpl) :
    scrubFSide (Impl.RsaPkcs1Enc.X86.Front.code (bodyName v c) (decCode v c)) [] 3732 = true :=
  scrubFSide_of_fillB (front_fill v c) front_side

/-- The postcondition reads the memory on return only in `out` and `msg_len`. -/
theorem front_postOut (stack : Nat) :
    PostOut (Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract abi stack)
      (Spec.RsaPkcs1Enc.decryptPrecomputedSig.retBits 32) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain fun
    | [out, outLen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaPkcs1Enc.decryptPrecomputedSig, Spec.RsaPkcs1Enc.decryptSig, List.cons_append,
        List.nil_append, Sig.bufs, List.mem_cons, forall_eq_or_imp, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop)
        [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e := bytesAt_of hb.1 (hp.2.1 ▸ toNat_sw_le abi ScrubAbi.plain outLen)
      have el := wordsAt_of (n := 1) hb.2.1
      revert h
      generalize Spec.RsaPkcs1Enc.decrypt _ _ _ _ _ _ _ _ _ = o
      cases o <;> simp only [Spec.RsaPkcs1Enc.writtenMsgFront, e, el] <;> exact id

/-- `vg_rsa_pkcs1_decrypt_precomputed_front` over `v` and `c`, before its
cleanup. -/
def frontPlain (v : Backend) (c : CrtImpl) : Unscrubbed Spec.RsaPkcs1Enc.decryptPrecomputedFrontApi target where
  code := Impl.RsaPkcs1Enc.X86.Front.code (bodyName v c) (decCode v c)
  contract := specF
  verified := front_verified (Proof.RsaPkcs1Enc.X86.Dec.decryptPrecomputed_verified v c)
    (Proof.RsaPkcs1Enc.X86.Dec.codeP_noSp v c crtPBaseline) (dec_stack v c)
  spSafe := Proof.Rsa.X86.PrivChecked.noSp_allStack (code_noSp (Proof.RsaPkcs1Enc.X86.Dec.codeP_noSp v c crtPBaseline))

/-- `Spec.RsaPkcs1Enc.decryptPrecomputedFrontApi`'s function as emitted over
`v` and `c` meets its contract in constant time and returns without secret
residue. -/
theorem front_scrubbed (v : Backend) (c : CrtImpl) :
    VerifiedScrubbed target (Impl.RsaPkcs1Enc.X86.Fn.decryptPrecomputedFront (bodyName v c) (decCode v c))
      specF 32 :=
  verifiedScrubbedAll (frontPlain v c) (front_postOut _) (hs := front_scrub v c)

theorem front_scrubbed_spSafe (v : Backend) (c : CrtImpl) :
    (Impl.RsaPkcs1Enc.X86.Fn.decryptPrecomputedFront (bodyName v c) (decCode v c)).all
      (fun i => !isa.writesSp i) = true :=
  scrubAll_spSafe (frontPlain v c).spSafe

end VG.Proof.RsaPkcs1Enc.X86.Front
