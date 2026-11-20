module

public import VerifiedGarbage.Proof.Rsa.X86.ScrubOut
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Fn
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.RndVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecP.Verified
public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Fn
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Rsa.X86.ScrubOut
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Fn
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyInstances
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.RndVerified
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecP.Verified
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Fn
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# RSAES-PKCS1-v1_5 on x86 (32-bit), without secret residue

`vg_rsa_pkcs1_encrypt_random`, emitted with the zeroing of the stack its
contract reserves and the tail that clears the registers
(`Impl.RsaPkcs1Enc.X86.Fn.encryptRandom`), returns without secret residue
(`encryptRandom_scrubbed`). Its postcondition reads the memory on return only
within `out` and `tape`, given that `out` holds `n_len` bytes
(`X86.Scrub.PostOut`).

`vg_rsa_pkcs1_decrypt_precomputed`, generic over SHA-256's implementation
(`Backend`) and the private-key operation's (`CrtImpl`), is emitted with its
cleanup (`Impl.RsaPkcs1Enc.X86.Fn.decryptPrecomputed`), which returns without
secret residue whatever the implementations (`decryptPrecomputed_scrubbed`).
What its cleanup needs of its code holds of it with every implementation
(`decrypt_scrub`): its code with holes where each implementation's code
goes, of the stack each states (`holeStub`: 0 bytes for the compression
function, 20 for SHA-256's `update` and `finalize`, 96 for the public
precomputation and check), which the kernel evaluates once
(`decrypt_side`), and `FillB` (`decrypt_fill`). Its postcondition reads the
memory on return only within `out` and `msg_len`, given that `out` holds
`n_len` bytes.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.Rsa.X86.Scrub

/-! ## Postconditions -/

theorem writtenRandom_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} {r : BitVec 32} {v : Option (List Byte)}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (h : Spec.RsaPkcs1Enc.writtenRandom m₁ o n r v) :
    Spec.RsaPkcs1Enc.writtenRandom m₂ o n r v := by
  cases v <;> simpa only [Spec.RsaPkcs1Enc.writtenRandom, e] using h

theorem encryptRandomOut (stack : Nat) :
    PostOut (Spec.RsaPkcs1Enc.encryptRandomContract abi stack) (Spec.RsaPkcs1Enc.encryptRandomSig.retBits 32) :=
  postOut_of_local_pre (leak := some _) ScrubAbi.plain fun
    | [out, outLen, tape, _, _, _, _, _, _, _, _, _, _, _, _], m, m₁, m₂, r, _, hp, hb, h => by
      simp only [Spec.RsaPkcs1Enc.encryptRandomSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      change @Curry.apply (Mem → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ m at hp
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
      change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
      dsimp only [Curry.apply, ArgWord.ofRaw] at hp h ⊢
      have e' := bytesAt_of hb.1 (hp.2.1 ▸ toNat_sw_le abi ScrubAbi.plain outLen)
      rw [wordsAt_of hb.2.1]
      refine ⟨h.1, ?_⟩
      have h2 := h.2
      revert h2
      generalize (Spec.RsaPkcs1Enc.padSearch _ _).outcome = o
      match o with
      | .accepted _ => exact fun h2 hP => writtenRandom_of e' (h2 hP)
      | .entropy .. => simp only [e']; exact id
      | .exhausted => simp only [e']; exact id

/-! ## The function, with its cleanup -/

open VG.Proof.RsaPkcs1Sig.X86.Ver (baseline)

/-- `vg_rsa_pkcs1_encrypt_random`, with the baseline public-key operation and
its cleanup, returns without secret residue. -/
theorem encryptRandom_scrubbed :
    VerifiedScrubbed target
      (Impl.RsaPkcs1Enc.X86.Fn.encryptRandom Proof.RsaPkcs1Enc.X86.Rnd.encName (Proof.RsaPkcs1Enc.X86.Rnd.enc baseline))
      Proof.RsaPkcs1Enc.X86.Rnd.spec 32 :=
  verifiedScrubbedF (api := Spec.RsaPkcs1Enc.encryptRandomApi) {
      code := Impl.RsaPkcs1Enc.X86.Random.code Proof.RsaPkcs1Enc.X86.Rnd.encName
        (Proof.RsaPkcs1Enc.X86.Rnd.enc baseline)
      verified := Proof.RsaPkcs1Enc.X86.Rnd.code_verified Proof.RsaPkcs1Enc.X86.Rnd.encName baseline
      spSafe := Proof.RsaPkcs1Enc.X86.Rnd.code_sp Proof.RsaPkcs1Enc.X86.Rnd.encName baseline }
    (encryptRandomOut _)

/-! ## Decryption, whatever the implementations -/

open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCodeP crtPBaseline)

theorem writtenMsg_of {m₁ m₂ : Mem} {o l : Addr} {n : Nat} {r : BitVec 32} {v : Spec.Rsa.Outcome}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (el : Spec.Rsa.wordsAt m₂ l 1 = Spec.Rsa.wordsAt m₁ l 1)
    (h : Spec.RsaPkcs1Enc.writtenMsg m₁ o l n r v) : Spec.RsaPkcs1Enc.writtenMsg m₂ o l n r v := by
  cases v <;> simpa only [Spec.RsaPkcs1Enc.writtenMsg, e, el] using h

theorem decryptPrecomputedOut (stack : Nat) :
    PostOut (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stack)
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
      exact writtenMsg_of (bytesAt_of hb.1 (hp.2.1 ▸ toNat_sw_le abi ScrubAbi.plain outLen))
        (wordsAt_of hb.2.1) h

/-- `vg_rsa_pkcs1_decrypt_precomputed` with holes for SHA-256's compression
function (no stack), `update` and `finalize` (20 bytes each) and the
private-key operation's public precomputation and check (96 bytes each). -/
def decryptStub : Prog isa :=
  Impl.RsaPkcs1Enc.X86.Decrypt.code
    (Proof.Sha256.X86.Variants.fns "" "" (holeStub 0) (holeStub 20) (holeStub 20)) ""
    (Impl.Rsa.X86.PrivChecked.codeP crtPBaseline.name crtPBaseline.code "" (holeStub 96) "" (holeStub 96))
    Impl.RsaPkcs1Enc.X86.Decrypt.privArgsP

-- The stub as a literal, for the kernel's evaluation.
materialize_code decryptStub

theorem decrypt_side : scrubFSide decryptStub [] 3568 = true := by lit_decide

theorem decrypt_fill (v : Backend) (c : CrtImpl) (hm : calleeSide v.cmpC 0 = true)
    (hu : calleeSide v.stream.upd 20 = true) (hf : calleeSide v.stream.fin 20 = true)
    (hc : calleeSide c.pc 96 = true) (hd : calleeSide c.pd 96 = true) :
    FillB decryptStub (Proof.RsaPkcs1Enc.X86.Dec.decryptCodeP v c crtPBaseline) := by
  unfold decryptStub
  fillB_calls
  -- SHA-256's blocks of instructions, the same whatever its implementation:
  all_goals exact FillB.refl _

/-- `scrubFSide` of `vg_rsa_pkcs1_decrypt_precomputed`, whatever the
implementations of SHA-256 and the private-key operation. -/
theorem decrypt_scrub (v : Backend) (c : CrtImpl) :
    scrubFSide (Proof.RsaPkcs1Enc.X86.Dec.decryptCodeP v c crtPBaseline) [] 3568 = true :=
  scrubFSide_of_fillB (decrypt_fill v c (calleeSide_of_eq v.cmpStack v.cmpScrub)
    (calleeSide_of_le v.stream.updSU v.updScrub) (calleeSide_of_le v.stream.finSU v.finScrub)
    (calleeSide_of_le c.pcStack c.pcScrub) (calleeSide_of_le c.pdStack c.pdScrub)) decrypt_side

/-- `vg_rsa_pkcs1_decrypt_precomputed`, with its cleanup, returns without
secret residue, whatever the implementations `v` of SHA-256 and `c` of the
private-key operation. -/
theorem decryptPrecomputed_scrubbed (v : Backend) (c : CrtImpl) :
    VerifiedScrubbed target
      (Impl.RsaPkcs1Enc.X86.Fn.decryptPrecomputed v.F (Proof.RsaPkcs1Enc.X86.Dec.privNameP c)
        (privCodeP c crtPBaseline))
      Proof.RsaPkcs1Enc.X86.Dec.specP 32 :=
  verifiedScrubbedF (api := Spec.RsaPkcs1Enc.decryptPrecomputedApi)
    { code := Proof.RsaPkcs1Enc.X86.Dec.decryptCodeP v c crtPBaseline
      verified := Proof.RsaPkcs1Enc.X86.Dec.decryptPrecomputed_verified v c
      spSafe := Proof.RsaPkcs1Enc.X86.Dec.codeP_sp v c crtPBaseline }
    (decryptPrecomputedOut _) (hs := decrypt_scrub v c)

/-- `vg_rsa_pkcs1_decrypt_precomputed`, with its cleanup, writes `esp` only by its frames. -/
theorem decryptPrecomputed_spSafe (v : Backend) (c : CrtImpl) :
    (Impl.RsaPkcs1Enc.X86.Fn.decryptPrecomputed v.F (Proof.RsaPkcs1Enc.X86.Dec.privNameP c)
      (privCodeP c crtPBaseline)).all (fun i => !isa.writesSp i) = true :=
  scrubF_spSafe (Proof.RsaPkcs1Enc.X86.Dec.codeP_sp v c crtPBaseline)

end VG.Proof.RsaPkcs1Enc.X86.Scrub
