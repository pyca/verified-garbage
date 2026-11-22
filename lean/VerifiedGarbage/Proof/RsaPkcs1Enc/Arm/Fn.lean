module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubOut
public import VerifiedGarbage.Proof.Rsa.Arm.ScrubCode
public import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.DecPrecomputed
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Arm.RndVerified
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# RSAES-PKCS1-v1_5 on ARMv7, as emitted

`Impl.RsaPkcs1Enc.Arm.Fn` has each function with its cleanup; `Fn` below
has the theorem of each, for any implementation of the private CRT's
interface: it meets its contract in constant time and returns without
secret residue (`VerifiedScrubbed`), which is what its registration binds
(`Arm.Scrub.verifiedScrubbedAll`).

Their frames use 3640 and 2312 bytes, which are not frame sizes of the model
(`FrameOk`), so their contracts reserve the next ones, 3648 and 2320
(`Arm.Scrub.Verified.stack_le`, with the witnesses of their preconditions
again). What the cleanup needs of the code (`CodeOk`: its frames within
those bytes, no indirect call) is proven once for any implementation, from
what each states of its own code (`Proof/Rsa/Arm/ScrubCode.lean`), with the
code around the call by `lit_decide`. Their postconditions read the memory
on return only within `out`, decryption's `msg_len` and encryption's `tape`,
as on PPC64LE (`Proof/RsaPkcs1Enc/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.Arm.Scrub

open VG.Arm VG.Arm.Scrub VG.Proof.Rsa.Arm.Scrub
open VG.Proof.Rsa.Arm (CrtImpl privCodeP)

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

theorem writtenMsg_of {m₁ m₂ : Mem} {o l : Addr} {n : Nat} {r : BitVec 32} {v : Spec.Rsa.Outcome}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (el : Spec.Rsa.wordsAt m₂ l 1 = Spec.Rsa.wordsAt m₁ l 1)
    (h : Spec.RsaPkcs1Enc.writtenMsg m₁ o l n r v) : Spec.RsaPkcs1Enc.writtenMsg m₂ o l n r v := by
  cases v <;> simpa only [Spec.RsaPkcs1Enc.writtenMsg, e, el] using h

theorem decryptPrecomputedOut (stack : Nat) :
    PostOut (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi stack)
      (Spec.RsaPkcs1Enc.decryptPrecomputedSig.retBits 32) :=
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
      exact writtenMsg_of (bytesAt_of hb.1 (hp.2.1 ▸ toNat_sw_le abi ScrubAbi.plain outLen))
        (wordsAt_of hb.2.1) h

/-! ## The stacks, at frame sizes of the model -/

theorem decryptSat : ∃ s, (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi 3648).pre s := by
  open Proof.RsaPkcs1Enc.Arm.Dec in
  have p11 : BitVec.setWidth 64 (stackArg preState 7) = 0x4200 := by decide
  have p13 : BitVec.setWidth 64 (stackArg preState 9) = 0x4300 := by decide
  have p23 : BitVec.setWidth 64 (stackArg preState 19) = 0x4800 := by decide
  have l4 : (stackArg preState 0).toNat = 64 := by decide
  have l12 : (stackArg preState 8).toNat = 32 := by decide
  have l14 : (stackArg preState 10).toNat = 32 := by decide
  have l24 : (stackArg preState 20).toNat = 24 := by decide
  refine ⟨preState, ?_⟩
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedContract, Spec.RsaPkcs1Enc.decryptPrecomputedSig,
    Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  sig_and_intros
  rotate_right
  · rw [show BitVec.setWidth 64 (8192 : BitVec 32) = (0x2000 : Addr) by decide, p11, p13, p23, l4, l12, l14, l24]
    exact preState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (simp only [Spec.Rsa.lenValid]; decide)

theorem decryptVerified (v : CrtImpl) :
    Verified target (Proof.RsaPkcs1Enc.Arm.Dec.decryptCodeP v) (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi 3648) :=
  Verified.stack_le (by decide) (Proof.RsaPkcs1Enc.Arm.Dec.decryptPrecomputed_verified v) decryptSat

theorem randomSat : ∃ s, (Spec.RsaPkcs1Enc.encryptRandomContract abi 2320).pre s := by
  open Proof.RsaPkcs1Enc.Arm.Rnd in
  sig_implies_sat [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi,
    argRegs, reduceClassify, Loc.val, State.addr]
    [satState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid, Spec.Rsa.scratchWords,
      Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, Spec.RsaPkcs1Enc.padEntropy] using satState

theorem randomVerified (encName : String) (c : Proof.RsaPkcs1Sig.Arm.PdImpl) :
    Verified target (Impl.RsaPkcs1Enc.Arm.Random.code encName (Impl.RsaPkcs1Enc.Arm.Precomputed.code c.name c.code))
      (Spec.RsaPkcs1Enc.encryptRandomContract abi 2320) :=
  Verified.stack_le (by decide) (Proof.RsaPkcs1Enc.Arm.Rnd.code_verified encName c) randomSat

/-! ## What the cleanup needs of the code -/

theorem decRest_ok : CodeOk (.seq (.block Impl.RsaPkcs1Enc.Arm.Decrypt.dZero) (.seq Impl.Bignum.Arm.maskBytes
    (.seq (.block Impl.RsaPkcs1Enc.Arm.Decrypt.dCopy) (.seq Impl.Bignum.Arm.copyBytes
    (.seq (Impl.RsaPkcs1Enc.Arm.Decrypt.hashD Proof.RsaPkcs1Enc.Arm.decFns)
    (.seq (Impl.RsaPkcs1Enc.Arm.Decrypt.kdkMac Proof.RsaPkcs1Enc.Arm.decFns)
    (.seq (Impl.RsaPkcs1Enc.Arm.Decrypt.clLoop Proof.RsaPkcs1Enc.Arm.decFns)
    (.seq (Impl.RsaPkcs1Enc.Arm.Decrypt.amLoop Proof.RsaPkcs1Enc.Arm.decFns)
    (.seq Impl.RsaPkcs1Enc.Arm.Decrypt.alPart Impl.RsaPkcs1Enc.Arm.Decrypt.selPart)))))))) : Prog isa) 3488 := by
  lit_decide

/-- Decryption's code, over `v`. -/
theorem decrypt_ok (v : CrtImpl) : CodeOk (Proof.RsaPkcs1Enc.Arm.Dec.decryptCodeP v) 3648 :=
  (wrap_codeOk (n := 3488) (F := 96)
    (CodeOk.seq (CodeOk.zero (CodeOk.block _)) (CodeOk.seq (CodeOk.call (privCodeP_ok v)) decRest_ok))).mono
    (by decide)

/-- `vg_rsa_pkcs1_encrypt_precomputed`'s code, over the public operation `pd`. -/
theorem precomputed_ok {pdName : String} {pd : Prog isa} (h : CodeOk pd 56) :
    CodeOk (Impl.RsaPkcs1Enc.Arm.Precomputed.code pdName pd) 1168 := by
  refine wrap_codeOk (n := 56) (F := 1056) (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.seq ?_
    (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.seq (CodeOk.call h) ?_))))))))
  all_goals lit_decide

/-- Encryption from a random tape's code, over the call `enc`. -/
theorem random_ok {encName : String} {enc : Prog isa} (h : CodeOk enc 1168) :
    CodeOk (Impl.RsaPkcs1Enc.Arm.Random.code encName enc) 2320 := by
  refine (wrap_codeOk (n := 1168) (F := 1088) (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.ite
    (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.seq ?_ (CodeOk.seq (CodeOk.call h) ?_)))) ?_))))).mono (by decide)
  all_goals lit_decide

theorem frameOk_3648 : FrameOk 3648 := by decide

theorem frameOk_2320 : FrameOk 2320 := by decide

end VG.Proof.RsaPkcs1Enc.Arm.Scrub

namespace VG.Proof.RsaPkcs1Enc.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Proof.Rsa.Arm VG.Proof.RsaPkcs1Enc.Arm.Scrub

/-- `vg_rsa_pkcs1_decrypt_precomputed`, calling `vg_rsa_private_checked_precomputed` over `v`. -/
theorem decryptPrecomputed (v : CrtImpl) :
    VerifiedScrubbed target
      (Impl.RsaPkcs1Enc.Arm.Fn.decryptPrecomputed Proof.RsaPkcs1Enc.Arm.decFns (privNameP v) (privCodeP v))
      (Spec.RsaPkcs1Enc.decryptPrecomputedContract abi 3648) 32 :=
  verifiedScrubbedAll (api := Spec.RsaPkcs1Enc.decryptPrecomputedApi)
    { code := Proof.RsaPkcs1Enc.Arm.Dec.decryptCodeP v, verified := decryptVerified v }
    (decryptPrecomputedOut _) (scrubSideF_of (decrypt_ok v) frameOk_3648 _)

/-- `vg_rsa_pkcs1_encrypt_random`, calling `vg_rsa_pkcs1_encrypt_precomputed`
over `v`'s public operation, by the name `encName`. -/
theorem encryptRandom (encName : String) (v : CrtImpl) :
    VerifiedScrubbed target
      (Impl.RsaPkcs1Enc.Arm.Fn.encryptRandom encName
        (Impl.RsaPkcs1Enc.Arm.Precomputed.code (pdOfCrt v).name (pdOfCrt v).code))
      (Spec.RsaPkcs1Enc.encryptRandomContract abi 2320) 32 :=
  verifiedScrubbedAll (api := Spec.RsaPkcs1Enc.encryptRandomApi)
    { code := Impl.RsaPkcs1Enc.Arm.Random.code encName
        (Impl.RsaPkcs1Enc.Arm.Precomputed.code (pdOfCrt v).name (pdOfCrt v).code)
      verified := randomVerified encName (pdOfCrt v) }
    (encryptRandomOut _) (scrubSideF_of (random_ok (precomputed_ok v.pdOk)) frameOk_2320 _)

end VG.Proof.RsaPkcs1Enc.Arm.Fn
