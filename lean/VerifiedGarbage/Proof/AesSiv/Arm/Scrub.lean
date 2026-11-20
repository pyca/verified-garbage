module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.AesSiv.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesSiv.Arm.Frame
public import VerifiedGarbage.Proof.AesSiv.Arm.Verified
import VerifiedGarbage.Proof.AesSiv.Scratch
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.AesSiv.Arm.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.AesSiv.Arm.Frame
meta import VerifiedGarbage.Proof.AesSiv.Arm.Verified
meta import VerifiedGarbage.Proof.AesSiv.Scratch
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-SIV on ARMv7, without secret residue

`vg_aes_siv_init`, `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` keep their
working space in a frame within the stack their contracts reserve and make
no indirect call (evaluated by `lit_decide`), and their postconditions read
the memory on return only within their buffers (`Arm.Scrub.PostOut`, as on
PPC64LE, `Proof/AesSiv/PPC64LE/Scrub.lean`). Each is emitted followed by
a wipe of that stack and by instructions that set the registers a callee may
change, but the result, and the flags to constants (`Impl.AesSiv.Arm.Fn`), and `Fn` below states
that it returns without secret residue (`Arm.Scrub.verifiedScrubbedF`), which
is what its registration binds.

That stack is a frame of the model (`Arm.Scrub.FrameOk`): the 2568 bytes
`init`'s proof is stated with are not, and it is stated with 2576
(`Arm.Scrub.Verified.stack_le`), whose precondition the same state as
before satisfies.
-/

@[expose] public section

namespace VG.Proof.AesSiv.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Impl.AesSiv.Arm

/-! ## Postconditions -/

theorem initOut (stack : Nat) :
    PostOut (Spec.Siv.initContract Arm.abi stack) (Spec.Siv.initSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.AesSiv.initPostOut_local _)

theorem encryptOut (stack : Nat) :
    PostOut (Spec.Siv.encryptContract Arm.abi stack) (Spec.Siv.encryptSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rd, ads, cnt, data, len, siv], _ =>
      simp only [Spec.Siv.encryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr,
        ArgWord.int 32, ArgWord.addr] (Spec.Siv.encryptPost 32) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr,
        ArgWord.int 32, ArgWord.addr] (Spec.Siv.encryptPost 32) _ m m₂ r
      dsimp only [Curry.apply, Spec.Siv.encryptPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [h key hk, Proof.AesSiv.bytesAt_congr fun i hi => Proof.AesSiv.agree_of hb.2.2 i (by omega),
        Proof.AesSiv.bytesAt_congr fun i hi => Proof.AesSiv.agree_of hb.2.1 i (by
          rw [BitVec.toNat_setWidth] at hi; exact Nat.lt_of_lt_of_le hi (Nat.mod_le _ _))]

theorem decryptOut (stack : Nat) :
    PostOut (Spec.Siv.decryptContract Arm.abi stack) (Spec.Siv.decryptSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rd, ads, cnt, data, len, siv], _ =>
      simp only [Spec.Siv.decryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr,
        ArgWord.int 32, ArgWord.addr] (Spec.Siv.decryptPost 32) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr,
        ArgWord.int 32, ArgWord.addr] (Spec.Siv.decryptPost 32) _ m m₂ r
      dsimp only [Curry.apply, Spec.Siv.decryptPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      have e := Proof.AesSiv.bytesAt_congr (n := (BitVec.setWidth 32 len).toNat) fun i hi =>
        Proof.AesSiv.agree_of hb.2.1 i (by
          rw [BitVec.toNat_setWidth] at hi; exact Nat.lt_of_lt_of_le hi (Nat.mod_le _ _))
      rw [e]
      exact h key hk

/-! ## The code: its frames, and no indirect call -/

theorem frameOk_2576 : FrameOk 2576 := by decide
theorem frameOk_2624 : FrameOk 2624 := by decide

theorem initSat : ∃ s, (Spec.Siv.initContract Arm.abi 2576).pre s := by
  implies_sat [Spec.Siv.initContract, Spec.Siv.initSig, Spec.Siv.initPre, Spec.Siv.initPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Proof.AesSiv.Arm.initFrameSat, Proof.AesSiv.Arm.sivSat] using Proof.AesSiv.Arm.initFrameSat

theorem init_code :
    CodeOk (Impl.StackScratch.Arm.withRegScratch 2560 .r3 init) 2576 := by
  lit_decide

theorem encrypt_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 2608 3 encrypt) 2624 := by
  lit_decide

theorem decrypt_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 2608 3 decrypt) 2624 := by
  lit_decide

end VG.Proof.AesSiv.Arm.Scrub

namespace VG.Proof.AesSiv.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Impl.AesSiv.Arm

/-- `vg_aes_siv_init`. -/
theorem init : VerifiedScrubbed target Impl.AesSiv.Arm.Fn.init (Spec.Siv.initContract abi 2576) 0 :=
  verifiedScrubbedF (api := Spec.Siv.initApi)
    { code := Impl.StackScratch.Arm.withRegScratch 2560 .r3 Impl.AesSiv.Arm.init
      verified := (Verified.stack_le (by decide) Proof.AesSiv.Arm.init_framed Scrub.initSat :
        Verified Arm.target _ (Spec.Siv.initContract Arm.abi 2576)) }
    (Scrub.initOut _) (scrubSideF_of Scrub.init_code Scrub.frameOk_2576 _)

/-- `vg_aes_siv_encrypt`. -/
theorem encrypt : VerifiedScrubbed target Impl.AesSiv.Arm.Fn.encrypt (Spec.Siv.encryptContract abi 2624) 0 :=
  verifiedScrubbedF (api := Spec.Siv.encryptApi)
    { code := Impl.StackScratch.Arm.withStackScratch 2608 3 Impl.AesSiv.Arm.encrypt
      verified := Proof.AesSiv.encrypt_keyed Proof.AesSiv.Arm.encrypt_framed }
    (Scrub.encryptOut _) (scrubSideF_of Scrub.encrypt_code Scrub.frameOk_2624 _)

/-- `vg_aes_siv_decrypt`. -/
theorem decrypt : VerifiedScrubbed target Impl.AesSiv.Arm.Fn.decrypt (Spec.Siv.decryptContract abi 2624) 32 :=
  verifiedScrubbedF (api := Spec.Siv.decryptApi)
    { code := Impl.StackScratch.Arm.withStackScratch 2608 3 Impl.AesSiv.Arm.decrypt
      verified := Proof.AesSiv.decrypt_keyed Proof.AesSiv.Arm.decrypt_framed }
    (Scrub.decryptOut _) (scrubSideF_of Scrub.decrypt_code Scrub.frameOk_2624 _)

end VG.Proof.AesSiv.Arm.Fn
