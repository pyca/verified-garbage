module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesOcb.Arm.Frame
public import VerifiedGarbage.Proof.AesOcb.Arm.Init
import VerifiedGarbage.Proof.AesOcb.Scratch
import VerifiedGarbage.Proof.AesGcm.Arm.Scrub
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.AesOcb.Arm.Frame
meta import VerifiedGarbage.Proof.AesOcb.Arm.Init
meta import VerifiedGarbage.Proof.AesOcb.Scratch
meta import VerifiedGarbage.Proof.AesGcm.Arm.Scrub
meta import VerifiedGarbage.Proof.Aes.ScrubLocal
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-OCB on ARMv7, without secret residue

`vg_aes_ocb_init` (AES-GCM's `init` code, `Proof/AesOcb/Arm/Init.lean`),
`vg_aes_ocb_seal` and `vg_aes_ocb_open` keep their working space in a frame
within the stack their contracts reserve and make no indirect call
(evaluated by `lit_decide`), and their postconditions read the memory on
return only within their buffers (`Arm.Scrub.PostOut`, as on PPC64LE,
`Proof/AesOcb/PPC64LE/Scrub.lean`). Each is registered followed by a wipe of
that stack and by instructions that set the registers a callee may change,
but the result, and the flags to constants (`Arm.Scrub.scrubRegF`).

That stack is a frame of the model (`Arm.Scrub.FrameOk`): the 2568 and 2600
bytes the proofs are stated with are not, and the functions are registered
with 2576 and 2608 (`Arm.Scrub.Verified.stack_le`), whose preconditions the
same states as before satisfy.
-/

@[expose] public section

namespace VG.Proof.AesOcb.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Aes.ScrubLocal VG.Impl.AesOcb.Arm

theorem len_le (x : BitVec 64) : (BitVec.setWidth 32 x).toNat ≤ x.toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_le _ _

/-! ## Postconditions -/

theorem initOut (stack : Nat) :
    PostOut (Spec.Ocb.initContract Arm.abi stack) (Spec.Ocb.initSig.retBits 32) :=
  Proof.AesGcm.Arm.Scrub.postOut_of_local_pre (leak := none) ScrubAbi.plain (Proof.AesOcb.initPostOut_local _)

theorem sealOut (stack : Nat) :
    PostOut (Spec.Ocb.sealContract Arm.abi stack) (Spec.Ocb.sealSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ocb.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr,
        ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32]
        (Spec.Ocb.sealPost 32) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr,
        ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32]
        (Spec.Ocb.sealPost 32) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ocb.sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [h key hk, bytesAt_of0 hb.2.2.2.1 (len_le _), bytesAt_of0 hb.2.2.2.2 (len_le _)]

theorem openOut (stack : Nat) :
    PostOut (Spec.Ocb.openContract Arm.abi stack) (Spec.Ocb.openSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ocb.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr,
        ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32]
        (Spec.Ocb.openPost 32) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr,
        ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32]
        (Spec.Ocb.openPost 32) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ocb.openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.1 (len_le _)]
      exact h key hk

/-! ## The code: its frames, and no indirect call -/

theorem frameOk_2576 : FrameOk 2576 := by decide
theorem frameOk_2608 : FrameOk 2608 := by decide

theorem initSat : ∃ s, (Spec.Ocb.initContract Arm.abi 2576).pre s :=
  Proof.AesGcm.Arm.Scrub.initSat

theorem sealSat : ∃ s, (Proof.AesOcb.sealRoundsContract Arm.abi 2608).pre s := by
  implies_sat [Proof.AesOcb.sealRoundsContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Proof.AesOcb.sealRoundsPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Proof.AesOcb.Arm.sealFrameSat, Proof.AesOcb.Arm.sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Proof.AesOcb.Arm.sealFrameSat

theorem openSat : ∃ s, (Proof.AesOcb.openRoundsContract Arm.abi 2608).pre s := by
  implies_sat [Proof.AesOcb.openRoundsContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Proof.AesOcb.openRoundsPost,
    Spec.Ocb.openLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Proof.AesOcb.Arm.openFrameSat, Proof.AesOcb.Arm.sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using Proof.AesOcb.Arm.openFrameSat

theorem init_code :
    armStack (Impl.StackScratch.Arm.withRegScratch 2560 .r3 Impl.AesGcm.Arm.init) ≤ 2576 ∧
      noIcall (Impl.StackScratch.Arm.withRegScratch 2560 .r3 Impl.AesGcm.Arm.init) = true := by
  lit_decide

theorem seal_code :
    armStack (Impl.StackScratch.Arm.withStackScratch 2592 6 «seal») ≤ 2608 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratch 2592 6 «seal») = true := by
  lit_decide

theorem open_code :
    armStack (Impl.StackScratch.Arm.withStackScratch 2592 6 «open») ≤ 2608 ∧
      noIcall (Impl.StackScratch.Arm.withStackScratch 2592 6 «open») = true := by
  lit_decide

/-! ## The registrations -/

/-- `vg_aes_ocb_init`. -/
def initReg : Registration Spec.Ocb.initApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withRegScratch 2560 .r3 Impl.AesGcm.Arm.init
      verified := (Verified.stack_le (by decide) Proof.AesOcb.Arm.init_framed initSat :
        Verified Arm.target _ (Spec.Ocb.initContract Arm.abi 2576)) }
    init_code.1 init_code.2 frameOk_2576 (initOut _) rfl

/-- `vg_aes_ocb_seal`. -/
def sealReg : Registration Spec.Ocb.sealApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 2592 6 «seal»
      verified := Proof.AesOcb.seal_keyed (Verified.stack_le (by decide) Proof.AesOcb.Arm.seal_framed sealSat :
        Verified Arm.target _ (Proof.AesOcb.sealRoundsContract Arm.abi 2608)) }
    seal_code.1 seal_code.2 frameOk_2608 (sealOut _) rfl

/-- `vg_aes_ocb_open`. -/
def openReg : Registration Spec.Ocb.openApi Arm.target :=
  scrubRegF {
      code := Impl.StackScratch.Arm.withStackScratch 2592 6 «open»
      verified := Proof.AesOcb.open_keyed (Verified.stack_le (by decide) Proof.AesOcb.Arm.open_framed openSat :
        Verified Arm.target _ (Proof.AesOcb.openRoundsContract Arm.abi 2608)) }
    open_code.1 open_code.2 frameOk_2608 (openOut _) rfl

end VG.Proof.AesOcb.Arm.Scrub
