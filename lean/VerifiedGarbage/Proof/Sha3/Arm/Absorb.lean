module

public import VerifiedGarbage.Proof.Sha3.Arm.Instances
public import VerifiedGarbage.Proof.Framework.Arm.StackScratch
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Sha3.PostOut
public import VerifiedGarbage.Proof.Sha3.Instances
public import VerifiedGarbage.Spec.Sha3.Instances
public import VerifiedGarbage.Impl.Sha3.Arm.Stream
import VerifiedGarbage.Proof.Sha3.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sha3.Arm.Instances
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratch
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import VerifiedGarbage.Proof.Sha3.PostOut
meta import VerifiedGarbage.Proof.Sha3.Instances
meta import VerifiedGarbage.Spec.Sha3.Instances
meta import VerifiedGarbage.Impl.Sha3.Arm.Stream
meta import VerifiedGarbage.Proof.Sha3.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SHA-3 and SHAKE on ARMv7, as emitted

`vg_<f>_update` (`Spec.Sha3.updateApi`) is `update` with its working space
`scratch` in a frame of 648 bytes on the stack, passed as its stack argument
(`Impl.Sha3.Arm.Instances.absorb`, `withStackScratch`): proven from
`update`'s proof (`Arm.Verified.stackScratch`, the contract with `scratch`
being `updateScratchContract` by `rfl`). Its cleanup (`Impl.Sha3.Arm.Fn`)
zeroes the 664 bytes of stack below the stack pointer that it and `update`
use, and clears the registers a callee may change, so that nothing is left
in the caller's memory.

The other functions keep their working space in a frame of their own too:
SHA-3's `finalize` 664 bytes, SHAKE's `finalize` 648 and `squeeze` 656
(`Impl.Sha3.Arm.Instances`), around calls of the sponge's `pad` and
`squeeze`, which use no stack (`Instances.pad_stack`, `squeeze_stack`) and
make no indirect call (by `lit_decide` on their literals). Their cleanup
zeroes that stack too, their postconditions reading the memory on return
only within their buffers (`Proof/Sha3/PostOut.lean`,
`Proof.Sha3.Instances.xofSqueezePostOut_local`). `Fn` below has the theorem
of each (`Arm.Scrub.verifiedScrubbedF`), which its registration binds.
-/

@[expose] public section

namespace VG.Proof.Sha3.Arm.Absorb

open VG.Arm VG.Arm.Scrub VG.Arm.FrameStack

-- The sponge's absorbing, which `update` calls, as a literal: `armStack` and
-- `noIcall` are checked by evaluation (`lit_decide`).
materialize_code streamAbsorb := Impl.Sha3.Arm.Stream.absorb

/-- A state satisfying `updateContract`'s precondition (with no data), with
664 bytes of stack. -/
def absorbSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r2 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 200⟩]

theorem frameOk664 : FrameOk 664 := by decide

theorem absorbOut (rate stack : Nat) :
    PostOut (Spec.Sha3.updateContract abi rate stack) (Spec.Sha3.updateSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha3.PostOut.updatePost_out rate _)

theorem absorbSat_sha3_224 : ∃ s, (Spec.Sha3.updateContract Arm.abi Spec.Sha3.hashSha3_224.rate 664).pre s := by
  implies_sat [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre, Spec.Sha3.updatePost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Spec.Sha3.hashSha3_224]
    [absorbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using absorbSat

theorem absorb_sha3_224 : Verified Arm.target (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_224.rate)
    (Spec.Sha3.updateContract Arm.abi Spec.Sha3.hashSha3_224.rate 664) :=
  Arm.Verified.stackScratch (sig := Spec.Sha3.updateSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.updatePre Spec.Sha3.hashSha3_224.rate Arm.abi.ptrBits)
    (post := Spec.Sha3.updatePost Spec.Sha3.hashSha3_224.rate Arm.abi.ptrBits) (wa := true) (stack := 16)
    (m := 0) (bytes := 648) Proof.Sha3.Arm.Instances.update_sha3_224 (by decide) (by decide) (by decide)
    (by decide) (Proof.Sha3.PostOut.updatePre_local _ _) (Proof.Sha3.PostOut.updatePost_local _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.updatePost_out _ _ vs mm m₁ m₂ r hl hb h)
    absorbSat_sha3_224

theorem absorb_sha3_224_armStack :
    armStack (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_224.rate) ≤ 664 := by lit_decide

theorem absorb_sha3_224_noIcall :
    noIcall (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_224.rate) = true := by lit_decide


theorem absorbSat_sha3_256 : ∃ s, (Spec.Sha3.updateContract Arm.abi Spec.Sha3.hashSha3_256.rate 664).pre s := by
  implies_sat [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre, Spec.Sha3.updatePost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Spec.Sha3.hashSha3_256]
    [absorbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using absorbSat

theorem absorb_sha3_256 : Verified Arm.target (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_256.rate)
    (Spec.Sha3.updateContract Arm.abi Spec.Sha3.hashSha3_256.rate 664) :=
  Arm.Verified.stackScratch (sig := Spec.Sha3.updateSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.updatePre Spec.Sha3.hashSha3_256.rate Arm.abi.ptrBits)
    (post := Spec.Sha3.updatePost Spec.Sha3.hashSha3_256.rate Arm.abi.ptrBits) (wa := true) (stack := 16)
    (m := 0) (bytes := 648) Proof.Sha3.Arm.Instances.update_sha3_256 (by decide) (by decide) (by decide)
    (by decide) (Proof.Sha3.PostOut.updatePre_local _ _) (Proof.Sha3.PostOut.updatePost_local _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.updatePost_out _ _ vs mm m₁ m₂ r hl hb h)
    absorbSat_sha3_256

theorem absorb_sha3_256_armStack :
    armStack (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_256.rate) ≤ 664 := by lit_decide

theorem absorb_sha3_256_noIcall :
    noIcall (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_256.rate) = true := by lit_decide


theorem absorbSat_sha3_384 : ∃ s, (Spec.Sha3.updateContract Arm.abi Spec.Sha3.hashSha3_384.rate 664).pre s := by
  implies_sat [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre, Spec.Sha3.updatePost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Spec.Sha3.hashSha3_384]
    [absorbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using absorbSat

theorem absorb_sha3_384 : Verified Arm.target (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_384.rate)
    (Spec.Sha3.updateContract Arm.abi Spec.Sha3.hashSha3_384.rate 664) :=
  Arm.Verified.stackScratch (sig := Spec.Sha3.updateSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.updatePre Spec.Sha3.hashSha3_384.rate Arm.abi.ptrBits)
    (post := Spec.Sha3.updatePost Spec.Sha3.hashSha3_384.rate Arm.abi.ptrBits) (wa := true) (stack := 16)
    (m := 0) (bytes := 648) Proof.Sha3.Arm.Instances.update_sha3_384 (by decide) (by decide) (by decide)
    (by decide) (Proof.Sha3.PostOut.updatePre_local _ _) (Proof.Sha3.PostOut.updatePost_local _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.updatePost_out _ _ vs mm m₁ m₂ r hl hb h)
    absorbSat_sha3_384

theorem absorb_sha3_384_armStack :
    armStack (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_384.rate) ≤ 664 := by lit_decide

theorem absorb_sha3_384_noIcall :
    noIcall (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_384.rate) = true := by lit_decide


theorem absorbSat_sha3_512 : ∃ s, (Spec.Sha3.updateContract Arm.abi Spec.Sha3.hashSha3_512.rate 664).pre s := by
  implies_sat [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre, Spec.Sha3.updatePost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Spec.Sha3.hashSha3_512]
    [absorbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using absorbSat

theorem absorb_sha3_512 : Verified Arm.target (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_512.rate)
    (Spec.Sha3.updateContract Arm.abi Spec.Sha3.hashSha3_512.rate 664) :=
  Arm.Verified.stackScratch (sig := Spec.Sha3.updateSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.updatePre Spec.Sha3.hashSha3_512.rate Arm.abi.ptrBits)
    (post := Spec.Sha3.updatePost Spec.Sha3.hashSha3_512.rate Arm.abi.ptrBits) (wa := true) (stack := 16)
    (m := 0) (bytes := 648) Proof.Sha3.Arm.Instances.update_sha3_512 (by decide) (by decide) (by decide)
    (by decide) (Proof.Sha3.PostOut.updatePre_local _ _) (Proof.Sha3.PostOut.updatePost_local _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.updatePost_out _ _ vs mm m₁ m₂ r hl hb h)
    absorbSat_sha3_512

theorem absorb_sha3_512_armStack :
    armStack (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_512.rate) ≤ 664 := by lit_decide

theorem absorb_sha3_512_noIcall :
    noIcall (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_512.rate) = true := by lit_decide


theorem absorbSat_shake128 : ∃ s, (Spec.Sha3.updateContract Arm.abi Spec.Sha3.xofShake128.rate 664).pre s := by
  implies_sat [Spec.Sha3.updateContract, Spec.Sha3.updateSig, Spec.Sha3.updatePre, Spec.Sha3.updatePost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Spec.Sha3.xofShake128]
    [absorbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using absorbSat

theorem absorb_shake128 : Verified Arm.target (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.xofShake128.rate)
    (Spec.Sha3.updateContract Arm.abi Spec.Sha3.xofShake128.rate 664) :=
  Arm.Verified.stackScratch (sig := Spec.Sha3.updateSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.updatePre Spec.Sha3.xofShake128.rate Arm.abi.ptrBits)
    (post := Spec.Sha3.updatePost Spec.Sha3.xofShake128.rate Arm.abi.ptrBits) (wa := true) (stack := 16)
    (m := 0) (bytes := 648) Proof.Sha3.Arm.Instances.update_shake128 (by decide) (by decide) (by decide)
    (by decide) (Proof.Sha3.PostOut.updatePre_local _ _) (Proof.Sha3.PostOut.updatePost_local _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.updatePost_out _ _ vs mm m₁ m₂ r hl hb h)
    absorbSat_shake128

theorem absorb_shake128_armStack :
    armStack (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.xofShake128.rate) ≤ 664 := by lit_decide

theorem absorb_shake128_noIcall :
    noIcall (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.xofShake128.rate) = true := by lit_decide


/-! ## `finalize` and `squeeze` -/

-- The sponge's padding and squeezing, which they call, as literals.
materialize_code streamPad := Impl.Sha3.Arm.Stream.pad
materialize_code streamSqueeze := Impl.Sha3.Arm.Stream.squeeze

theorem pad_noIcall : noIcall Impl.Sha3.Arm.Stream.pad = true := by lit_decide
theorem squeeze_noIcall : noIcall Impl.Sha3.Arm.Stream.squeeze = true := by lit_decide

theorem frameOk648 : FrameOk 648 := by decide
theorem frameOk656 : FrameOk 656 := by decide

theorem finalize_scrubArm (rate len : Nat) :
    armStack (Impl.Sha3.Arm.Instances.finalize rate len) ≤ 664 ∧
      noIcall (Impl.Sha3.Arm.Instances.finalize rate len) = true := by
  simp only [Impl.Sha3.Arm.Instances.finalize, armStack, noIcall, Proof.Sha3.Arm.Instances.pad_stack,
    Proof.Sha3.Arm.Instances.squeeze_stack, pad_noIcall, squeeze_noIcall]
  decide

theorem xofFinalize_scrubArm (rate : Nat) :
    armStack (Impl.Sha3.Arm.Instances.xofFinalize rate) ≤ 648 ∧
      noIcall (Impl.Sha3.Arm.Instances.xofFinalize rate) = true := by
  simp only [Impl.Sha3.Arm.Instances.xofFinalize, armStack, noIcall, Proof.Sha3.Arm.Instances.pad_stack,
    pad_noIcall]
  decide

theorem xofSqueeze_scrubArm (rate : Nat) :
    armStack (Impl.Sha3.Arm.Instances.xofSqueeze rate) ≤ 656 ∧
      noIcall (Impl.Sha3.Arm.Instances.xofSqueeze rate) = true := by
  simp only [Impl.Sha3.Arm.Instances.xofSqueeze, armStack, noIcall, Proof.Sha3.Arm.Instances.squeeze_stack,
    squeeze_noIcall]
  decide

theorem finalizeOut (H : Spec.Sha3.HashFn) (hlen : H.len < 2 ^ 64) :
    PostOut (Spec.Sha3.finalizeContract abi H 664) ((Spec.Sha3.finalizeSig H.len).retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha3.PostOut.finalizePost_out H _ hlen)

theorem xofFinalizeOut (X : Spec.Sha3.Xof) :
    PostOut (Spec.Sha3.xofFinalizeContract abi X 648) (Spec.Sha3.xofFinalizeSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha3.PostOut.xofFinalizePost_out X _)

theorem xofSqueezeOut (X : Spec.Sha3.Xof) :
    PostOut (Spec.Sha3.xofSqueezeContract abi X 656) (Spec.Sha3.xofSqueezeSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha3.Instances.xofSqueezePostOut_local _ X)

end VG.Proof.Sha3.Arm.Absorb

namespace VG.Proof.Sha3.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Proof.Sha3.Arm.Absorb

/-- `vg_sha3_224_update`. -/
theorem update_sha3_224 : VerifiedScrubbed target (Impl.Sha3.Arm.Fn.update Spec.Sha3.hashSha3_224.rate)
    (Spec.Sha3.updateContract abi Spec.Sha3.hashSha3_224.rate 664) 32 :=
  verifiedScrubbedF (api := Spec.Sha3.updateSha3_224Api)
    { code := Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_224.rate, verified := absorb_sha3_224 }
    (absorbOut _ _) (scrubSideF_of ⟨absorb_sha3_224_armStack, absorb_sha3_224_noIcall⟩ frameOk664 _)

/-- `vg_sha3_256_update`. -/
theorem update_sha3_256 : VerifiedScrubbed target (Impl.Sha3.Arm.Fn.update Spec.Sha3.hashSha3_256.rate)
    (Spec.Sha3.updateContract abi Spec.Sha3.hashSha3_256.rate 664) 32 :=
  verifiedScrubbedF (api := Spec.Sha3.updateSha3_256Api)
    { code := Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_256.rate, verified := absorb_sha3_256 }
    (absorbOut _ _) (scrubSideF_of ⟨absorb_sha3_256_armStack, absorb_sha3_256_noIcall⟩ frameOk664 _)

/-- `vg_sha3_384_update`. -/
theorem update_sha3_384 : VerifiedScrubbed target (Impl.Sha3.Arm.Fn.update Spec.Sha3.hashSha3_384.rate)
    (Spec.Sha3.updateContract abi Spec.Sha3.hashSha3_384.rate 664) 32 :=
  verifiedScrubbedF (api := Spec.Sha3.updateSha3_384Api)
    { code := Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_384.rate, verified := absorb_sha3_384 }
    (absorbOut _ _) (scrubSideF_of ⟨absorb_sha3_384_armStack, absorb_sha3_384_noIcall⟩ frameOk664 _)

/-- `vg_sha3_512_update`. -/
theorem update_sha3_512 : VerifiedScrubbed target (Impl.Sha3.Arm.Fn.update Spec.Sha3.hashSha3_512.rate)
    (Spec.Sha3.updateContract abi Spec.Sha3.hashSha3_512.rate 664) 32 :=
  verifiedScrubbedF (api := Spec.Sha3.updateSha3_512Api)
    { code := Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_512.rate, verified := absorb_sha3_512 }
    (absorbOut _ _) (scrubSideF_of ⟨absorb_sha3_512_armStack, absorb_sha3_512_noIcall⟩ frameOk664 _)

/-- `vg_shake128_update`. -/
theorem update_shake128 : VerifiedScrubbed target (Impl.Sha3.Arm.Fn.update Spec.Sha3.xofShake128.rate)
    (Spec.Sha3.updateContract abi Spec.Sha3.xofShake128.rate 664) 32 :=
  verifiedScrubbedF (api := Spec.Sha3.updateShake128Api)
    { code := Impl.Sha3.Arm.Instances.absorb Spec.Sha3.xofShake128.rate, verified := absorb_shake128 }
    (absorbOut _ _) (scrubSideF_of ⟨absorb_shake128_armStack, absorb_shake128_noIcall⟩ frameOk664 _)

/-- `vg_sha3_224_finalize`. -/
theorem finalize_sha3_224 : VerifiedScrubbed target
    (Impl.Sha3.Arm.Fn.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len)
    (Spec.Sha3.finalizeContract abi Spec.Sha3.hashSha3_224 664) 0 :=
  verifiedScrubbedF (api := Spec.Sha3.finalizeSha3_224Api)
    { code := Impl.Sha3.Arm.Instances.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len
      verified := Proof.Sha3.Arm.Instances.finalize_sha3_224 }
    (finalizeOut _ (by decide)) (scrubSideF_of (finalize_scrubArm _ _) frameOk664 _)

/-- `vg_sha3_256_finalize`. -/
theorem finalize_sha3_256 : VerifiedScrubbed target
    (Impl.Sha3.Arm.Fn.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len)
    (Spec.Sha3.finalizeContract abi Spec.Sha3.hashSha3_256 664) 0 :=
  verifiedScrubbedF (api := Spec.Sha3.finalizeSha3_256Api)
    { code := Impl.Sha3.Arm.Instances.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len
      verified := Proof.Sha3.Arm.Instances.finalize_sha3_256 }
    (finalizeOut _ (by decide)) (scrubSideF_of (finalize_scrubArm _ _) frameOk664 _)

/-- `vg_sha3_384_finalize`. -/
theorem finalize_sha3_384 : VerifiedScrubbed target
    (Impl.Sha3.Arm.Fn.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len)
    (Spec.Sha3.finalizeContract abi Spec.Sha3.hashSha3_384 664) 0 :=
  verifiedScrubbedF (api := Spec.Sha3.finalizeSha3_384Api)
    { code := Impl.Sha3.Arm.Instances.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len
      verified := Proof.Sha3.Arm.Instances.finalize_sha3_384 }
    (finalizeOut _ (by decide)) (scrubSideF_of (finalize_scrubArm _ _) frameOk664 _)

/-- `vg_sha3_512_finalize`. -/
theorem finalize_sha3_512 : VerifiedScrubbed target
    (Impl.Sha3.Arm.Fn.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len)
    (Spec.Sha3.finalizeContract abi Spec.Sha3.hashSha3_512 664) 0 :=
  verifiedScrubbedF (api := Spec.Sha3.finalizeSha3_512Api)
    { code := Impl.Sha3.Arm.Instances.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len
      verified := Proof.Sha3.Arm.Instances.finalize_sha3_512 }
    (finalizeOut _ (by decide)) (scrubSideF_of (finalize_scrubArm _ _) frameOk664 _)

/-- `vg_shake128_finalize`. -/
theorem finalize_shake128 : VerifiedScrubbed target (Impl.Sha3.Arm.Fn.xofFinalize Spec.Sha3.xofShake128.rate)
    (Spec.Sha3.xofFinalizeContract abi Spec.Sha3.xofShake128 648) 0 :=
  verifiedScrubbedF (api := Spec.Sha3.finalizeShake128Api)
    { code := Impl.Sha3.Arm.Instances.xofFinalize Spec.Sha3.xofShake128.rate
      verified := Proof.Sha3.Arm.Instances.finalize_shake128 }
    (xofFinalizeOut _) (scrubSideF_of (xofFinalize_scrubArm _) frameOk648 _)

/-- `vg_shake128_squeeze`. -/
theorem squeeze_shake128 : VerifiedScrubbed target (Impl.Sha3.Arm.Fn.xofSqueeze Spec.Sha3.xofShake128.rate)
    (Spec.Sha3.xofSqueezeContract abi Spec.Sha3.xofShake128 656) 32 :=
  verifiedScrubbedF (api := Spec.Sha3.squeezeShake128Api)
    { code := Impl.Sha3.Arm.Instances.xofSqueeze Spec.Sha3.xofShake128.rate
      verified := Proof.Sha3.Arm.Instances.squeeze_shake128 }
    (xofSqueezeOut _) (scrubSideF_of (xofSqueeze_scrubArm _) frameOk656 _)

/-- `vg_shake256_finalize`. -/
theorem finalize_shake256 : VerifiedScrubbed target (Impl.Sha3.Arm.Fn.xofFinalize Spec.Sha3.xofShake256.rate)
    (Spec.Sha3.xofFinalizeContract abi Spec.Sha3.xofShake256 648) 0 :=
  verifiedScrubbedF (api := Spec.Sha3.finalizeShake256Api)
    { code := Impl.Sha3.Arm.Instances.xofFinalize Spec.Sha3.xofShake256.rate
      verified := Proof.Sha3.Arm.Instances.finalize_shake256 }
    (xofFinalizeOut _) (scrubSideF_of (xofFinalize_scrubArm _) frameOk648 _)

/-- `vg_shake256_squeeze`. -/
theorem squeeze_shake256 : VerifiedScrubbed target (Impl.Sha3.Arm.Fn.xofSqueeze Spec.Sha3.xofShake256.rate)
    (Spec.Sha3.xofSqueezeContract abi Spec.Sha3.xofShake256 656) 32 :=
  verifiedScrubbedF (api := Spec.Sha3.squeezeShake256Api)
    { code := Impl.Sha3.Arm.Instances.xofSqueeze Spec.Sha3.xofShake256.rate
      verified := Proof.Sha3.Arm.Instances.squeeze_shake256 }
    (xofSqueezeOut _) (scrubSideF_of (xofSqueeze_scrubArm _) frameOk656 _)

end VG.Proof.Sha3.Arm.Fn
