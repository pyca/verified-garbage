module

public import VerifiedGarbage.Proof.Sha3.Arm.Instances
public import VerifiedGarbage.Proof.Framework.Arm.StackScratch
public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha3.PostOut
public import VerifiedGarbage.Spec.Sha3.Instances
public import VerifiedGarbage.Impl.Sha3.Arm.Stream
import VerifiedGarbage.Proof.Sha3.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sha3.Arm.Instances
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratch
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Sha3.PostOut
meta import VerifiedGarbage.Spec.Sha3.Instances
meta import VerifiedGarbage.Impl.Sha3.Arm.Stream
meta import VerifiedGarbage.Proof.Sha3.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SHA-3's absorb on ARMv7

`vg_<f>_absorb` (`Spec.Sha3.absorbApi`) is `update` with its working space
`scratch` in a frame of 648 bytes on the stack, passed as its stack argument
(`Impl.Sha3.Arm.Instances.absorb`, `withStackScratch`): proven from
`update`'s proof (`Arm.Verified.stackScratch`, the contract with `scratch`
being `updateContract` by `rfl`), and returning without secret residue
(`Arm.Scrub.scrubRegF`, which zeroes the 664 bytes of stack below the stack
pointer that it and `update` use, and clears the registers a callee may
change), so that nothing is left in the caller's memory.
-/

@[expose] public section

namespace VG.Proof.Sha3.Arm.Absorb

open VG.Arm VG.Arm.Scrub VG.Arm.FrameStack

-- The sponge's absorbing, which `update` calls, as a literal: `armStack` and
-- `noIcall` are checked by evaluation (`lit_decide`).
materialize_code streamAbsorb := Impl.Sha3.Arm.Stream.absorb

/-- A state satisfying `absorbContract`'s precondition (with no data), with
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
    PostOut (Spec.Sha3.absorbContract abi rate stack) (Spec.Sha3.absorbSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha3.PostOut.absorbPost_out rate _)

theorem absorbSat_sha3_224 : ∃ s, (Spec.Sha3.absorbContract Arm.abi Spec.Sha3.hashSha3_224.rate 664).pre s := by
  implies_sat [Spec.Sha3.absorbContract, Spec.Sha3.absorbSig, Spec.Sha3.absorbPre, Spec.Sha3.absorbPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Spec.Sha3.hashSha3_224]
    [absorbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using absorbSat

theorem absorb_sha3_224 : Verified Arm.target (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_224.rate)
    (Spec.Sha3.absorbContract Arm.abi Spec.Sha3.hashSha3_224.rate 664) :=
  Arm.Verified.stackScratch (sig := Spec.Sha3.absorbSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.absorbPre Spec.Sha3.hashSha3_224.rate Arm.abi.ptrBits)
    (post := Spec.Sha3.absorbPost Spec.Sha3.hashSha3_224.rate Arm.abi.ptrBits) (wa := true) (stack := 16)
    (m := 0) (bytes := 648) Proof.Sha3.Arm.Instances.update_sha3_224 (by decide) (by decide) (by decide)
    (by decide) (Proof.Sha3.PostOut.absorbPre_local _ _) (Proof.Sha3.PostOut.absorbPost_local _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.absorbPost_out _ _ vs mm m₁ m₂ r hl hb h)
    absorbSat_sha3_224

theorem absorb_sha3_224_armStack :
    armStack (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_224.rate) ≤ 664 := by lit_decide

theorem absorb_sha3_224_noIcall :
    noIcall (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_224.rate) = true := by lit_decide

/-- `vg_sha3_224_absorb`. -/
def absorbSha3_224Reg : Registration Spec.Sha3.absorbSha3_224Api target :=
  scrubRegF {
      code := Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_224.rate
      verified := absorb_sha3_224 }
    absorb_sha3_224_armStack absorb_sha3_224_noIcall frameOk664 (absorbOut _ _) rfl

theorem absorbSat_sha3_256 : ∃ s, (Spec.Sha3.absorbContract Arm.abi Spec.Sha3.hashSha3_256.rate 664).pre s := by
  implies_sat [Spec.Sha3.absorbContract, Spec.Sha3.absorbSig, Spec.Sha3.absorbPre, Spec.Sha3.absorbPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Spec.Sha3.hashSha3_256]
    [absorbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using absorbSat

theorem absorb_sha3_256 : Verified Arm.target (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_256.rate)
    (Spec.Sha3.absorbContract Arm.abi Spec.Sha3.hashSha3_256.rate 664) :=
  Arm.Verified.stackScratch (sig := Spec.Sha3.absorbSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.absorbPre Spec.Sha3.hashSha3_256.rate Arm.abi.ptrBits)
    (post := Spec.Sha3.absorbPost Spec.Sha3.hashSha3_256.rate Arm.abi.ptrBits) (wa := true) (stack := 16)
    (m := 0) (bytes := 648) Proof.Sha3.Arm.Instances.update_sha3_256 (by decide) (by decide) (by decide)
    (by decide) (Proof.Sha3.PostOut.absorbPre_local _ _) (Proof.Sha3.PostOut.absorbPost_local _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.absorbPost_out _ _ vs mm m₁ m₂ r hl hb h)
    absorbSat_sha3_256

theorem absorb_sha3_256_armStack :
    armStack (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_256.rate) ≤ 664 := by lit_decide

theorem absorb_sha3_256_noIcall :
    noIcall (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_256.rate) = true := by lit_decide

/-- `vg_sha3_256_absorb`. -/
def absorbSha3_256Reg : Registration Spec.Sha3.absorbSha3_256Api target :=
  scrubRegF {
      code := Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_256.rate
      verified := absorb_sha3_256 }
    absorb_sha3_256_armStack absorb_sha3_256_noIcall frameOk664 (absorbOut _ _) rfl

theorem absorbSat_sha3_384 : ∃ s, (Spec.Sha3.absorbContract Arm.abi Spec.Sha3.hashSha3_384.rate 664).pre s := by
  implies_sat [Spec.Sha3.absorbContract, Spec.Sha3.absorbSig, Spec.Sha3.absorbPre, Spec.Sha3.absorbPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Spec.Sha3.hashSha3_384]
    [absorbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using absorbSat

theorem absorb_sha3_384 : Verified Arm.target (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_384.rate)
    (Spec.Sha3.absorbContract Arm.abi Spec.Sha3.hashSha3_384.rate 664) :=
  Arm.Verified.stackScratch (sig := Spec.Sha3.absorbSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.absorbPre Spec.Sha3.hashSha3_384.rate Arm.abi.ptrBits)
    (post := Spec.Sha3.absorbPost Spec.Sha3.hashSha3_384.rate Arm.abi.ptrBits) (wa := true) (stack := 16)
    (m := 0) (bytes := 648) Proof.Sha3.Arm.Instances.update_sha3_384 (by decide) (by decide) (by decide)
    (by decide) (Proof.Sha3.PostOut.absorbPre_local _ _) (Proof.Sha3.PostOut.absorbPost_local _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.absorbPost_out _ _ vs mm m₁ m₂ r hl hb h)
    absorbSat_sha3_384

theorem absorb_sha3_384_armStack :
    armStack (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_384.rate) ≤ 664 := by lit_decide

theorem absorb_sha3_384_noIcall :
    noIcall (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_384.rate) = true := by lit_decide

/-- `vg_sha3_384_absorb`. -/
def absorbSha3_384Reg : Registration Spec.Sha3.absorbSha3_384Api target :=
  scrubRegF {
      code := Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_384.rate
      verified := absorb_sha3_384 }
    absorb_sha3_384_armStack absorb_sha3_384_noIcall frameOk664 (absorbOut _ _) rfl

theorem absorbSat_sha3_512 : ∃ s, (Spec.Sha3.absorbContract Arm.abi Spec.Sha3.hashSha3_512.rate 664).pre s := by
  implies_sat [Spec.Sha3.absorbContract, Spec.Sha3.absorbSig, Spec.Sha3.absorbPre, Spec.Sha3.absorbPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Spec.Sha3.hashSha3_512]
    [absorbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using absorbSat

theorem absorb_sha3_512 : Verified Arm.target (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_512.rate)
    (Spec.Sha3.absorbContract Arm.abi Spec.Sha3.hashSha3_512.rate 664) :=
  Arm.Verified.stackScratch (sig := Spec.Sha3.absorbSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.absorbPre Spec.Sha3.hashSha3_512.rate Arm.abi.ptrBits)
    (post := Spec.Sha3.absorbPost Spec.Sha3.hashSha3_512.rate Arm.abi.ptrBits) (wa := true) (stack := 16)
    (m := 0) (bytes := 648) Proof.Sha3.Arm.Instances.update_sha3_512 (by decide) (by decide) (by decide)
    (by decide) (Proof.Sha3.PostOut.absorbPre_local _ _) (Proof.Sha3.PostOut.absorbPost_local _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.absorbPost_out _ _ vs mm m₁ m₂ r hl hb h)
    absorbSat_sha3_512

theorem absorb_sha3_512_armStack :
    armStack (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_512.rate) ≤ 664 := by lit_decide

theorem absorb_sha3_512_noIcall :
    noIcall (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_512.rate) = true := by lit_decide

/-- `vg_sha3_512_absorb`. -/
def absorbSha3_512Reg : Registration Spec.Sha3.absorbSha3_512Api target :=
  scrubRegF {
      code := Impl.Sha3.Arm.Instances.absorb Spec.Sha3.hashSha3_512.rate
      verified := absorb_sha3_512 }
    absorb_sha3_512_armStack absorb_sha3_512_noIcall frameOk664 (absorbOut _ _) rfl

theorem absorbSat_shake128 : ∃ s, (Spec.Sha3.absorbContract Arm.abi Spec.Sha3.xofShake128.rate 664).pre s := by
  implies_sat [Spec.Sha3.absorbContract, Spec.Sha3.absorbSig, Spec.Sha3.absorbPre, Spec.Sha3.absorbPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Spec.Sha3.xofShake128]
    [absorbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using absorbSat

theorem absorb_shake128 : Verified Arm.target (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.xofShake128.rate)
    (Spec.Sha3.absorbContract Arm.abi Spec.Sha3.xofShake128.rate 664) :=
  Arm.Verified.stackScratch (sig := Spec.Sha3.absorbSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Sha3.absorbPre Spec.Sha3.xofShake128.rate Arm.abi.ptrBits)
    (post := Spec.Sha3.absorbPost Spec.Sha3.xofShake128.rate Arm.abi.ptrBits) (wa := true) (stack := 16)
    (m := 0) (bytes := 648) Proof.Sha3.Arm.Instances.update_shake128 (by decide) (by decide) (by decide)
    (by decide) (Proof.Sha3.PostOut.absorbPre_local _ _) (Proof.Sha3.PostOut.absorbPost_local _ _)
    (fun vs mm m₁ m₂ r hl _ hb h => Proof.Sha3.PostOut.absorbPost_out _ _ vs mm m₁ m₂ r hl hb h)
    absorbSat_shake128

theorem absorb_shake128_armStack :
    armStack (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.xofShake128.rate) ≤ 664 := by lit_decide

theorem absorb_shake128_noIcall :
    noIcall (Impl.Sha3.Arm.Instances.absorb Spec.Sha3.xofShake128.rate) = true := by lit_decide

/-- `vg_shake128_absorb`. -/
def absorbShake128Reg : Registration Spec.Sha3.absorbShake128Api target :=
  scrubRegF {
      code := Impl.Sha3.Arm.Instances.absorb Spec.Sha3.xofShake128.rate
      verified := absorb_shake128 }
    absorb_shake128_armStack absorb_shake128_noIcall frameOk664 (absorbOut _ _) rfl

end VG.Proof.Sha3.Arm.Absorb
