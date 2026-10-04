import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Hmac.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-!
# HMAC's `init` and `finalize` on ARMv7, with their working space on the stack

`init` and `finalize` run their `_scratch` forms (`Instances.lean`,
`Sha256.lean`, `Sha224.lean`) in a frame that allocates the working space and
copies the arguments passed on the stack (`Verified.stackScratch`):
`initFramed` and `finFramed`, for any instance, from the locality of HMAC's
pre- and postconditions (`Proof/Hmac/Scratch.lean`). `init` has no arguments
on the stack, `finalize` one (`out`). Both frames are `frame I` bytes: the
working space, the copied arguments and the saved registers, rounded up to a
multiple of 32 bytes, which an ARM immediate encodes. `initFrameSat` and
`finFrameSat` satisfy the preconditions of the contracts without the
working space.
-/

namespace VG.Proof.Pbkdf2.Md.Arm

open VG.Arm

/-- The bytes of `init`'s and `finalize`'s frames: `finalize`'s copy of its
one stack argument, the saved registers and the working space, rounded up to
a multiple of 32. -/
def frame (I : Spec.Hmac.Instance) : Nat := (4 + 8 + 8 * I.scratch + 31) / 32 * 32

theorem initFramed {I : Spec.Hmac.Instance} {c : Prog isa} {bytes : Nat}
    (h : Verified Arm.target c (I.initScratchContract Arm.abi 16))
    (hb : Fits 0 bytes .u64 I.scratch)
    (hsat : ∃ s, (I.initContract Arm.abi (16 + bytes)).pre s) :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch bytes 0 c)
      (I.initContract Arm.abi (16 + bytes)) :=
  Arm.Verified.stackScratch (sig := Spec.Hmac.initSig I.S) (nm := "scratch") (e := .u64)
    (n := I.scratch) (pre := Spec.Hmac.initPre I.S Arm.abi.ptrBits)
    (post := Spec.Hmac.initPost I.S Arm.abi.ptrBits) (wa := true) (stack := 16) (m := 0) h
    rfl rfl rfl hb
    (Hmac.initPre_local I.S _) (Hmac.initPost_local I.S _) hsat

theorem finFramed {I : Spec.Hmac.Instance} {c : Prog isa} {bytes : Nat}
    (h : Verified Arm.target c (I.finalizeScratchContract Arm.abi 16))
    (hb : Fits 1 bytes .u64 I.scratch)
    (hR : Hmac.ReprLocal I.S) (hS : I.S.stateBytes < 2 ^ 64)
    (hsat : ∃ s, (I.finalizeContract Arm.abi (16 + bytes)).pre s) :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch bytes 1 c)
      (I.finalizeContract Arm.abi (16 + bytes)) :=
  Arm.Verified.stackScratch (sig := Spec.Hmac.finalizeSig I.S) (nm := "scratch") (e := .u64)
    (n := I.scratch) (post := Spec.Hmac.finalizePost I.S Arm.abi.ptrBits) (wa := true)
    (stack := 16) (m := 1) h
    rfl rfl rfl hb
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Hmac.finalizePost_local I.S _ hR hS) hsat

/-- A state satisfying `init`'s precondition without the working space, with
states of `S` bytes (and a one-byte key). -/
def initFrameSat (S : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 1
    | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x3000, 1⟩]
  wr := [⟨0x1000, S⟩, ⟨0x2000, S⟩]

/-- A state satisfying `finalize`'s precondition without the working space,
with states of `S` bytes and a digest of `D` bytes; `out`, at `0x3000`, is
the stack argument. -/
def finFrameSat (S D : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000
    | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x6001 then 0x30 else 0
  rd := [⟨0x2000, S⟩, ⟨0x6000, 4⟩]
  wr := [⟨0x1000, S⟩, ⟨0x3000, D⟩]

theorem md5_initFrameSat :
    ∃ s, (Spec.Hmac.md5I.initContract Arm.abi (16 + frame Spec.Hmac.md5I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using initFrameSat 80

theorem md5_finFrameSat :
    ∃ s, (Spec.Hmac.md5I.finalizeContract Arm.abi (16 + frame Spec.Hmac.md5I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat 80 16

theorem sha1_initFrameSat :
    ∃ s, (Spec.Hmac.sha1I.initContract Arm.abi (16 + frame Spec.Hmac.sha1I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using initFrameSat 84

theorem sha1_finFrameSat :
    ∃ s, (Spec.Hmac.sha1I.finalizeContract Arm.abi (16 + frame Spec.Hmac.sha1I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat 84 20

theorem sha224_initFrameSat :
    ∃ s, (Spec.Hmac.sha224I.initContract Arm.abi (16 + frame Spec.Hmac.sha224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using initFrameSat 96

theorem sha224_finFrameSat :
    ∃ s, (Spec.Hmac.sha224I.finalizeContract Arm.abi (16 + frame Spec.Hmac.sha224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat 96 28

theorem sha256_initFrameSat :
    ∃ s, (Spec.Hmac.sha256I.initContract Arm.abi (16 + frame Spec.Hmac.sha256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using initFrameSat 96

theorem sha256_finFrameSat :
    ∃ s, (Spec.Hmac.sha256I.finalizeContract Arm.abi (16 + frame Spec.Hmac.sha256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat 96 32

theorem sha384_initFrameSat :
    ∃ s, (Spec.Hmac.sha384I.initContract Arm.abi (16 + frame Spec.Hmac.sha384I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using initFrameSat 192

theorem sha384_finFrameSat :
    ∃ s, (Spec.Hmac.sha384I.finalizeContract Arm.abi (16 + frame Spec.Hmac.sha384I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat 192 48

theorem sha512_initFrameSat :
    ∃ s, (Spec.Hmac.sha512I.initContract Arm.abi (16 + frame Spec.Hmac.sha512I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using initFrameSat 192

theorem sha512_finFrameSat :
    ∃ s, (Spec.Hmac.sha512I.finalizeContract Arm.abi (16 + frame Spec.Hmac.sha512I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat 192 64

theorem sha512_224_initFrameSat :
    ∃ s, (Spec.Hmac.sha512_224I.initContract Arm.abi (16 + frame Spec.Hmac.sha512_224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using initFrameSat 192

theorem sha512_224_finFrameSat :
    ∃ s, (Spec.Hmac.sha512_224I.finalizeContract Arm.abi (16 + frame Spec.Hmac.sha512_224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat 192 28

theorem sha512_256_initFrameSat :
    ∃ s, (Spec.Hmac.sha512_256I.initContract Arm.abi (16 + frame Spec.Hmac.sha512_256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using initFrameSat 192

theorem sha512_256_finFrameSat :
    ∃ s, (Spec.Hmac.sha512_256I.finalizeContract Arm.abi (16 + frame Spec.Hmac.sha512_256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat 192 32

end VG.Proof.Pbkdf2.Md.Arm
