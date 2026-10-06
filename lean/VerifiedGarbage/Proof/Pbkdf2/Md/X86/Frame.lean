import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Hmac.Scratch
import VerifiedGarbage.Proof.Framework.X86.StackScratch

/-!
# HMAC's `init` and `finalize` on x86, with their working space on the stack

`init` and `finalize` run their `_scratch` forms (`Instances.lean`, and the
SHA-256 backends' `Proof/Sha256/X86/Variants/Interface.lean`) in a frame
that allocates the working space and copies the arguments passed on the
stack (`Verified.stackScratch`): `initFramed` and `finFramed`, for any
instance, from the locality of HMAC's pre- and postconditions
(`Proof/Hmac/Scratch.lean`). `initFrameSat` and `finFrameSat` satisfy the
preconditions of the contracts without the working space.
-/

namespace VG.Proof.Pbkdf2.Md.X86

open VG.X86

/-- The bytes of `init`'s frame: its return address, a copy of its four
argument slots and the working space. -/
def initFrame (I : Spec.Hmac.Instance) : Nat := 8 + 16 + 8 * I.scratch

/-- The bytes of `finalize`'s frame: as `initFrame`, with five argument
slots. -/
def finFrame (I : Spec.Hmac.Instance) : Nat := 8 + 20 + 8 * I.scratch

theorem initFramed {I : Spec.Hmac.Instance} {c : Prog isa}
    (h : Verified X86.target c (I.initScratchContract X86.abi 48)) (hs : 8 * I.scratch < 4072)
    (hsp : c.allInstrs (fun i => !Taint.clobbers i .esp) = true) (hd : stackUse c ≤ 48)
    (hsat : ∃ s, (I.initContract X86.abi (48 + initFrame I)).pre s) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch (initFrame I) 4 c)
      (I.initContract X86.abi (48 + initFrame I)) :=
  X86.Verified.stackScratch (sig := Spec.Hmac.initSig I.S) (nm := "scratch") (e := .u64)
    (n := I.scratch) (pre := Spec.Hmac.initPre I.S X86.abi.ptrBits)
    (post := Spec.Hmac.initPost I.S X86.abi.ptrBits) (wa := true) (stack := 48)
    (bytes := initFrame I) h
    (by
      refine ⟨?_, by simp only [initFrame]; omega, by simp only [initFrame]; omega⟩
      change 8 + 4 * 4 + I.scratch * 8 ≤ initFrame I
      simp only [initFrame]; omega)
    hsp hd (Hmac.initPre_local I.S _) (Hmac.initPost_local I.S _) hsat

theorem finFramed {I : Spec.Hmac.Instance} {c : Prog isa}
    (h : Verified X86.target c (I.finalizeScratchContract X86.abi 48)) (hs : 8 * I.scratch < 4068)
    (hR : Hmac.ReprLocal I.S) (hS : I.S.stateBytes < 2 ^ 64)
    (hsp : c.allInstrs (fun i => !Taint.clobbers i .esp) = true) (hd : stackUse c ≤ 48)
    (hsat : ∃ s, (I.finalizeContract X86.abi (48 + finFrame I)).pre s) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch (finFrame I) 5 c)
      (I.finalizeContract X86.abi (48 + finFrame I)) :=
  X86.Verified.stackScratch (sig := Spec.Hmac.finalizeSig I.S) (nm := "scratch") (e := .u64)
    (n := I.scratch) (post := Spec.Hmac.finalizePost I.S X86.abi.ptrBits) (wa := true) (stack := 48)
    (bytes := finFrame I) h
    (by
      refine ⟨?_, by simp only [finFrame]; omega, by simp only [finFrame]; omega⟩
      change 8 + 4 * 5 + I.scratch * 8 ≤ finFrame I
      simp only [finFrame]; omega)
    hsp hd (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Hmac.finalizePost_local I.S _ hR hS) hsat

/-- Memory holding the arguments `0x1000, 0x1400, 0x1800, 0` of `init` at
`0x6004`. -/
def initFrameMem : Mem := fun a =>
  if a = 0x6005 then 0x10 else if a = 0x6009 then 0x14 else if a = 0x600D then 0x18 else 0

/-- A state satisfying `init`'s precondition without the working space, with
states of `S` bytes (and an empty key), with the arguments writable. -/
def initFrameSat (S : Nat) : State where
  gpr r := match r with
    | .esp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := initFrameMem
  rd := [⟨0x1800, 0⟩]
  wr := [⟨0x1000, S⟩, ⟨0x1400, S⟩, ⟨0x6004, 16⟩]

/-- Memory holding the arguments `0x1000, 0x1400, 0, 0, 0x1800` of
`finalize` at `0x6004`. -/
def finFrameMem : Mem := fun a =>
  if a = 0x6005 then 0x10 else if a = 0x6009 then 0x14 else if a = 0x6015 then 0x18 else 0

/-- A state satisfying `finalize`'s precondition without the working space,
with states of `S` bytes and a digest of `D` bytes, with the arguments
writable. -/
def finFrameSat (S D : Nat) : State where
  gpr r := match r with
    | .esp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := finFrameMem
  rd := [⟨0x1400, S⟩]
  wr := [⟨0x1000, S⟩, ⟨0x1800, D⟩, ⟨0x6004, 20⟩]

/-- The frame of `withStackScratch` keeps the stack pointer for any `c` that
does, if it does for an empty body (decided for literal sizes). -/
theorem withStackScratch_spSafe {bytes n : Nat} {c : Prog isa}
    (hf : (Impl.StackScratch.X86.withStackScratch bytes n (.block [])).all
      (fun i => !isa.writesSp i) = true)
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (Impl.StackScratch.X86.withStackScratch bytes n c).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.StackScratch.X86.withStackScratch, Code.all, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at hf ⊢
  simp_all

/-- `c` writes `esp` only through its frames' pushes and pops: as `NoSp`. -/
theorem noEsp_of {c : Prog isa} (h : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

theorem md5_initFrameSat :
    ∃ s, (Spec.Hmac.md5I.initContract X86.abi (48 + initFrame Spec.Hmac.md5I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, initFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using initFrameSat 80

theorem md5_finFrameSat :
    ∃ s, (Spec.Hmac.md5I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.md5I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, finFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using finFrameSat 80 16

theorem sha1_initFrameSat :
    ∃ s, (Spec.Hmac.sha1I.initContract X86.abi (48 + initFrame Spec.Hmac.sha1I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, initFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using initFrameSat 84

theorem sha1_finFrameSat :
    ∃ s, (Spec.Hmac.sha1I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha1I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, finFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using finFrameSat 84 20

theorem sha224_initFrameSat :
    ∃ s, (Spec.Hmac.sha224I.initContract X86.abi (48 + initFrame Spec.Hmac.sha224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, initFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using initFrameSat 96

theorem sha224_finFrameSat :
    ∃ s, (Spec.Hmac.sha224I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, finFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using finFrameSat 96 28

theorem sha256_initFrameSat :
    ∃ s, (Spec.Hmac.sha256I.initContract X86.abi (48 + initFrame Spec.Hmac.sha256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, initFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using initFrameSat 96

theorem sha256_finFrameSat :
    ∃ s, (Spec.Hmac.sha256I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, finFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using finFrameSat 96 32

theorem sha384_initFrameSat :
    ∃ s, (Spec.Hmac.sha384I.initContract X86.abi (48 + initFrame Spec.Hmac.sha384I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, initFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using initFrameSat 192

theorem sha384_finFrameSat :
    ∃ s, (Spec.Hmac.sha384I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha384I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, finFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using finFrameSat 192 48

theorem sha512_initFrameSat :
    ∃ s, (Spec.Hmac.sha512I.initContract X86.abi (48 + initFrame Spec.Hmac.sha512I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, initFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using initFrameSat 192

theorem sha512_finFrameSat :
    ∃ s, (Spec.Hmac.sha512I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha512I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, finFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using finFrameSat 192 64

theorem sha512_224_initFrameSat :
    ∃ s, (Spec.Hmac.sha512_224I.initContract X86.abi (48 + initFrame Spec.Hmac.sha512_224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, initFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using initFrameSat 192

theorem sha512_224_finFrameSat :
    ∃ s, (Spec.Hmac.sha512_224I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha512_224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, finFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using finFrameSat 192 28

theorem sha512_256_initFrameSat :
    ∃ s, (Spec.Hmac.sha512_256I.initContract X86.abi (48 + initFrame Spec.Hmac.sha512_256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, initFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using initFrameSat 192

theorem sha512_256_finFrameSat :
    ∃ s, (Spec.Hmac.sha512_256I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha512_256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, finFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using finFrameSat 192 32

end VG.Proof.Pbkdf2.Md.X86
