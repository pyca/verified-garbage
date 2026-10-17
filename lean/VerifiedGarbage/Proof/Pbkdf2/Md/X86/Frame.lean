module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Hmac.Scratch
public import VerifiedGarbage.Proof.Framework.X86.StackScratch
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs

/-!
# HMAC's `finalize` on x86, with its working space on the stack

`finalize` runs its `_scratch` form (`Instances.lean`, and the SHA-256
backends' `Proof/Sha256/X86/Variants/Interface.lean`) in a frame that
allocates the working space and copies the arguments passed on the stack
(`Verified.stackScratch`): `finFramed`, for any instance, from the locality
of HMAC's postcondition (`Proof/Hmac/Scratch.lean`). `finFrameSat`
satisfies the precondition of the contract without the working space, and
`initFrameSat` that of `init` (`Proof/Pbkdf2/Whole/X86/AnyKeyCT.lean`, which
frames `init` for a key of any length).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86

open VG.X86

/-- The bytes of `finalize`'s frame: its return address, a copy of its five
argument slots and the working space. -/
def finFrame (I : Spec.Hmac.Instance) : Nat := 8 + 20 + 8 * I.scratch

theorem finFramed {I : Spec.Hmac.Instance} {c : Prog isa}
    (h : Verified X86.target c (I.finalizeScratchContract X86.abi 48))
    (hR : Hmac.ReprLocal I.S)
    (hsat : ∃ s, (I.finalizeContract X86.abi (48 + finFrame I)).pre s)
    (hsp : c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by lit_decide)
    (hd : stackUse c ≤ 48 := by lit_decide)
    (hs : 8 * I.scratch < 4068 := by decide) (hS : I.S.stateBytes < 2 ^ 64 := by decide) :
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
    (h : c.all (fun i => !isa.writesSp i) = true)
    (hf : (Impl.StackScratch.X86.withStackScratch bytes n (.block [])).all
      (fun i => !isa.writesSp i) = true := by decide) :
    (Impl.StackScratch.X86.withStackScratch bytes n c).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.StackScratch.X86.withStackScratch, Code.all, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at hf ⊢
  simp_all

/-- `c` writes `esp` only through its frames' pushes and pops: as `NoSp`. -/
theorem noEsp_of {c : Prog isa} (h : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

theorem md5_finFrameSat :
    ∃ s, (Spec.Hmac.md5I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.md5I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, finFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using finFrameSat 80 16

theorem sha1_finFrameSat :
    ∃ s, (Spec.Hmac.sha1I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha1I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, finFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using finFrameSat 84 20

theorem sha224_finFrameSat :
    ∃ s, (Spec.Hmac.sha224I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, finFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using finFrameSat 96 28

theorem sha256_finFrameSat :
    ∃ s, (Spec.Hmac.sha256I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, finFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using finFrameSat 96 32

theorem sha384_finFrameSat :
    ∃ s, (Spec.Hmac.sha384I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha384I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, finFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using finFrameSat 192 48

theorem sha512_finFrameSat :
    ∃ s, (Spec.Hmac.sha512I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha512I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, finFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using finFrameSat 192 64

theorem sha512_224_finFrameSat :
    ∃ s, (Spec.Hmac.sha512_224I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha512_224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, finFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using finFrameSat 192 28

theorem sha512_256_finFrameSat :
    ∃ s, (Spec.Hmac.sha512_256I.finalizeContract X86.abi (48 + finFrame Spec.Hmac.sha512_256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, finFrame,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finFrameSat, finFrameMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using finFrameSat 192 32

end VG.Proof.Pbkdf2.Md.X86
