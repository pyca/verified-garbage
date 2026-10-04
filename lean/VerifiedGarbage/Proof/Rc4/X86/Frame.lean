import VerifiedGarbage.Proof.Rc4.X86.Verified
import VerifiedGarbage.Proof.Rc4.X86.Lit
import VerifiedGarbage.Proof.Rc4.Scratch
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe

/-!
# RC4 on x86, with the working space on the stack

`vg_rc4_init` and `vg_rc4_apply` keep our caller's `ebx`, `esi`, `edi` and
`ebp`, and `vg_rc4_apply` the secret `j`, in their working space: they run
their code, proved with it as an argument (`Verified.lean`), in a frame that
allocates it and copies their three argument slots, and zero it after the
code (`Verified.stackScratchWiped`): 84 bytes, 64 of working space. The code
uses no other stack. The copies are read only where the postconditions and
`vg_rc4_apply`'s leak, the context's `i`, read the buffers
(`Proof/Rc4/Scratch.lean`).
-/

namespace VG.Proof.Rc4.X86

open VG VG.X86

/-- A state satisfying `vg_rc4_init`'s precondition: a 1-byte key at
`0x1000` and the context at `0x2000`, as stack arguments at `0x8004`, which
are writable. -/
def initFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 1 else if a = 0x800d then 0x20 else 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 258⟩, ⟨0x8004, 12⟩]

theorem initFrameSat_pre : ∃ s, (Spec.Rc4.initContract X86.abi 84).pre s := by
  implies_sat [Spec.Rc4.initContract, Spec.Rc4.initSig, Spec.Rc4.initPost, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes] [initFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using initFrameSat

/-- A state satisfying `vg_rc4_apply`'s precondition: the context at
`0x1000` and 1 byte of data at `0x2000`, as stack arguments at `0x8004`,
which are writable. -/
def applyFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800c then 1 else 0
  rd := []
  wr := [⟨0x1000, 258⟩, ⟨0x2000, 1⟩, ⟨0x8004, 12⟩]

theorem applyFrameSat_pre : ∃ s, (Spec.Rc4.applyContract X86.abi 84).pre s := by
  implies_sat [Spec.Rc4.applyContract, Spec.Rc4.applySig, Spec.Rc4.applyPost, Spec.Rc4.applyLeak,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [applyFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using applyFrameSat

theorem init_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 84 3 16 Impl.Rc4.X86.init)
      (Spec.Rc4.initContract X86.abi 84) :=
  X86.Verified.stackScratchWiped (sig := Spec.Rc4.initSig) (nm := "scratch") (e := .u64) (n := 8)
    (post := Spec.Rc4.initPost X86.abi.ptrBits) (wa := true) (stack := 0) (bytes := 84)
    init_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Rc4.initPost_local _)
    (Proof.Rc4.initPostOut_local _) initFrameSat_pre

theorem apply_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 84 3 16 Impl.Rc4.X86.apply)
      (Spec.Rc4.applyContract X86.abi 84) :=
  X86.Verified.stackScratchWiped (sig := Spec.Rc4.applySig) (nm := "scratch") (e := .u64) (n := 8)
    (post := Spec.Rc4.applyPost X86.abi.ptrBits) (wa := true) (stack := 0) (bytes := 84)
    (leak := some (Spec.Rc4.applyLeak X86.abi.ptrBits))
    apply_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Rc4.applyPost_local _)
    (Proof.Rc4.applyPostOut_local _) applyFrameSat_pre (hleak := Proof.Rc4.applyLeak_local _)

end VG.Proof.Rc4.X86
