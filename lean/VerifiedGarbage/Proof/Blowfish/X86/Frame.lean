module
public import VerifiedGarbage.Proof.Blowfish.X86.Contract
public import VerifiedGarbage.Impl.StackScratch.X86

import VerifiedGarbage.Proof.Blowfish.X86.Verified
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Impl.Blowfish.X86
import VerifiedGarbage.Proof.Blowfish.X86.Run

/-!
# Blowfish on x86 (32-bit), with the working space on the stack

Key expansion and ECB keep our caller's `ebx`, `esi`, `edi` and `ebp`, the
halves, F, and their pointer and counter in working space that was their
fourth argument: they run their code, proved with it as an argument
(`Verified.lean`), in a frame that allocates it and copies their three
argument slots, and zero the 40 bytes of it they use after the code
(`Verified.stackScratchWiped`): 84 bytes for key expansion (64 of working
space) and 276 for ECB (256). The code uses no other stack.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86

open VG VG.X86

/-- A state satisfying `vg_blowfish_expand_key`'s precondition: a 4-byte key
at `0x1000` and the schedule at `0x2000`, as stack arguments at `0x8004`. -/
def expandKeyFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 4 else if a = 0x800d then 0x20 else 0
  rd := [⟨0x1000, 4⟩, ⟨0x8004, 12⟩]
  wr := [⟨0x2000, 4168⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Blowfish.expandKeyContract X86.abi 84).pre s := by
  implies_sat [Spec.Blowfish.expandKeyContract, Spec.Blowfish.expandKeySig, Spec.Blowfish.expandKeyPre,
    Spec.Blowfish.expandKeyPost, Spec.Blowfish.validKey, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [expandKeyFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using expandKeyFrameSat

theorem expandKey_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 84 3 10 Impl.Blowfish.X86.expandKey)
      (Spec.Blowfish.expandKeyContract X86.abi 84) :=
  X86.Verified.stackScratchWiped (sig := Spec.Blowfish.expandKeySig) (nm := "scratch") (e := .u64) (n := 8)
    (pre := Spec.Blowfish.expandKeyPre X86.abi.ptrBits) (post := Spec.Blowfish.expandKeyPost X86.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 84)
    expandKey_verified (by decide) (by decide +kernel) (by decide +kernel) (by decide)
    (Proof.Blowfish.expandKeyPre_local _) (Proof.Blowfish.expandKeyPost_local _)
    (Proof.Blowfish.expandKeyPostOut_local _) expandKeyFrameSat_pre

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000` and no data at `0x2000`, as stack arguments at `0x8004`, which are
writable. -/
def ecbFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x8004, 12⟩]

theorem ecbFrameSat_pre (d : Spec.Blowfish.Direction) :
    ∃ s, (Spec.Blowfish.ecbContract X86.abi d 276).pre s := by
  have h0 : (X86.arg ecbFrameSat 2).toNat = 0 := by decide
  refine ⟨ecbFrameSat, ?_⟩
  sig_pre [Spec.Blowfish.ecbContract, Spec.Blowfish.ecbSig, Spec.Blowfish.ecbPost, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
  sig_and_intros
  -- The data is empty.
  all_goals first
    | rfl
    | decide
    | (intro a _ h₂; simp only [Region.Contains, h0] at h₂; omega)
    | exact Region.disjoint_of_sep (by decide)

theorem ecb_framed (up : Bool) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 276 3 10 (Impl.Blowfish.X86.ecb up))
      (Spec.Blowfish.ecbContract X86.abi (dir up) 276) :=
  X86.Verified.stackScratchWiped (sig := Spec.Blowfish.ecbSig) (nm := "scratch") (e := .u64) (n := 32)
    (post := Spec.Blowfish.ecbPost (dir up) X86.abi.ptrBits) (wa := true) (stack := 0) (bytes := 276)
    (ecb_verified up) (by decide) (by cases up <;> lit_decide) (by cases up <;> lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Blowfish.ecbPost_local _ (dir up))
    (Proof.Blowfish.ecbPostOut_local _ (dir up)) (ecbFrameSat_pre (dir up))

end VG.Proof.Blowfish.X86
