import VerifiedGarbage.Proof.TripleDes.X86.Key.Verified
import VerifiedGarbage.Proof.TripleDes.X86.Ecb.Verified
import VerifiedGarbage.Proof.TripleDes.Scratch
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe

/-!
# Triple DES key expansion and ECB on x86, with their working space on the stack

Key expansion and ECB run their code, proved with the working space as an
argument, in a frame that allocates it and copies their three argument slots,
and zeroes it after the code (`Verified.stackScratchWiped`), since it may
hold the key schedule and the data: 532 bytes for key expansion (512 of
working space) and 1044 for ECB (1024). The copies are read only where the
postconditions read the buffers (`Proof/TripleDes/Scratch.lean`).
-/

namespace VG.Proof.TripleDes.X86

open VG VG.X86

/-- A state satisfying `vg_triple_des_expand_key`'s precondition: a 16-byte
key at `0x1000` and the schedule at `0x2000`, as stack arguments at
`0x8004`. -/
def expandKeyFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800d then 0x20 else 0
  rd := [⟨0x1000, 16⟩, ⟨0x8004, 12⟩]
  wr := [⟨0x2000, 384⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.TripleDes.expandKeyContract X86.abi 532).pre s := by
  implies_sat [Spec.TripleDes.expandKeyContract, Spec.TripleDes.expandKeySig,
    Spec.TripleDes.expandKeyPre, Spec.TripleDes.expandKeyPost, Spec.TripleDes.validKey, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes]
    [expandKeyFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using expandKeyFrameSat

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000` and no blocks at `0x2000`, as stack arguments at `0x8004`, which
are writable. -/
def ecbFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x8004, 12⟩]

theorem ecbFrameSat_pre (d : Spec.TripleDes.Direction) :
    ∃ s, (Spec.TripleDes.ecbContract X86.abi d 1060).pre s := by
  implies_sat [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, Spec.TripleDes.ecbPost, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes]
    [ecbFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using ecbFrameSat

theorem expandKey_framed :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped 532 3 128 Impl.TripleDes.X86.Key.expandKey)
      (Spec.TripleDes.expandKeyContract X86.abi 532) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 64) (pre := Spec.TripleDes.expandKeyPre X86.abi.ptrBits)
    (post := Spec.TripleDes.expandKeyPost X86.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 532) Key.verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (Proof.TripleDes.expandKeyPre_local _) (Proof.TripleDes.expandKeyPost_local _)
    (Proof.TripleDes.expandKeyPostOut_local _) expandKeyFrameSat_pre

theorem ecb_framed (d : Spec.TripleDes.Direction) :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped 1044 3 256 (Impl.TripleDes.X86.Ecb.ecb d))
      (Spec.TripleDes.ecbContract X86.abi d 1060) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.ecbSig) (nm := "scratch") (e := .u64)
    (n := 128) (post := Spec.TripleDes.ecbPost d X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 1044) (Ecb.ecb_verified d) (by decide) (by cases d <;> lit_decide)
    (by cases d <;> lit_decide) (by decide) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.ecbPost_local _ d) (Proof.TripleDes.ecbPostOut_local _ d) (ecbFrameSat_pre d)

end VG.Proof.TripleDes.X86
