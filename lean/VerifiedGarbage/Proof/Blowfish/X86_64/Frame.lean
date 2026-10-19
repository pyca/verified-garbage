module
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Blowfish.Scratch
public import VerifiedGarbage.Proof.Blowfish.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.Blowfish.X86_64.KeyVerified
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Blowfish.X86_64.Block
import VerifiedGarbage.Proof.Blowfish.X86_64.Combine
import VerifiedGarbage.Proof.Blowfish.X86_64.Verified
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Spec.Rc2

/-!
# Blowfish on x86-64, with its working space on the stack

Key expansion and ECB run their code, proved with the working space as an
argument, in a frame that allocates it and zeroes the bytes the code uses
after the code (`Verified.stackScratchWiped`), since they hold the key
schedule's intermediate blocks and the data: 40 bytes for key expansion (32
of working space) and 264 for ECB (256, of which it uses 16), with 8 more to
keep `rsp` aligned. The code uses no other stack.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64

/-- A state satisfying `vg_blowfish_expand_key`'s precondition: a 16-byte key
at `0x1000` and the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 4168⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Blowfish.expandKeyContract X86_64.abi 40).pre s := by
  implies_sat [Spec.Blowfish.expandKeyContract, Spec.Blowfish.expandKeySig, Spec.Blowfish.expandKeyPre,
    Spec.Blowfish.expandKeyPost, Spec.Blowfish.validKey, X86_64.abi, X86_64.argRegs] [expandKeyFrameSat]
    using expandKeyFrameSat

theorem expandKey_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratchWiped 40 .rcx 4 Impl.Blowfish.X86_64.expandKey)
      (Spec.Blowfish.expandKeyContract X86_64.abi 40) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Blowfish.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 4) (pre := Spec.Blowfish.expandKeyPre X86_64.abi.ptrBits)
    (post := Spec.Blowfish.expandKeyPost X86_64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 40) expandKey_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by decide +kernel)) (by decide +kernel) (by decide)
    (Proof.Blowfish.expandKeyPostOut_local _) expandKeyFrameSat_pre

/-- An implementation `c` of ECB in the direction `d`, proved with its
working space as an argument and no stack, in its frame. -/
theorem ecb_framed {c : Prog isa} {d : Spec.Blowfish.Direction}
    (h : Verified X86_64.target c (Proof.Blowfish.ecbScratchContract X86_64.abi d 0))
    (hsp : c.all (fun i => !isa.writesSp i) = true := by exact Code.all_of_allInstrs (by lit_decide))
    (hd : c.x86_64Depth ≤ 0 := by lit_decide) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 264 .rcx 2 c)
      (Spec.Blowfish.ecbContract X86_64.abi d 264) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Blowfish.ecbSig) (nm := "scratch") (e := .u64)
    (n := 32) (post := Spec.Blowfish.ecbPost d X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 264) h (by decide) (by decide) (by decide) hsp hd (by decide)
    (Proof.Blowfish.ecbPostOut_local _ d)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Blowfish.X86_64
