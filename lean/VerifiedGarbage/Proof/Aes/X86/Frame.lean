import VerifiedGarbage.Proof.Aes.X86.ExpandKey
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyBlocks
import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyVerified
import VerifiedGarbage.Proof.Aes.Scratch
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe

/-!
# The AES key expansion on x86, with its working space on the stack

`vg_aes_expand_key` and `vg_aes_expand_key_aesni` run the code of
`vg_aes_expand_key_scratch` and `vg_aes_expand_key_scratch_aesni`, proved
with the working space as an argument, in a frame that allocates it and
copies their three argument slots, and zeroes it after the code
(`Verified.stackScratchWiped`), since it may hold the key and its schedule:
532 bytes, the 512 of working space, the copies and the return address of
the call of the code, which uses no other stack. The copies are read only
where the pre- and postcondition read the buffers
(`Proof/Aes/Scratch.lean`).
-/

namespace VG.Proof.Aes.X86

open VG VG.X86

/-- A state satisfying `vg_aes_expand_key`'s precondition: a 16-byte key at
`0x1000` and the schedule at `0x2000`, as stack arguments at `0x8004`. -/
def expandKeyFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800d then 0x20 else 0
  rd := [⟨0x1000, 16⟩, ⟨0x8004, 12⟩]
  wr := [⟨0x2000, 240⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Aes.expandKeyContract X86.abi 532).pre s := by
  implies_sat [Spec.Aes.expandKeyContract, Spec.Aes.expandKeySig, Spec.Aes.expandKeyPre,
    Spec.Aes.expandKeyPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [expandKeyFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using expandKeyFrameSat

/-- The code `c` of `vg_aes_expand_key_scratch` or of one of its variants,
proved with its working space as an argument and no stack, in its frame. -/
theorem expandKey_framed {c : Prog isa}
    (h : Verified X86.target c (Spec.Aes.expandKeyScratchContract X86.abi))
    (hsp : c.allInstrs (fun i => !Taint.clobbers i .esp) = true) (hd : stackUse c ≤ 0) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 532 3 128 c)
      (Spec.Aes.expandKeyContract X86.abi 532) :=
  X86.Verified.stackScratchWiped (sig := Spec.Aes.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 64) (pre := Spec.Aes.expandKeyPre X86.abi.ptrBits)
    (post := Spec.Aes.expandKeyPost X86.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 532) (Proof.Aes.expandKey_scratch h) (by decide) hsp hd (by decide)
    (Proof.Aes.expandKeyPre_local _) (Proof.Aes.expandKeyPost_local _)
    (Proof.Aes.expandKeyPostOut_local _) expandKeyFrameSat_pre

theorem scalar_expandKey_framed :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped 532 3 128 Impl.Aes.X86.expandKey)
      (Spec.Aes.expandKeyContract X86.abi 532) :=
  expandKey_framed expandKey_verified (by lit_decide) (by lit_decide)

theorem aesni_expandKey_framed :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped 532 3 128 Impl.Aes.X86.AesNi.expandKey)
      (Spec.Aes.expandKeyContract X86.abi 532) :=
  expandKey_framed
    (AesNi.expandKey_verified ⟨AesNi.expand128_ok, AesNi.expand192_ok, AesNi.expand256_ok⟩)
    (by lit_decide) (by lit_decide)

end VG.Proof.Aes.X86
