import VerifiedGarbage.Proof.Aes.X86_64.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe

/-!
# The AES key expansion on x86-64, with its working space on the stack

`vg_aes_expand_key` and `vg_aes_expand_key_aesni` run the code of
`vg_aes_expand_key_scratch` and `vg_aes_expand_key_scratch_aesni`, proved
with the working space as an argument, in a frame that allocates it and
zeroes it after the code (`Verified.stackScratchWiped`), since it may hold
the key and its schedule: 520 bytes, the 512 of working space and 8 more to
keep `rsp` aligned. The code uses no other stack.
-/

namespace VG.Proof.Aes.X86_64

open VG VG.X86_64

/-- A state satisfying `vg_aes_expand_key`'s precondition: a 16-byte key at
`0x1000` and the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 240⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Aes.expandKeyContract X86_64.abi 520).pre s := by
  implies_sat [Spec.Aes.expandKeyContract, Spec.Aes.expandKeySig, Spec.Aes.expandKeyPre,
    Spec.Aes.expandKeyPost, X86_64.abi, X86_64.argRegs] [expandKeyFrameSat] using expandKeyFrameSat

/-- The code `c` of `vg_aes_expand_key_scratch` or of one of its variants,
proved with its working space as an argument and no stack, in its frame. -/
theorem expandKey_framed {c : Prog isa}
    (h : Verified X86_64.target c (Spec.Aes.expandKeyScratchContract X86_64.abi))
    (hsp : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ 0) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 520 .rcx 64 c)
      (Spec.Aes.expandKeyContract X86_64.abi 520) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Aes.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 64) (pre := Spec.Aes.expandKeyPre X86_64.abi.ptrBits)
    (post := Spec.Aes.expandKeyPost X86_64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 520) (Proof.Aes.expandKey_scratch h) (by decide) (by decide) (by decide) hsp hd
    (by decide) (Proof.Aes.expandKeyPostOut_local _) expandKeyFrameSat_pre

theorem scalar_expandKey_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratchWiped 520 .rcx 64 Impl.Aes.X86_64.expandKey)
      (Spec.Aes.expandKeyContract X86_64.abi 520) :=
  expandKey_framed expandKey_verified (Code.all_of_allInstrs (by lit_decide)) (by lit_decide)

theorem aesni_expandKey_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratchWiped 520 .rcx 64 Impl.Aes.X86_64.AesNi.expandKey)
      (Spec.Aes.expandKeyContract X86_64.abi 520) :=
  expandKey_framed AesNi.Key.expandKey_verified (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide)

end VG.Proof.Aes.X86_64
