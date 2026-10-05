import VerifiedGarbage.Proof.AesSiv.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# AES-SIV's key setup on x86-64, with its working space on the stack

`vg_aes_siv_init` runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame of 2568 bytes that allocates it
(`Verified.stackScratch`): the 2560 bytes of working space, and 8 more to
keep `rsp` aligned. Its own calls use 16 bytes below it: two return
addresses, as `vg_aes_ctr32` and `vg_aes_expand_key_scratch` use no stack.
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.Impl.AesSiv.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem init_xdepth (v : Ctr32Impl) : (init v.expand v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [init, Impl.CmacAes.X86_64.subkeys, Code.x86_64Depth, v.noStack, v.expandNoStack]
  decide +kernel

/-- A state satisfying `vg_aes_siv_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 512⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Siv.initContract X86_64.abi 2584).pre s := by
  implies_sat [Spec.Siv.initContract, Spec.Siv.initSig, Spec.Siv.initPre, Spec.Siv.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed (v : Ctr32Impl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (init v.expand v.callee v.suffix))
      (Spec.Siv.initContract X86_64.abi 2584) :=
  X86_64.Verified.stackScratch (sig := Spec.Siv.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Siv.initPre X86_64.abi.ptrBits) (post := Spec.Siv.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 2568) (init_verified v) (by decide) (by decide) (by decide)
    (init_spSafe v) (init_xdepth v) initFrameSat_pre

end VG.Proof.AesSiv.X86_64
