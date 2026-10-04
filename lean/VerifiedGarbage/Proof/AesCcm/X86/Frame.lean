import VerifiedGarbage.Proof.AesCcm.X86.Verified
import VerifiedGarbage.Proof.Framework.X86.StackScratch

/-!
# AES-CCM on x86, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it and copies the
arguments passed on the stack (`Verified.stackScratch`): the return address,
the ten argument slots and the 2560 bytes of working space, 2608 bytes. The
code's own calls use 56 bytes below it. The copies are read only where the
pre- and postconditions read the buffers, and `open`'s leak, whether it
succeeds, reads only its buffers (`Proof/AesCcm/Scratch.lean`).
-/

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86

theorem noEsp_of {c : Prog isa} (h : NoSp c) :
    c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

variable (v : Proof.Aes.X86.Ctr32Impl)

theorem seal_noEsp : («seal» v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [«seal», ccmEntry, Impl.AesGcm.X86.entry, ctrs, mac, b0, aad, aadHead, header, absorbPad, updBlock,
    updCall, Impl.CmacAes.Stream.X86.call6, tag, ctr, ctrCall, tagOut, Code.allInstrs,
    noEsp_of (Proof.CmacAes.X86.update_nosp v), noEsp_of v.nosp]
  decide +kernel

theorem open_noEsp : («open» v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [«open», ccmEntry, Impl.AesGcm.X86.entry, ctrs, mac, b0, aad, aadHead, header, absorbPad, updBlock,
    updCall, Impl.CmacAes.Stream.X86.call6, tag, ctr, ctrCall, mask, Impl.AesGcm.X86.recv, Impl.AesGcm.X86.cmp,
    Code.allInstrs, noEsp_of (Proof.CmacAes.X86.update_nosp v), noEsp_of v.nosp]
  decide +kernel

theorem seal_stackUse : stackUse («seal» v.callee v.suffix) ≤ 56 := by
  simp only [«seal», ccmEntry, Impl.AesGcm.X86.entry, ctrs, mac, b0, aad, aadHead, header, absorbPad, updBlock,
    updCall, Impl.CmacAes.Stream.X86.call6, tag, ctr, ctrCall, tagOut, stackUse,
    Proof.CmacAes.X86.update_stack v, v.stack]
  decide +kernel

theorem open_stackUse : stackUse («open» v.callee v.suffix) ≤ 56 := by
  simp only [«open», ccmEntry, Impl.AesGcm.X86.entry, ctrs, mac, b0, aad, aadHead, header, absorbPad, updBlock,
    updCall, Impl.CmacAes.Stream.X86.call6, tag, ctr, ctrCall, mask, Impl.AesGcm.X86.recv, Impl.AesGcm.X86.cmp,
    stackUse, Proof.CmacAes.X86.update_stack v, v.stack]
  decide +kernel

/-- A state satisfying `vg_aes_ccm_seal`'s precondition, without the working
space: as `sealSat`, with ten stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x4000, 4⟩, ⟨0x8004, 40⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.Ccm.sealContract X86.abi 2664).pre s := by
  implies_sat [Spec.Ccm.sealContract, Spec.Ccm.sealSig, Spec.Ccm.sealPre, Spec.Ccm.sealPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [sealFrameSat, sealSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using sealFrameSat

/-- A state satisfying `vg_aes_ccm_open`'s precondition, without the working
space: as `sealFrameSat`, with the tag read only. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x4000, 4⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x8004, 40⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.Ccm.openContract X86.abi 2664).pre s := by
  implies_sat [Spec.Ccm.openContract, Spec.Ccm.openSig, Spec.Ccm.openPre, Spec.Ccm.openPost,
    Spec.Ccm.openLeak, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [openFrameSat, sealSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using openFrameSat

theorem seal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2608 10 («seal» v.callee v.suffix))
      (Spec.Ccm.sealContract X86.abi 2664) :=
  X86.Verified.stackScratch (sig := Spec.Ccm.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ccm.sealPre X86.abi.ptrBits) (post := Spec.Ccm.sealPost X86.abi.ptrBits)
    (wa := true) (stack := 56) (bytes := 2608) (seal_verified v) (by decide) (seal_noEsp v)
    (seal_stackUse v) (sealPre_local _) (sealPost_local _) sealFrameSat_pre

theorem open_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2608 10 («open» v.callee v.suffix))
      (Spec.Ccm.openContract X86.abi 2664) :=
  X86.Verified.stackScratch (sig := Spec.Ccm.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ccm.openPre X86.abi.ptrBits) (post := Spec.Ccm.openPost X86.abi.ptrBits)
    (wa := true) (stack := 56) (leak := some (Spec.Ccm.openLeak X86.abi.ptrBits)) (bytes := 2608)
    (open_verified v) (by decide) (open_noEsp v) (open_stackUse v) (openPre_local _) (openPost_local _)
    openFrameSat_pre (hleak := openLeak_local _)

end VG.Proof.AesCcm.X86
