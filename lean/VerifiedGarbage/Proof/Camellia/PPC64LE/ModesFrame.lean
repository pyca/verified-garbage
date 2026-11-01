module

public import VerifiedGarbage.Proof.Camellia.CbcScratch
public import VerifiedGarbage.Proof.Camellia.FbScratch
public import VerifiedGarbage.Proof.Camellia.CtrScratch
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.Camellia.Cfb
public import VerifiedGarbage.Spec.Camellia.Ofb
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Camellia's modes on PPC64LE, with their working space on the stack

Each mode runs its code, proved with the working space as an argument, in a
frame that allocates it and zeroes it after the code
(`Verified.stackScratchWiped`), since it holds the table of subkeys, the
caller's registers, a block of data and the chaining value: 3408 bytes, the
frame's 32-byte header and the 3376 of working space. The code uses no other
stack: it calls nothing.
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG VG.PPC64LE

/-- A state satisfying the modes' precondition, without the working space:
the schedule at `0x1000`, 18 rounds, the IV at `0x3000` and no data at
`0x4000`. -/
def modeFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 18 | .r5 => 0x3000 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 0⟩]

theorem cbcEncFrameSat_pre : ∃ s, (Spec.Camellia.cbcEncryptChainedContract PPC64LE.abi 3408).pre s := by
  implies_sat [Spec.Camellia.cbcEncryptChainedContract, Spec.Camellia.cbcChainedSig,
    PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

theorem cbcDecFrameSat_pre : ∃ s, (Spec.Camellia.cbcDecryptChainedContract PPC64LE.abi 3408).pre s := by
  implies_sat [Spec.Camellia.cbcDecryptChainedContract, Spec.Camellia.cbcChainedSig,
    PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

theorem ofbFrameSat_pre : ∃ s, (Spec.Camellia.ofbContract PPC64LE.abi 3408).pre s := by
  implies_sat [Spec.Camellia.ofbContract, Spec.Camellia.ofbSig, Spec.Camellia.ofbPre,
    Spec.Camellia.ofbPost, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

theorem cfbEncFrameSat_pre : ∃ s, (Spec.Camellia.cfbEncryptContract PPC64LE.abi 3408).pre s := by
  implies_sat [Spec.Camellia.cfbEncryptContract, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre,
    Spec.Camellia.cfbEncryptPost, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

theorem cfbDecFrameSat_pre : ∃ s, (Spec.Camellia.cfbDecryptContract PPC64LE.abi 3408).pre s := by
  implies_sat [Spec.Camellia.cfbDecryptContract, Spec.Camellia.cfbSig, Spec.Camellia.cfbPre,
    Spec.Camellia.cfbDecryptPost, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

/-- An implementation `c` of CBC encryption updating the chaining value,
proved with its working space as an argument and no stack, in its frame. -/
theorem cbcEnc_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Camellia.cbcEncChainedScratchContract PPC64LE.abi 422)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 c)
      (Spec.Camellia.cbcEncryptChainedContract PPC64LE.abi 3408) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Camellia.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 422) (pre := Proof.Camellia.cbcChainedPre PPC64LE.abi.ptrBits)
    (post := Proof.Camellia.cbcEncChainedPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3408) (words := 422) (by rw [← Proof.Camellia.cbcEncChainedScratchContract_eq]; exact h)
    (by decide) (by decide) (by decide) (Proof.Camellia.cbcChainedPre_local _)
    (Proof.Camellia.cbcEncChainedPost_local _) (Proof.Camellia.cbcEncChainedPostOut_local _) cbcEncFrameSat_pre

/-- CBC decryption updating the chaining value, in its frame. -/
theorem cbcDec_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Camellia.cbcDecChainedScratchContract PPC64LE.abi 422)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 c)
      (Spec.Camellia.cbcDecryptChainedContract PPC64LE.abi 3408) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Camellia.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 422) (pre := Proof.Camellia.cbcChainedPre PPC64LE.abi.ptrBits)
    (post := Proof.Camellia.cbcDecChainedPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3408) (words := 422) (by rw [← Proof.Camellia.cbcDecChainedScratchContract_eq]; exact h)
    (by decide) (by decide) (by decide) (Proof.Camellia.cbcChainedPre_local _)
    (Proof.Camellia.cbcDecChainedPost_local _) (Proof.Camellia.cbcDecChainedPostOut_local _) cbcDecFrameSat_pre

/-- OFB, in its frame. -/
theorem ofb_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Camellia.ofbScratchContract PPC64LE.abi 422)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 c)
      (Spec.Camellia.ofbContract PPC64LE.abi 3408) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Camellia.ofbSig) (nm := "scratch") (e := .u64)
    (n := 422) (pre := Spec.Camellia.ofbPre PPC64LE.abi.ptrBits)
    (post := Spec.Camellia.ofbPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3408) (words := 422) (by rw [← Proof.Camellia.ofbScratchContract_eq]; exact h)
    (by decide) (by decide) (by decide) (Proof.Camellia.ofbPre_local _)
    (Proof.Camellia.ofbPost_local _) (Proof.Camellia.ofbPostOut_local _) ofbFrameSat_pre

/-- CFB128 encryption, in its frame. -/
theorem cfbEnc_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Camellia.cfbEncScratchContract PPC64LE.abi 422)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 c)
      (Spec.Camellia.cfbEncryptContract PPC64LE.abi 3408) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Camellia.cfbSig) (nm := "scratch") (e := .u64)
    (n := 422) (pre := Spec.Camellia.cfbPre PPC64LE.abi.ptrBits)
    (post := Spec.Camellia.cfbEncryptPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3408) (words := 422) (by rw [← Proof.Camellia.cfbEncScratchContract_eq]; exact h)
    (by decide) (by decide) (by decide) (Proof.Camellia.cfbPre_local _)
    (Proof.Camellia.cfbEncryptPost_local _) (Proof.Camellia.cfbEncryptPostOut_local _) cfbEncFrameSat_pre

/-- CFB128 decryption, in its frame. -/
theorem cfbDec_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Camellia.cfbDecScratchContract PPC64LE.abi 422)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 c)
      (Spec.Camellia.cfbDecryptContract PPC64LE.abi 3408) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Camellia.cfbSig) (nm := "scratch") (e := .u64)
    (n := 422) (pre := Spec.Camellia.cfbPre PPC64LE.abi.ptrBits)
    (post := Spec.Camellia.cfbDecryptPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3408) (words := 422) (by rw [← Proof.Camellia.cfbDecScratchContract_eq]; exact h)
    (by decide) (by decide) (by decide) (Proof.Camellia.cfbPre_local _)
    (Proof.Camellia.cfbDecryptPost_local _) (Proof.Camellia.cfbDecryptPostOut_local _) cfbDecFrameSat_pre

theorem ctrFrameSat_pre : ∃ s, (Spec.Camellia.ctrContract PPC64LE.abi 3408).pre s := by
  implies_sat [Spec.Camellia.ctrContract, Spec.Camellia.ctrSig, Spec.Camellia.ctrPre,
    Spec.Camellia.ctrPost, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

/-- CTR, in its frame. -/
theorem ctr_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Camellia.ctrScratchContract PPC64LE.abi 422)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3408 .r8 422 c)
      (Spec.Camellia.ctrContract PPC64LE.abi 3408) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Camellia.ctrSig) (nm := "scratch") (e := .u64)
    (n := 422) (pre := Spec.Camellia.ctrPre PPC64LE.abi.ptrBits)
    (post := Spec.Camellia.ctrPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3408) (words := 422) (by rw [← Proof.Camellia.ctrScratchContract_eq]; exact h)
    (by decide) (by decide) (by decide) (Proof.Camellia.ctrPre_local _)
    (Proof.Camellia.ctrPost_local _) (Proof.Camellia.ctrPostOut_local _) ctrFrameSat_pre

end VG.Proof.Camellia.PPC64LE
