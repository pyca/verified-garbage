module

public import VerifiedGarbage.Proof.Blowfish.CbcScratch
public import VerifiedGarbage.Proof.Blowfish.FbScratch
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.Blowfish.Cfb
public import VerifiedGarbage.Spec.Blowfish.Ofb
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Blowfish's modes on PPC64LE, with their working space on the stack

Each mode runs its code, proved with the working space as an argument, in a
frame that allocates it and zeroes it after the code
(`Verified.stackScratchWiped`), since it holds a block of data, the chaining
value and our caller's registers: 128 bytes, the frame's 32-byte header and
the 96 of working space. The code uses no other stack: it calls nothing.
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE

open VG VG.PPC64LE

/-- A state satisfying the modes' precondition, without the working space:
the schedule at `0x1000`, the IV at `0x3000` and no data at `0x4000`. -/
def modeFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r5 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 0⟩]

theorem cbcFrameSat_pre (post : Spec.Blowfish.cbcChainedSig.Post PPC64LE.abi.ptrBits) :
    ∃ s, (Spec.Blowfish.cbcChainedSig.contract PPC64LE.abi (post := post) (writeArgs := true)
      (stack := 0 + 128)).pre s := by
  implies_sat [Spec.Blowfish.cbcChainedSig, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

theorem fbFrameSat_pre (post : Spec.Blowfish.ofbSig.Post PPC64LE.abi.ptrBits) :
    ∃ s, (Spec.Blowfish.ofbSig.contract PPC64LE.abi (post := post) (writeArgs := true)
      (stack := 0 + 128)).pre s := by
  implies_sat [Spec.Blowfish.ofbSig, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

/-- An implementation `c` of CBC encryption updating the chaining value,
proved with its working space as an argument and no stack, in its frame. -/
theorem cbcEnc_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Blowfish.cbcEncChainedScratchContract PPC64LE.abi 12)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 c)
      (Spec.Blowfish.cbcEncryptChainedContract PPC64LE.abi 128) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Blowfish.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 12) (post := Proof.Blowfish.cbcEncChainedPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 128) (words := 12) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Blowfish.cbcEncChainedPost_local _) (Proof.Blowfish.cbcEncChainedPostOut_local _) (cbcFrameSat_pre _)

/-- CBC decryption updating the chaining value, in its frame. -/
theorem cbcDec_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Blowfish.cbcDecChainedScratchContract PPC64LE.abi 12)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 c)
      (Spec.Blowfish.cbcDecryptChainedContract PPC64LE.abi 128) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Blowfish.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 12) (post := Proof.Blowfish.cbcDecChainedPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 128) (words := 12) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Blowfish.cbcDecChainedPost_local _) (Proof.Blowfish.cbcDecChainedPostOut_local _) (cbcFrameSat_pre _)

/-- OFB, in its frame. -/
theorem ofb_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Blowfish.fbScratchContract PPC64LE.abi 12 Proof.Blowfish.ofbPost)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 c)
      (Spec.Blowfish.ofbContract PPC64LE.abi 128) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Blowfish.ofbSig) (nm := "scratch") (e := .u64)
    (n := 12) (post := Proof.Blowfish.ofbPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 128) (words := 12) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Blowfish.ofbPost_local _) (Proof.Blowfish.ofbPostOut_local _) (fbFrameSat_pre _)

/-- CFB64 encryption, in its frame. -/
theorem cfbEnc_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Blowfish.fbScratchContract PPC64LE.abi 12 Proof.Blowfish.cfbEncPost)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 c)
      (Spec.Blowfish.cfbEncryptContract PPC64LE.abi 128) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbSig) (nm := "scratch") (e := .u64)
    (n := 12) (post := Proof.Blowfish.cfbEncPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 128) (words := 12) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Blowfish.cfbEncPost_local _) (Proof.Blowfish.cfbEncPostOut_local _) (fbFrameSat_pre _)

/-- CFB64 decryption, in its frame. -/
theorem cfbDec_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Blowfish.fbScratchContract PPC64LE.abi 12 Proof.Blowfish.cfbDecPost)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 128 .r7 12 c)
      (Spec.Blowfish.cfbDecryptContract PPC64LE.abi 128) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbSig) (nm := "scratch") (e := .u64)
    (n := 12) (post := Proof.Blowfish.cfbDecPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 128) (words := 12) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Blowfish.cfbDecPost_local _) (Proof.Blowfish.cfbDecPostOut_local _) (fbFrameSat_pre _)

end VG.Proof.Blowfish.PPC64LE
