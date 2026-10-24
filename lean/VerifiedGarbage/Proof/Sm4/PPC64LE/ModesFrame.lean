module

public import VerifiedGarbage.Proof.Sm4.CbcScratch
public import VerifiedGarbage.Proof.Sm4.FbScratch
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.Sm4.Cfb
public import VerifiedGarbage.Spec.Sm4.Ofb
public import VerifiedGarbage.Spec.Sm4.Cbc
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# SM4's modes on PPC64LE, with their working space on the stack

Each mode runs its code, proved with the working space as an argument, in a
frame that allocates it and zeroes it after the code
(`Verified.stackScratchWiped`), since it holds the data's blocks, the prepared
functions' saved registers, the round keys' table and the chaining value:
3296 bytes, the frame's 32-byte header and the 3264 of working space (408
words). The code uses no other stack: the mode saves the return address in
the working space before its calls.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE

/-- A state satisfying the modes' precondition, without the working space:
the schedule at `0x1000`, the IV at `0x2000` and no data at `0x3000`. -/
def modeFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩]

theorem cbcFrameSat_pre (post : Spec.Sm4.cbcChainedSig.Post PPC64LE.abi.ptrBits) :
    ∃ s, (Spec.Sm4.cbcChainedSig.contract PPC64LE.abi (post := post) (writeArgs := true)
      (stack := 0 + 3296)).pre s := by
  implies_sat [Spec.Sm4.cbcChainedSig, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

theorem fbFrameSat_pre (post : Spec.Sm4.ofbSig.Post PPC64LE.abi.ptrBits) :
    ∃ s, (Spec.Sm4.ofbSig.contract PPC64LE.abi (post := post) (writeArgs := true)
      (stack := 0 + 3296)).pre s := by
  implies_sat [Spec.Sm4.ofbSig, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

/-- An implementation `c` of CBC encryption updating the chaining value,
proved with its working space as an argument and no stack, in its frame. -/
theorem cbcEnc_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Sm4.cbcEncChainedScratchContract PPC64LE.abi 408)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 c)
      (Spec.Sm4.cbcEncryptChainedContract PPC64LE.abi 3296) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Sm4.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 408) (post := Proof.Sm4.cbcEncChainedPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3296) (words := 408) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.cbcEncChainedPost_local _) (Proof.Sm4.cbcEncChainedPostOut_local _) (cbcFrameSat_pre _)

/-- CBC decryption updating the chaining value, in its frame. -/
theorem cbcDec_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Sm4.cbcDecChainedScratchContract PPC64LE.abi 408)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 c)
      (Spec.Sm4.cbcDecryptChainedContract PPC64LE.abi 3296) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Sm4.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 408) (post := Proof.Sm4.cbcDecChainedPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3296) (words := 408) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.cbcDecChainedPost_local _) (Proof.Sm4.cbcDecChainedPostOut_local _) (cbcFrameSat_pre _)

/-- OFB, in its frame. -/
theorem ofb_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Sm4.fbScratchContract PPC64LE.abi 408 Proof.Sm4.ofbPost)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 c)
      (Spec.Sm4.ofbContract PPC64LE.abi 3296) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Sm4.ofbSig) (nm := "scratch") (e := .u64)
    (n := 408) (post := Proof.Sm4.ofbPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3296) (words := 408) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.ofbPost_local _) (Proof.Sm4.ofbPostOut_local _) (fbFrameSat_pre _)

/-- CFB128 encryption, in its frame. -/
theorem cfbEnc_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Sm4.fbScratchContract PPC64LE.abi 408 Proof.Sm4.cfbEncPost)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 c)
      (Spec.Sm4.cfbEncryptContract PPC64LE.abi 3296) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Sm4.cfbSig) (nm := "scratch") (e := .u64)
    (n := 408) (post := Proof.Sm4.cfbEncPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3296) (words := 408) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.cfbEncPost_local _) (Proof.Sm4.cfbEncPostOut_local _) (fbFrameSat_pre _)

/-- CFB128 decryption, in its frame. -/
theorem cfbDec_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Sm4.fbScratchContract PPC64LE.abi 408 Proof.Sm4.cfbDecPost)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3296 .r7 408 c)
      (Spec.Sm4.cfbDecryptContract PPC64LE.abi 3296) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Sm4.cfbSig) (nm := "scratch") (e := .u64)
    (n := 408) (post := Proof.Sm4.cfbDecPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3296) (words := 408) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.cfbDecPost_local _) (Proof.Sm4.cfbDecPostOut_local _) (fbFrameSat_pre _)

end VG.Proof.Sm4.PPC64LE
