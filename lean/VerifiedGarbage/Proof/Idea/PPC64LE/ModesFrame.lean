module

public import VerifiedGarbage.Proof.Idea.CbcScratch
public import VerifiedGarbage.Proof.Idea.FbScratch
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.Idea.Cfb
public import VerifiedGarbage.Spec.Idea.Ofb
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# IDEA's modes on PPC64LE, with their working space on the stack

Each mode runs its code, proved with the working space as an argument, in a
frame that allocates it and zeroes it after the code
(`Verified.stackScratchWiped`), since it holds a block of data and the chaining
value: 96 bytes, the frame's 32-byte header and
the 64 of working space. The code uses no other stack: it calls nothing.
-/

@[expose] public section

namespace VG.Proof.Idea.PPC64LE

open VG VG.PPC64LE

/-- A state satisfying the modes' precondition, without the working space:
the schedule at `0x1000`, the IV at `0x3000` and no data at `0x4000`. -/
def modeFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r5 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 0⟩]

theorem cbcFrameSat_pre (post : Spec.Idea.cbcChainedSig.Post PPC64LE.abi.ptrBits) :
    ∃ s, (Spec.Idea.cbcChainedSig.contract PPC64LE.abi (post := post) (writeArgs := true)
      (stack := 0 + 96)).pre s := by
  implies_sat [Spec.Idea.cbcChainedSig, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

theorem fbFrameSat_pre (post : Spec.Idea.ofbSig.Post PPC64LE.abi.ptrBits) :
    ∃ s, (Spec.Idea.ofbSig.contract PPC64LE.abi (post := post) (writeArgs := true)
      (stack := 0 + 96)).pre s := by
  implies_sat [Spec.Idea.ofbSig, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

/-- An implementation `c` of CBC encryption updating the chaining value,
proved with its working space as an argument and no stack, in its frame. -/
theorem cbcEnc_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Idea.cbcEncChainedScratchContract PPC64LE.abi 8)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 c)
      (Spec.Idea.cbcEncryptChainedContract PPC64LE.abi 96) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Idea.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 8) (post := Proof.Idea.cbcEncChainedPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 96) (words := 8) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Idea.cbcEncChainedPost_local _) (Proof.Idea.cbcEncChainedPostOut_local _) (cbcFrameSat_pre _)

/-- CBC decryption updating the chaining value, in its frame. -/
theorem cbcDec_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Idea.cbcDecChainedScratchContract PPC64LE.abi 8)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 c)
      (Spec.Idea.cbcDecryptChainedContract PPC64LE.abi 96) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Idea.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 8) (post := Proof.Idea.cbcDecChainedPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 96) (words := 8) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Idea.cbcDecChainedPost_local _) (Proof.Idea.cbcDecChainedPostOut_local _) (cbcFrameSat_pre _)

/-- OFB, in its frame. -/
theorem ofb_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Idea.fbScratchContract PPC64LE.abi 8 Proof.Idea.ofbPost)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 c)
      (Spec.Idea.ofbContract PPC64LE.abi 96) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Idea.ofbSig) (nm := "scratch") (e := .u64)
    (n := 8) (post := Proof.Idea.ofbPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 96) (words := 8) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Idea.ofbPost_local _) (Proof.Idea.ofbPostOut_local _) (fbFrameSat_pre _)

/-- CFB64 encryption, in its frame. -/
theorem cfbEnc_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Idea.fbScratchContract PPC64LE.abi 8 Proof.Idea.cfbEncPost)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 c)
      (Spec.Idea.cfbEncryptContract PPC64LE.abi 96) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Idea.cfbSig) (nm := "scratch") (e := .u64)
    (n := 8) (post := Proof.Idea.cfbEncPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 96) (words := 8) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Idea.cfbEncPost_local _) (Proof.Idea.cfbEncPostOut_local _) (fbFrameSat_pre _)

/-- CFB64 decryption, in its frame. -/
theorem cfbDec_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Idea.fbScratchContract PPC64LE.abi 8 Proof.Idea.cfbDecPost)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 c)
      (Spec.Idea.cfbDecryptContract PPC64LE.abi 96) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Idea.cfbSig) (nm := "scratch") (e := .u64)
    (n := 8) (post := Proof.Idea.cfbDecPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 96) (words := 8) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Idea.cfbDecPost_local _) (Proof.Idea.cfbDecPostOut_local _) (fbFrameSat_pre _)

end VG.Proof.Idea.PPC64LE
