module

public import VerifiedGarbage.Proof.TripleDes.CbcScratch
public import VerifiedGarbage.Proof.TripleDes.FbScratch
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Spec.TripleDes.Cfb8
public import VerifiedGarbage.Spec.TripleDes.Ofb
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Triple DES's modes on PPC64LE, with their working space on the stack

Each mode runs its code, proved with the working space as an argument, in a
frame that allocates it and zeroes it after the code
(`Verified.stackScratchWiped`), since it holds the data's blocks, the block
function's saved registers and the chaining value: 608 bytes, the frame's
32-byte header and the 576 of working space. The code uses no other stack:
its calls keep the return address in the link register.
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE

/-- A state satisfying the modes' precondition, without the working space:
the schedule at `0x1000`, the IV at `0x2000` and no data at `0x3000`. -/
def modeFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩]

theorem cbcFrameSat_pre (post : Spec.TripleDes.cbcChainedSig.Post PPC64LE.abi.ptrBits) :
    ∃ s, (Spec.TripleDes.cbcChainedSig.contract PPC64LE.abi (post := post) (writeArgs := true)
      (stack := 0 + 608)).pre s := by
  implies_sat [Spec.TripleDes.cbcChainedSig, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

theorem fbFrameSat_pre (post : Spec.TripleDes.ofbSig.Post PPC64LE.abi.ptrBits) :
    ∃ s, (Spec.TripleDes.ofbSig.contract PPC64LE.abi (post := post) (writeArgs := true)
      (stack := 0 + 608)).pre s := by
  implies_sat [Spec.TripleDes.ofbSig, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

theorem cfb8FrameSat_pre (post : Spec.TripleDes.cfb8Sig.Post PPC64LE.abi.ptrBits) :
    ∃ s, (Spec.TripleDes.cfb8Sig.contract PPC64LE.abi (post := post) (writeArgs := true)
      (stack := 0 + 608)).pre s := by
  implies_sat [Spec.TripleDes.cfb8Sig, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

/-- An implementation `c` of CBC encryption updating the chaining value,
proved with its working space as an argument and no stack, in its frame. -/
theorem cbcEnc_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.TripleDes.cbcEncChainedScratchContract PPC64LE.abi 72)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 c)
      (Spec.TripleDes.cbcEncryptChainedContract PPC64LE.abi 608) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 72) (post := Proof.TripleDes.cbcEncChainedPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 608) (words := 72) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cbcEncChainedPost_local _) (Proof.TripleDes.cbcEncChainedPostOut_local _) (cbcFrameSat_pre _)

/-- CBC decryption updating the chaining value, in its frame. -/
theorem cbcDec_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.TripleDes.cbcDecChainedScratchContract PPC64LE.abi 72)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 c)
      (Spec.TripleDes.cbcDecryptChainedContract PPC64LE.abi 608) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 72) (post := Proof.TripleDes.cbcDecChainedPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 608) (words := 72) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cbcDecChainedPost_local _) (Proof.TripleDes.cbcDecChainedPostOut_local _) (cbcFrameSat_pre _)

/-- OFB, in its frame. -/
theorem ofb_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.TripleDes.fbScratchContract PPC64LE.abi 72 Proof.TripleDes.ofbPost)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 c)
      (Spec.TripleDes.ofbContract PPC64LE.abi 608) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.TripleDes.ofbSig) (nm := "scratch") (e := .u64)
    (n := 72) (post := Proof.TripleDes.ofbPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 608) (words := 72) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.ofbPost_local _) (Proof.TripleDes.ofbPostOut_local _) (fbFrameSat_pre _)

/-- CFB64 encryption, in its frame. -/
theorem cfbEnc_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.TripleDes.fbScratchContract PPC64LE.abi 72 Proof.TripleDes.cfbEncPost)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 c)
      (Spec.TripleDes.cfbEncryptContract PPC64LE.abi 608) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbSig) (nm := "scratch") (e := .u64)
    (n := 72) (post := Proof.TripleDes.cfbEncPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 608) (words := 72) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cfbEncPost_local _) (Proof.TripleDes.cfbEncPostOut_local _) (fbFrameSat_pre _)

/-- CFB64 decryption, in its frame. -/
theorem cfbDec_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.TripleDes.fbScratchContract PPC64LE.abi 72 Proof.TripleDes.cfbDecPost)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 c)
      (Spec.TripleDes.cfbDecryptContract PPC64LE.abi 608) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbSig) (nm := "scratch") (e := .u64)
    (n := 72) (post := Proof.TripleDes.cfbDecPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 608) (words := 72) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cfbDecPost_local _) (Proof.TripleDes.cfbDecPostOut_local _) (fbFrameSat_pre _)

/-- CFB8 encryption, in its frame. -/
theorem cfb8Enc_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.TripleDes.cfb8ScratchContract PPC64LE.abi 72 Proof.TripleDes.cfb8EncPost)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 c)
      (Spec.TripleDes.cfb8EncryptContract PPC64LE.abi 608) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.TripleDes.cfb8Sig) (nm := "scratch") (e := .u64)
    (n := 72) (post := Proof.TripleDes.cfb8EncPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 608) (words := 72) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cfb8EncPost_local _) (Proof.TripleDes.cfb8EncPostOut_local _) (cfb8FrameSat_pre _)

/-- CFB8 decryption, in its frame. -/
theorem cfb8Dec_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.TripleDes.cfb8ScratchContract PPC64LE.abi 72 Proof.TripleDes.cfb8DecPost)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 608 .r7 72 c)
      (Spec.TripleDes.cfb8DecryptContract PPC64LE.abi 608) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.TripleDes.cfb8Sig) (nm := "scratch") (e := .u64)
    (n := 72) (post := Proof.TripleDes.cfb8DecPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 608) (words := 72) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cfb8DecPost_local _) (Proof.TripleDes.cfb8DecPostOut_local _) (cfb8FrameSat_pre _)

end VG.Proof.TripleDes.PPC64LE
