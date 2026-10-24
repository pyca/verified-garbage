module

public import VerifiedGarbage.Proof.Seed.CbcScratch
public import VerifiedGarbage.Proof.Seed.FbScratch
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.Seed.Cfb
public import VerifiedGarbage.Spec.Seed.Ofb
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# SEED's modes on PPC64LE, with their working space on the stack

Each mode runs its code, proved with the working space as an argument, in a
frame that allocates it and zeroes it after the code
(`Verified.stackScratchWiped`), since it holds the caller's registers, a block of data and the chaining
value: 1136 bytes, the frame's 32-byte header and the 1104 of working space.
The code uses no other stack: it calls nothing.
-/

@[expose] public section

namespace VG.Proof.Seed.PPC64LE

open VG VG.PPC64LE

/-- A state satisfying the modes' precondition, without the working space:
the schedule at `0x1000`, the IV at `0x3000` and no data at `0x4000`. -/
def modeFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r5 => 0x4000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 16⟩, ⟨0x4000, 0⟩]

theorem cbcFrameSat_pre (post : Spec.Seed.cbcChainedSig.Post PPC64LE.abi.ptrBits) :
    ∃ s, (Spec.Seed.cbcChainedSig.contract PPC64LE.abi (post := post) (writeArgs := true)
      (stack := 0 + 1136)).pre s := by
  implies_sat [Spec.Seed.cbcChainedSig, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

theorem fbFrameSat_pre (post : Spec.Seed.ofbSig.Post PPC64LE.abi.ptrBits) :
    ∃ s, (Spec.Seed.ofbSig.contract PPC64LE.abi (post := post) (writeArgs := true)
      (stack := 0 + 1136)).pre s := by
  implies_sat [Spec.Seed.ofbSig, PPC64LE.abi, PPC64LE.argRegs] [modeFrameSat] using modeFrameSat

/-- An implementation `c` of CBC encryption updating the chaining value,
proved with its working space as an argument and no stack, in its frame. -/
theorem cbcEnc_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Seed.cbcEncChainedScratchContract PPC64LE.abi 138)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 1136 .r7 138 c)
      (Spec.Seed.cbcEncryptChainedContract PPC64LE.abi 1136) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Seed.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 138) (post := Proof.Seed.cbcEncChainedPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1136) (words := 138) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Seed.cbcEncChainedPost_local _) (Proof.Seed.cbcEncChainedPostOut_local _) (cbcFrameSat_pre _)

/-- CBC decryption updating the chaining value, in its frame. -/
theorem cbcDec_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Seed.cbcDecChainedScratchContract PPC64LE.abi 138)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 1136 .r7 138 c)
      (Spec.Seed.cbcDecryptChainedContract PPC64LE.abi 1136) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Seed.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 138) (post := Proof.Seed.cbcDecChainedPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1136) (words := 138) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Seed.cbcDecChainedPost_local _) (Proof.Seed.cbcDecChainedPostOut_local _) (cbcFrameSat_pre _)

/-- OFB, in its frame. -/
theorem ofb_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Seed.fbScratchContract PPC64LE.abi 138 Proof.Seed.ofbPost)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 1136 .r7 138 c)
      (Spec.Seed.ofbContract PPC64LE.abi 1136) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Seed.ofbSig) (nm := "scratch") (e := .u64)
    (n := 138) (post := Proof.Seed.ofbPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1136) (words := 138) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Seed.ofbPost_local _) (Proof.Seed.ofbPostOut_local _) (fbFrameSat_pre _)

/-- CFB128 encryption, in its frame. -/
theorem cfbEnc_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Seed.fbScratchContract PPC64LE.abi 138 Proof.Seed.cfbEncPost)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 1136 .r7 138 c)
      (Spec.Seed.cfbEncryptContract PPC64LE.abi 1136) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Seed.cfbSig) (nm := "scratch") (e := .u64)
    (n := 138) (post := Proof.Seed.cfbEncPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1136) (words := 138) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Seed.cfbEncPost_local _) (Proof.Seed.cfbEncPostOut_local _) (fbFrameSat_pre _)

/-- CFB128 decryption, in its frame. -/
theorem cfbDec_framed {c : Prog isa}
    (h : Verified PPC64LE.target c (Proof.Seed.fbScratchContract PPC64LE.abi 138 Proof.Seed.cfbDecPost)) :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 1136 .r7 138 c)
      (Spec.Seed.cfbDecryptContract PPC64LE.abi 1136) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Seed.cfbSig) (nm := "scratch") (e := .u64)
    (n := 138) (post := Proof.Seed.cfbDecPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1136) (words := 138) h (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Seed.cfbDecPost_local _) (Proof.Seed.cfbDecPostOut_local _) (fbFrameSat_pre _)

end VG.Proof.Seed.PPC64LE
