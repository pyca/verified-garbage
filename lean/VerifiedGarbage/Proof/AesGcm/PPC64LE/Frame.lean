module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Verified
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch

/-!
# AES-GCM on PPC64LE, with its working space on the stack

Each function runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame of 2592 bytes that allocates it
(`Verified.stackScratch`): its arguments all arrive in registers, the
working space in the next one.
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE

/-- A state satisfying `vg_aes_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩]

theorem initFrameSat_pre : ∃ s, (Spec.Gcm.initContract PPC64LE.abi 2592).pre s := by
  implies_sat [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
    PPC64LE.abi, PPC64LE.argRegs] [initFrameSat] using initFrameSat

theorem init_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r6 init)
      (Spec.Gcm.initContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre PPC64LE.abi.ptrBits) (post := Spec.Gcm.initPost PPC64LE.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2592) init_verified (by decide) (by decide)
    (Proof.AesGcm.initPre_local _) (Proof.AesGcm.initPost_local _) initFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩]

theorem streamInitFrameSat_pre : ∃ s, (Spec.Gcm.streamInitContract PPC64LE.abi 2592).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    PPC64LE.abi, PPC64LE.argRegs] [streamInitFrameSat] using streamInitFrameSat

theorem streamInit_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r7 streamInit)
      (Spec.Gcm.streamInitContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamInitPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamInit_verified (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.AesGcm.streamInitPost_local _)
    streamInitFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x3000 | .r6 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩]
  wr := [⟨0x3000, 80⟩]

theorem streamAadFrameSat_pre : ∃ s, (Spec.Gcm.streamAadContract PPC64LE.abi 2592).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    PPC64LE.abi, PPC64LE.argRegs] [streamAadFrameSat] using streamAadFrameSat

theorem streamAad_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratch 2592 .r8 streamAad)
      (Spec.Gcm.streamAadContract PPC64LE.abi 2592) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamAadPost PPC64LE.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2592) streamAad_verified (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.AesGcm.streamAadPost_local _)
    streamAadFrameSat_pre

end VG.Proof.AesGcm.PPC64LE
