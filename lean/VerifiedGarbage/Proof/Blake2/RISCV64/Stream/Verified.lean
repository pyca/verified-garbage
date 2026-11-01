module

public import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Common
public import VerifiedGarbage.Spec.Blake2.Contract
public import VerifiedGarbage.Proof.Blake2.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Blake2.RISCV64.Verified
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.CT
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Init
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Update
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Finalize
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit
import VerifiedGarbage.Proof.Blake2.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit
meta import VerifiedGarbage.Proof.Blake2.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Common
meta import VerifiedGarbage.Spec.Blake2.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# Streaming BLAKE2 on RISC-V: `Verified`

Correctness (from `Init`, `Update` and `Finalize`, with the compression
function of `Proof/Blake2/RISCV64/Compress.lean`), constant time (from `CT`),
and a state satisfying each precondition, for BLAKE2b and BLAKE2s. `update`
and `finalize` keep their working space in a frame of 576 bytes on the stack;
BLAKE2b's `update_scratch` and `finalize_scratch` take it as an argument and
use no stack.
-/

@[expose] public section

namespace VG.Proof.Blake2.RISCV64.Stream

open VG VG.RISCV64 VG.Spec.Blake2

theorem calleeB : CalleeOk b (Impl.Blake2.RISCV64.compress b) :=
  ⟨Proof.Blake2.RISCV64.compress_correct (z := .d) _ Proof.Blake2.RISCV64.rok_b, by lit_decide⟩

theorem calleeS : CalleeOk s (Impl.Blake2.RISCV64.compress s) :=
  ⟨Proof.Blake2.RISCV64.compress_correct (z := .w) _ Proof.Blake2.RISCV64.rok_s, by lit_decide⟩

/-! ## States satisfying the preconditions -/

/-- `init` for `w`-bit words, with no key. -/
def initSat (w : Nat) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 1 | .a2 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, bufOff w + blockBytes w⟩]

/-- `update_scratch`, with no data, for `w`-bit words. -/
def updateSat (w : Nat) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a2 => 0x2000 | .a4 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, bufOff w + blockBytes w⟩, ⟨0x3000, 576⟩]

/-- `update`, with no data, for `w`-bit words. -/
def updateFramedSat (w : Nat) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a2 => 0x2000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, bufOff w + blockBytes w⟩]

/-- `finalize_scratch`, for `w`-bit words. -/
def finalizeSat (w : Nat) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a2 => 0x2000 | .a3 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, bufOff w + blockBytes w⟩, ⟨0x2000, bufOff w⟩, ⟨0x3000, 576⟩]

/-- `finalize`, for `w`-bit words. -/
def finalizeFramedSat (w : Nat) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a2 => 0x2000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, bufOff w + blockBytes w⟩, ⟨0x2000, bufOff w⟩]

/-! ## Correctness -/

theorem init_correct {z : Size} {P : Params z.bits} (hP : Ok P) (st : State) (hs : (initRISCV64 P).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.RISCV64.Stream.init P) st t s' ∧ abiPreserved st s' ∧
      (initRISCV64 P).post st s' := by
  obtain ⟨t, s', he, h₁, hra, h₂⟩ := Init.correct hP hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, hra⟩, h₂⟩

/-! ## BLAKE2b -/

theorem initB_verified :
    Verified RISCV64.target (Impl.Blake2.RISCV64.Stream.init b)
      (Spec.Blake2.initBContract RISCV64.abi) :=
  Verified.of_correct (init_correct (z := .d) okB) initB_ct (by
    contract_implies [Spec.Blake2.initBContract, Spec.Blake2.initBSig, Proof.Blake2.initRISCV64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, Size.bits, RISCV64.abi, RISCV64.argRegs] [initSat]
      using initSat 64)

theorem updateScratchB_verified :
    Verified RISCV64.target (Impl.Blake2.RISCV64.Stream.updateScratch b)
      (Proof.Blake2.updateBScratchContract RISCV64.abi) :=
  Verified.of_correct (fun st hs => Update.correct okB calleeB hs) updateScratchB_ct (by
    sig_implies [Proof.Blake2.updateBScratchContract, Proof.Blake2.updateBScratchSig,
      Proof.Blake2.updateRISCV64, Proof.Blake2.updatePost, Spec.Blake2.updateBPost, Spec.Blake2.bufOff,
      Spec.Blake2.blockBytes, RISCV64.abi, RISCV64.argRegs]
      [updateSat] using updateSat 64)

theorem updateB_verified :
    Verified RISCV64.target (Impl.Blake2.RISCV64.Stream.update b)
      (Spec.Blake2.updateBContract RISCV64.abi 576) :=
  Verified.of_correct (fun st hs => Update.correctFramed okB calleeB hs) updateB_ct (by
    sig_implies [Spec.Blake2.updateBContract, Spec.Blake2.updateBSig,
      Proof.Blake2.updateFramedRISCV64, Proof.Blake2.updatePost, Spec.Blake2.updateBPost,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, RISCV64.abi, RISCV64.argRegs]
      [updateFramedSat] using updateFramedSat 64)

theorem finalizeScratchB_verified :
    Verified RISCV64.target (Impl.Blake2.RISCV64.Stream.finalizeScratch b)
      (Proof.Blake2.finalizeBScratchContract RISCV64.abi) :=
  Verified.of_correct (fun st hs => Finalize.correct okB calleeB hs) finalizeScratchB_ct (by
    sig_implies [Proof.Blake2.finalizeBScratchContract, Proof.Blake2.finalizeBScratchSig,
      Proof.Blake2.finalizeRISCV64, Proof.Blake2.finalizePost, Spec.Blake2.finalizeBPost,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, RISCV64.abi, RISCV64.argRegs]
      [finalizeSat] using finalizeSat 64)

theorem finalizeB_verified :
    Verified RISCV64.target (Impl.Blake2.RISCV64.Stream.finalize b)
      (Spec.Blake2.finalizeBContract RISCV64.abi 576) :=
  Verified.of_correct (fun st hs => Finalize.correctFramed okB calleeB hs) finalizeB_ct (by
    sig_implies [Spec.Blake2.finalizeBContract, Spec.Blake2.finalizeBSig,
      Proof.Blake2.finalizeFramedRISCV64, Proof.Blake2.finalizePost, Spec.Blake2.finalizeBPost,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, RISCV64.abi, RISCV64.argRegs]
      [finalizeFramedSat] using finalizeFramedSat 64)

/-! ## BLAKE2s -/

theorem initS_verified :
    Verified RISCV64.target (Impl.Blake2.RISCV64.Stream.init s)
      (Spec.Blake2.initSContract RISCV64.abi) :=
  Verified.of_correct (init_correct (z := .w) okS) initS_ct (by
    contract_implies [Spec.Blake2.initSContract, Spec.Blake2.initSSig, Proof.Blake2.initRISCV64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, Size.bits, RISCV64.abi, RISCV64.argRegs] [initSat]
      using initSat 32)

theorem updateS_verified :
    Verified RISCV64.target (Impl.Blake2.RISCV64.Stream.update s)
      (Spec.Blake2.updateSContract RISCV64.abi 576) :=
  Verified.of_correct (fun st hs => Update.correctFramed okS calleeS hs) updateS_ct (by
    sig_implies [Spec.Blake2.updateSContract, Spec.Blake2.updateSSig,
      Proof.Blake2.updateFramedRISCV64, Proof.Blake2.updatePost, Spec.Blake2.updateSPost,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, RISCV64.abi, RISCV64.argRegs]
      [updateFramedSat] using updateFramedSat 32)

theorem finalizeS_verified :
    Verified RISCV64.target (Impl.Blake2.RISCV64.Stream.finalize s)
      (Spec.Blake2.finalizeSContract RISCV64.abi 576) :=
  Verified.of_correct (fun st hs => Finalize.correctFramed okS calleeS hs) finalizeS_ct (by
    sig_implies [Spec.Blake2.finalizeSContract, Spec.Blake2.finalizeSSig,
      Proof.Blake2.finalizeFramedRISCV64, Proof.Blake2.finalizePost, Spec.Blake2.finalizeSPost,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, RISCV64.abi, RISCV64.argRegs]
      [finalizeFramedSat] using finalizeFramedSat 32)

end VG.Proof.Blake2.RISCV64.Stream
