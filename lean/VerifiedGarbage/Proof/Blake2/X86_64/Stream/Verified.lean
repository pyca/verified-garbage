import VerifiedGarbage.Proof.Blake2.X86_64.Compress
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Init
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Update
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Finalize
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# Streaming BLAKE2 on x86-64: `Verified`

Correctness (from `Init`, `Update` and `Finalize`, with the compression
function of `Proof/Blake2/X86_64/Compress.lean`), constant time (from `CT`),
and a state satisfying each precondition, for BLAKE2b and BLAKE2s.
-/

namespace VG.Proof.Blake2.X86_64.Stream

open VG VG.X86_64 VG.Spec.Blake2

theorem calleeB : CalleeOk b (Impl.Blake2.X86_64.compress b) :=
  CalleeOk.of_verified Proof.Blake2.X86_64.compressB_correct (by lit_decide) (by lit_decide)

theorem calleeS : CalleeOk s (Impl.Blake2.X86_64.compress s) :=
  CalleeOk.of_verified Proof.Blake2.X86_64.compressS_correct (by lit_decide) (by lit_decide)

/-! ## States satisfying the preconditions -/

/-- `init` for BLAKE2b, with no key. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1 | .rdx => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 192⟩]

/-- `update`, with no data, for `w`-bit words. -/
def updateSat (w : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, bufOff w + blockBytes w⟩, ⟨0x3000, 576⟩]

/-- `finalize`, for `w`-bit words. -/
def finalizeSat (w : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, bufOff w + blockBytes w⟩, ⟨0x2000, bufOff w⟩, ⟨0x3000, 576⟩]

/-! ## BLAKE2b -/

theorem initB_correct (st : State) (hs : (initX86_64 b).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.X86_64.Stream.init b) st t s' ∧ abiPreserved st s' ∧
      (initX86_64 b).post st s' := by
  obtain ⟨t, s', he, h⟩ := Init.correct okB hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem updateB_correct (st : State) (hs : (updateX86_64 b).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.X86_64.Stream.update b) st t s' ∧ abiPreserved st s' ∧
      (updateX86_64 b).post st s' := by
  obtain ⟨t, s', he, h⟩ := Update.correct (callee := Impl.Blake2.X86_64.Stream.scalar b) okB calleeB (Update.pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem finalizeB_correct (st : State) (hs : (finalizeX86_64 b).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.X86_64.Stream.finalize b) st t s' ∧ abiPreserved st s' ∧
      (finalizeX86_64 b).post st s' := by
  obtain ⟨t, s', he, h⟩ := Finalize.correct (callee := Impl.Blake2.X86_64.Stream.scalar b) okB calleeB hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem initB_verified :
    Verified X86_64.target (Impl.Blake2.X86_64.Stream.init b) (Spec.Blake2.initBContract X86_64.abi) :=
  Verified.of_correct initB_correct initB_ct (by
    contract_implies [Spec.Blake2.initBContract, Spec.Blake2.initBSig, Proof.Blake2.initX86_64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes,
      X86_64.abi, X86_64.argRegs] [initSat] using initSat)

theorem updateB_verified :
    Verified X86_64.target (Impl.Blake2.X86_64.Stream.update b)
      (Spec.Blake2.updateBScratchContract X86_64.abi 8) :=
  Verified.of_correct updateB_correct updateB_ct (by
    sig_implies [Spec.Blake2.updateBScratchContract, Spec.Blake2.updateBScratchSig, Proof.Blake2.updateX86_64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, X86_64.abi, X86_64.argRegs]
      [updateSat] using updateSat 64)

theorem finalizeB_verified :
    Verified X86_64.target (Impl.Blake2.X86_64.Stream.finalize b)
      (Spec.Blake2.finalizeBScratchContract X86_64.abi 8) :=
  Verified.of_correct finalizeB_correct finalizeB_ct (by
    sig_implies [Spec.Blake2.finalizeBScratchContract, Spec.Blake2.finalizeBScratchSig,
      Proof.Blake2.finalizeX86_64, Spec.Blake2.bufOff, Spec.Blake2.blockBytes, X86_64.abi,
      X86_64.argRegs]
      [finalizeSat] using finalizeSat 64)

/-! ## BLAKE2s -/

/-- `init` for BLAKE2s, with no key. -/
def initSatS : State := { initSat with wr := [⟨0x1000, 96⟩] }


theorem initS_correct (st : State) (hs : (initX86_64 s).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.X86_64.Stream.init s) st t s' ∧ abiPreserved st s' ∧
      (initX86_64 s).post st s' := by
  obtain ⟨t, s', he, h⟩ := Init.correct okS hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem updateS_correct (st : State) (hs : (updateX86_64 s).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.X86_64.Stream.update s) st t s' ∧ abiPreserved st s' ∧
      (updateX86_64 s).post st s' := by
  obtain ⟨t, s', he, h⟩ := Update.correct (callee := Impl.Blake2.X86_64.Stream.scalar s) okS calleeS (Update.pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem finalizeS_correct (st : State) (hs : (finalizeX86_64 s).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.X86_64.Stream.finalize s) st t s' ∧ abiPreserved st s' ∧
      (finalizeX86_64 s).post st s' := by
  obtain ⟨t, s', he, h⟩ := Finalize.correct (callee := Impl.Blake2.X86_64.Stream.scalar s) okS calleeS hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem initS_verified :
    Verified X86_64.target (Impl.Blake2.X86_64.Stream.init s) (Spec.Blake2.initSContract X86_64.abi) :=
  Verified.of_correct initS_correct initS_ct (by
    contract_implies [Spec.Blake2.initSContract, Spec.Blake2.initSSig, Proof.Blake2.initX86_64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes,
      X86_64.abi, X86_64.argRegs] [initSatS] using initSatS)

theorem updateS_verified :
    Verified X86_64.target (Impl.Blake2.X86_64.Stream.update s)
      (Spec.Blake2.updateSScratchContract X86_64.abi 8) :=
  Verified.of_correct updateS_correct updateS_ct (by
    sig_implies [Spec.Blake2.updateSScratchContract, Spec.Blake2.updateSScratchSig, Proof.Blake2.updateX86_64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, X86_64.abi, X86_64.argRegs]
      [updateSat] using updateSat 32)

theorem finalizeS_verified :
    Verified X86_64.target (Impl.Blake2.X86_64.Stream.finalize s)
      (Spec.Blake2.finalizeSScratchContract X86_64.abi 8) :=
  Verified.of_correct finalizeS_correct finalizeS_ct (by
    sig_implies [Spec.Blake2.finalizeSScratchContract, Spec.Blake2.finalizeSScratchSig,
      Proof.Blake2.finalizeX86_64, Spec.Blake2.bufOff, Spec.Blake2.blockBytes, X86_64.abi,
      X86_64.argRegs]
      [finalizeSat] using finalizeSat 32)

/-! ## `update` and `finalize` with their working space in a frame of their own

The theorems above are of the streaming functions with their working space
as an argument (`update_scratch`, `finalize_scratch`); `update` and
`finalize` run them in a frame that allocates it (`Verified.stackScratch`).
-/

theorem updateS_framed : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratch 584 .r8 (Impl.Blake2.X86_64.Stream.update s))
    (Spec.Blake2.updateSContract X86_64.abi (8 + 584)) :=
  X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 72) (stack := 8) (bytes := 584)
    updateS_verified (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalizeS_framed : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratch 584 .rcx (Impl.Blake2.X86_64.Stream.finalize s))
    (Spec.Blake2.finalizeSContract X86_64.abi (8 + 584)) :=
  X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 72) (stack := 8) (bytes := 584)
    finalizeS_verified (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Blake2.X86_64.Stream
