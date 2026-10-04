import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# BLAKE2s compression backends on x86-64

As for BLAKE2b (`Backend.lean`): the streaming functions are proved once for
an arbitrary compression callee, and a backend supplies its compression
function with its proof, and the constant-time and instruction-property
certificates of the streaming code that calls it. The generic registration
(`Generic/Blake2s/X86_64/Stream.lean`) emits those callers with the
backend's suffix.
-/

namespace VG.Proof.Blake2.X86_64

open VG VG.X86_64
open VG.Spec.Blake2 (s)

structure BackendS where
  suffix : String
  features : List String
  code : Prog isa
  callee : Stream.CalleeOk s code
  verified : Verified X86_64.target code (Spec.Blake2.compressSContract abi)
  spSafe : code.all (fun i => !isa.writesSp i) = true
  updateCT : ConstantTime isa (updateX86_64 s).pre (updateX86_64 s).pub
    (Impl.Blake2.X86_64.Stream.update s ⟨Spec.Blake2.compressSApi.name ++ suffix, code⟩)
  finalizeCT : ConstantTime isa (finalizeX86_64 s).pre (finalizeX86_64 s).pub
    (Impl.Blake2.X86_64.Stream.finalize s ⟨Spec.Blake2.compressSApi.name ++ suffix, code⟩)
  updateMxcsr : (Impl.Blake2.X86_64.Stream.update s
    ⟨Spec.Blake2.compressSApi.name ++ suffix, code⟩).allInstrs (fun i => !loadsMxcsr i) = true
  finalizeMxcsr : (Impl.Blake2.X86_64.Stream.finalize s
    ⟨Spec.Blake2.compressSApi.name ++ suffix, code⟩).allInstrs (fun i => !loadsMxcsr i) = true
  updateSpSafe : (Impl.Blake2.X86_64.Stream.update s
    ⟨Spec.Blake2.compressSApi.name ++ suffix, code⟩).all (fun i => !isa.writesSp i) = true
  finalizeSpSafe : (Impl.Blake2.X86_64.Stream.finalize s
    ⟨Spec.Blake2.compressSApi.name ++ suffix, code⟩).all (fun i => !isa.writesSp i) = true
  /-- The stack the streaming functions use, so that `update` and `finalize`
  can keep their working space in a frame of their own. -/
  updateDepth : (Impl.Blake2.X86_64.Stream.update s
    ⟨Spec.Blake2.compressSApi.name ++ suffix, code⟩).x86_64Depth ≤ 8
  finalizeDepth : (Impl.Blake2.X86_64.Stream.finalize s
    ⟨Spec.Blake2.compressSApi.name ++ suffix, code⟩).x86_64Depth ≤ 8

namespace BackendS

def compressName (v : BackendS) : String := Spec.Blake2.compressSApi.name ++ v.suffix

def hashCallee (v : BackendS) : Impl.Blake2.X86_64.Stream.Callee := ⟨v.compressName, v.code⟩
def update (v : BackendS) : Prog isa := Impl.Blake2.X86_64.Stream.update s v.hashCallee
def finalize (v : BackendS) : Prog isa := Impl.Blake2.X86_64.Stream.finalize s v.hashCallee

theorem update_correct (v : BackendS) (st : State) (hs : (updateX86_64 s).pre st) :
    ∃ t s', Exec isa v.update st t s' ∧ abiPreserved st s' ∧ (updateX86_64 s).post st s' := by
  obtain ⟨t, s', he, h⟩ := Stream.Update.correct (callee := v.hashCallee) Stream.okS v.callee
    (Stream.Update.pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec v.updateMxcsr he h.1, h.2⟩

theorem finalize_correct (v : BackendS) (st : State) (hs : (finalizeX86_64 s).pre st) :
    ∃ t s', Exec isa v.finalize st t s' ∧ abiPreserved st s' ∧ (finalizeX86_64 s).post st s' := by
  obtain ⟨t, s', he, h⟩ := Stream.Finalize.correct (callee := v.hashCallee) Stream.okS v.callee hs
  exact ⟨t, s', he, abiPreserved_of_exec v.finalizeMxcsr he h.1, h.2⟩

theorem update_verified (v : BackendS) :
    Verified X86_64.target v.update (Spec.Blake2.updateSScratchContract abi 8) :=
  Verified.of_correct v.update_correct v.updateCT (by
    sig_implies [Spec.Blake2.updateSScratchContract, Spec.Blake2.updateSScratchSig, Proof.Blake2.updateX86_64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, X86_64.abi, X86_64.argRegs]
      [Stream.updateSat] using Stream.updateSat 32)

theorem finalize_verified (v : BackendS) :
    Verified X86_64.target v.finalize (Spec.Blake2.finalizeSScratchContract abi 8) :=
  Verified.of_correct v.finalize_correct v.finalizeCT (by
    sig_implies [Spec.Blake2.finalizeSScratchContract, Spec.Blake2.finalizeSScratchSig,
      Proof.Blake2.finalizeX86_64, Spec.Blake2.bufOff, Spec.Blake2.blockBytes, X86_64.abi,
      X86_64.argRegs] [Stream.finalizeSat] using Stream.finalizeSat 32)

/-- `update`: the streaming code with its working space in a frame of its own. -/
theorem update_framed (v : BackendS) : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratch 584 .r8 v.update)
    (Spec.Blake2.updateSContract abi (8 + 584)) :=
  X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 72) (stack := 8) (bytes := 584)
    v.update_verified (by decide) (by decide) (by decide) v.updateSpSafe v.updateDepth
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- `finalize`: the streaming code with its working space in a frame of its own. -/
theorem finalize_framed (v : BackendS) : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratch 584 .rcx v.finalize)
    (Spec.Blake2.finalizeSContract abi (8 + 584)) :=
  X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 72) (stack := 8) (bytes := 584)
    v.finalize_verified (by decide) (by decide) (by decide) v.finalizeSpSafe v.finalizeDepth
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end BackendS
end VG.Proof.Blake2.X86_64
