import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# BLAKE2b compression backends on x86-64

Streaming correctness is proved once for an arbitrary compression callee.
A backend supplies constant-time and instruction-property certificates for
the streaming code that calls it. Generic registrations emit those callers
and constructions built on them with the same suffix.
-/

namespace VG.Proof.Blake2.X86_64

open VG VG.X86_64
open VG.Spec.Blake2 (b)

structure Backend where
  suffix : String
  features : List String
  code : Prog isa
  callee : Stream.CalleeOk b code
  verified : Verified X86_64.target code (Spec.Blake2.compressBContract abi)
  spSafe : code.all (fun i => !isa.writesSp i) = true
  updateCT : ConstantTime isa (updateX86_64 b).pre (updateX86_64 b).pub
    (Impl.Blake2.X86_64.Stream.update b ⟨Spec.Blake2.compressBApi.name ++ suffix, code⟩)
  finalizeCT : ConstantTime isa (finalizeX86_64 b).pre (finalizeX86_64 b).pub
    (Impl.Blake2.X86_64.Stream.finalize b ⟨Spec.Blake2.compressBApi.name ++ suffix, code⟩)
  updateMxcsr : (Impl.Blake2.X86_64.Stream.update b
    ⟨Spec.Blake2.compressBApi.name ++ suffix, code⟩).allInstrs (fun i => !loadsMxcsr i) = true
  finalizeMxcsr : (Impl.Blake2.X86_64.Stream.finalize b
    ⟨Spec.Blake2.compressBApi.name ++ suffix, code⟩).allInstrs (fun i => !loadsMxcsr i) = true
  updateSpSafe : (Impl.Blake2.X86_64.Stream.update b
    ⟨Spec.Blake2.compressBApi.name ++ suffix, code⟩).all (fun i => !isa.writesSp i) = true
  finalizeSpSafe : (Impl.Blake2.X86_64.Stream.finalize b
    ⟨Spec.Blake2.compressBApi.name ++ suffix, code⟩).all (fun i => !isa.writesSp i) = true
  /-- The stack the streaming functions use, so that `update` and `finalize`
  can keep their working space in a frame of their own. -/
  updateDepth : (Impl.Blake2.X86_64.Stream.update b
    ⟨Spec.Blake2.compressBApi.name ++ suffix, code⟩).x86_64Depth ≤ 8
  finalizeDepth : (Impl.Blake2.X86_64.Stream.finalize b
    ⟨Spec.Blake2.compressBApi.name ++ suffix, code⟩).x86_64Depth ≤ 8

namespace Backend

def compressName (v : Backend) : String := Spec.Blake2.compressBApi.name ++ v.suffix
/-- The names of `update_scratch` and `finalize_scratch`, which Argon2's code
calls. -/
def updateName (v : Backend) : String := Spec.Blake2.updateBScratchApi.name ++ v.suffix
def finalizeName (v : Backend) : String := Spec.Blake2.finalizeBScratchApi.name ++ v.suffix

def hashCallee (v : Backend) : Impl.Blake2.X86_64.Stream.Callee := ⟨v.compressName, v.code⟩
def init (_ : Backend) : Prog isa := Impl.Blake2.X86_64.Stream.init b
def update (v : Backend) : Prog isa := Impl.Blake2.X86_64.Stream.update b v.hashCallee
def finalize (v : Backend) : Prog isa := Impl.Blake2.X86_64.Stream.finalize b v.hashCallee

theorem init_verified (v : Backend) : Verified X86_64.target v.init (Spec.Blake2.initBContract abi) :=
  Stream.initB_verified

theorem update_correct (v : Backend) (st : State) (hs : (updateX86_64 b).pre st) :
    ∃ t s', Exec isa v.update st t s' ∧ abiPreserved st s' ∧ (updateX86_64 b).post st s' := by
  obtain ⟨t, s', he, h⟩ := Stream.Update.correct (callee := v.hashCallee) Stream.okB v.callee
    (Stream.Update.pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec v.updateMxcsr he h.1, h.2⟩

theorem finalize_correct (v : Backend) (st : State) (hs : (finalizeX86_64 b).pre st) :
    ∃ t s', Exec isa v.finalize st t s' ∧ abiPreserved st s' ∧ (finalizeX86_64 b).post st s' := by
  obtain ⟨t, s', he, h⟩ := Stream.Finalize.correct (callee := v.hashCallee) Stream.okB v.callee hs
  exact ⟨t, s', he, abiPreserved_of_exec v.finalizeMxcsr he h.1, h.2⟩

theorem update_verified (v : Backend) :
    Verified X86_64.target v.update (Spec.Blake2.updateBScratchContract abi 8) :=
  Verified.of_correct v.update_correct v.updateCT (by
    sig_implies [Spec.Blake2.updateBScratchContract, Spec.Blake2.updateBScratchSig, Proof.Blake2.updateX86_64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, X86_64.abi, X86_64.argRegs]
      [Stream.updateSat] using Stream.updateSat 64)

theorem finalize_verified (v : Backend) :
    Verified X86_64.target v.finalize (Spec.Blake2.finalizeBScratchContract abi 8) :=
  Verified.of_correct v.finalize_correct v.finalizeCT (by
    sig_implies [Spec.Blake2.finalizeBScratchContract, Spec.Blake2.finalizeBScratchSig,
      Proof.Blake2.finalizeX86_64, Spec.Blake2.bufOff, Spec.Blake2.blockBytes, X86_64.abi,
      X86_64.argRegs] [Stream.finalizeSat] using Stream.finalizeSat 64)

/-- `update`: `update_scratch` with its working space in a frame of its own. -/
theorem update_framed (v : Backend) : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratch 584 .r8 v.update)
    (Spec.Blake2.updateBContract abi (8 + 584)) :=
  X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 72) (stack := 8) (bytes := 584)
    v.update_verified (by decide) (by decide) (by decide) v.updateSpSafe v.updateDepth
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- `finalize`: `finalize_scratch` with its working space in a frame of its own. -/
theorem finalize_framed (v : Backend) : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratch 584 .rcx v.finalize)
    (Spec.Blake2.finalizeBContract abi (8 + 584)) :=
  X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 72) (stack := 8) (bytes := 584)
    v.finalize_verified (by decide) (by decide) (by decide) v.finalizeSpSafe v.finalizeDepth
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end Backend
end VG.Proof.Blake2.X86_64
