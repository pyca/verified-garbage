module

import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Sm3.X86_64.Compress
import VerifiedGarbage.Proof.Sm3.X86_64.Stream.Init
public import VerifiedGarbage.Proof.Sm3.Scratch
public import VerifiedGarbage.Impl.Sm3.X86_64.Stream
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Sm3.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
public import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
import VerifiedGarbage.Proof.MdStream.X86_64.Words
public import VerifiedGarbage.Proof.Sm3.Md
meta import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
meta import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
meta import VerifiedGarbage.Proof.MdStream.X86_64.Words
meta import VerifiedGarbage.Proof.Sm3.Md
meta import VerifiedGarbage.Proof.Sm3.X86_64.Compress
meta import VerifiedGarbage.Impl.Sm3.X86_64.Stream
meta import VerifiedGarbage.Proof.Sm3.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Sm3.X86_64.Stream.Md`, which only this module used -/

section

/-!
# Streaming SM3 on x86-64: `update` and `finalize`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/X86_64.lean`), so they are verified by the generic proofs
(`Proof/MdStream/X86_64/`) for SM3's instance (`Proof/Sm3/Md.lean`), given
what SM3's own pieces do: its length field and digest (`shape`), that the
taint analysis accepts its code between the calls (`taints`), and that its
compression function is verified (`callee`).
-/

@[expose] public section

namespace VG.Proof.Sm3.X86_64.Stream

open VG VG.X86_64 VG.Proof.MdStream VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (len64 out32)

abbrev params := Impl.Sm3.X86_64.Stream.params

theorem dims : Dims params := ⟨.inl rfl, by decide, by decide, by decide⟩

theorem shape : Shape (P := params) md where
  lenV s := (lenV64_ok true s).mono fun _ ⟨g, rd, wr, m, x0, x7⟩ => ⟨g, rd, wr, m, x0, x7⟩
  len s hout := by
    rw [show params.len = len64 88 true ++ [] from rfl]
    exact len64_ok hout fun s' g rd wr m => WP.block_nil ⟨g, rd, wr, m⟩
  out s hin hout hd := by
    refine (out32_ok (n := 8) true (by decide) hin hout hd).mono fun s' ⟨g, rd, wr, m⟩ => ⟨g, rd, wr, ?_⟩
    rw [m, digest_eq]

theorem taints : Taints params :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, by decide, by decide⟩

theorem callee : CalleeOk (P := params) md Impl.Sm3.X86_64.compress :=
  .of_verified compress_verified.1 compress_verified.2.1 (by rw [← Code.allInstrs_eq]; lit_decide)
    (by lit_decide)

namespace Update

theorem update_verified : Verified X86_64.target Impl.Sm3.X86_64.Stream.update Proof.Sm3.updateX86_64 :=
  have h := MdStream.X86_64.Update.verified (name := "vg_sm3_compress") dims taints callee (by lit_decide)
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sm3.iv m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.X86_64.Update.sat params

end Update

namespace Finalize

theorem finalize_verified : Verified X86_64.target Impl.Sm3.X86_64.Stream.finalize Proof.Sm3.finalizeX86_64 :=
  have h := MdStream.X86_64.Finalize.verified (name := "vg_sm3_compress") dims shape taints callee (by lit_decide)
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sm3.iv m hr trivial hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.X86_64.Finalize.sat params

end Finalize

end VG.Proof.Sm3.X86_64.Stream

end

end

/-!
# SM3 on x86-64: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sm3/X86_64/Compress.lean`); these theorems move them to the shared
contracts of `Spec/Sm3/Contract.lean`, which the artifacts are emitted with.

`update` and `finalize` keep their working space (20 words: the compression
function's 112 bytes, then our caller's callee-saved registers) in a frame of
their own: they are `updateScratch` and `finalizeScratch` (the shared
contracts with the working space as an argument, `Proof/Sm3/Scratch.lean`)
run in a frame that allocates it (`Verified.stackScratch`).
-/

@[expose] public section

namespace VG.Proof.Sm3.X86_64.Shared

theorem init :
    Verified X86_64.target Impl.Sm3.X86_64.Stream.init (Spec.Sm3.initContract X86_64.abi) :=
  Proof.Sm3.X86_64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sm3.initContract, Spec.Sm3.initSig, Proof.Sm3.initX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sm3.X86_64.Stream.initSat] using Proof.Sm3.X86_64.Stream.initSat)

theorem updateScratch :
    Verified X86_64.target Impl.Sm3.X86_64.Stream.update (Proof.Sm3.updateScratchContract X86_64.abi 20 8) :=
  Proof.Sm3.X86_64.Stream.Update.update_verified.of_implies (by
    sig_implies [Proof.Sm3.updateScratchContract, Proof.Sm3.updateScratchSig, Spec.Sm3.updateSig,
      Proof.Sm3.updateX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sm3.X86_64.Stream.Update.sat,
        MdStream.X86_64.Update.sat, Impl.Sm3.X86_64.Stream.params] using Proof.Sm3.X86_64.Stream.Update.sat)

theorem finalizeScratch :
    Verified X86_64.target Impl.Sm3.X86_64.Stream.finalize (Proof.Sm3.finalizeScratchContract X86_64.abi 20 8) :=
  Proof.Sm3.X86_64.Stream.Finalize.finalize_verified.of_implies (by
    sig_implies [Proof.Sm3.finalizeScratchContract, Proof.Sm3.finalizeScratchSig, Spec.Sm3.finalizeSig,
      Proof.Sm3.finalizeX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sm3.X86_64.Stream.Finalize.sat,
        MdStream.X86_64.Finalize.sat, Impl.Sm3.X86_64.Stream.params] using Proof.Sm3.X86_64.Stream.Finalize.sat)

theorem update : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratch 168 .r8 Impl.Sm3.X86_64.Stream.update)
    (Spec.Sm3.updateContract X86_64.abi (8 + 168)) :=
  X86_64.Verified.stackScratch (sig := Spec.Sm3.updateSig) (nm := "scratch") (e := .u64) (n := 20)
    (stack := 8) (bytes := 168)
    (by rw [← Proof.Sm3.updateScratchContract_eq]; exact updateScratch) (by decide) (by decide)
    (by decide) (Code.all_of_spTest (by lit_decide)) (by lit_decide)
    (Proof.Sm3.updatePostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalize : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratch 168 .rcx Impl.Sm3.X86_64.Stream.finalize)
    (Spec.Sm3.finalizeContract X86_64.abi (8 + 168)) :=
  X86_64.Verified.stackScratch (sig := Spec.Sm3.finalizeSig) (nm := "scratch") (e := .u64) (n := 20)
    (stack := 8) (bytes := 168)
    (by rw [← Proof.Sm3.finalizeScratchContract_eq]; exact finalizeScratch) (by decide) (by decide)
    (by decide) (Code.all_of_spTest (by lit_decide)) (by lit_decide)
    (Proof.Sm3.finalizePostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sm3.X86_64.Shared
