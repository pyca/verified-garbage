module

public import VerifiedGarbage.Proof.Sm3.PPC64LE.Compress
import VerifiedGarbage.Proof.Sm3.PPC64LE.Stream.Init
public import VerifiedGarbage.Proof.Sm3.Scratch
public import VerifiedGarbage.Spec.Sm3.Contract
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Sm3.PPC64LE.Stream
import VerifiedGarbage.Proof.Framework.PPC64LE.TaintMono
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintMono
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Finalize
import VerifiedGarbage.Proof.MdStream.PPC64LE.Words
public import VerifiedGarbage.Proof.Sm3.Md
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MdStream.PPC64LE.Finalize
meta import VerifiedGarbage.Proof.MdStream.PPC64LE.Words
meta import VerifiedGarbage.Proof.Sm3.Md
meta import VerifiedGarbage.Proof.Sm3.PPC64LE.Compress
meta import VerifiedGarbage.Impl.Sm3.PPC64LE.Stream
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Sm3.PPC64LE.Stream.Md`, which only this module used -/

section

/-!
# Streaming SM3 on PPC64LE: `update` and `finalize`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/PPC64LE.lean`), so they are verified by the generic proofs
(`Proof/MdStream/PPC64LE/`) for SM3's instance (`Proof/Sm3/Md.lean`), given
what SM3's own pieces do: its length field and digest (`shape`), that its
compression function is verified (`callee`), and that the taint analysis
accepts its code.
-/

@[expose] public section

namespace VG.Proof.Sm3.PPC64LE.Stream

open VG VG.PPC64LE VG.Proof.MdStream VG.Proof.MdStream.PPC64LE

abbrev params := Impl.Sm3.PPC64LE.Stream.params

theorem dims : Dims params := ⟨by decide, by decide, by decide, by decide⟩

theorem shape : ShapeD (P := params) md 32 where
  le := by decide
  len _ hout := len64_ok (d := params.N + params.B - params.L) (be := true) (by decide) hout
  out _ hin hout hd := by
    refine (out32_ok (n := 8) true (by decide) hin hout hd).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
      ⟨g, rd, wr, sp, ?_⟩
    rw [m, digest_eq, List.take_of_length_le (by simp only [List.length_flatMap, bytes32_length]; decide)]

theorem callee : CalleeOk (P := params) md Impl.Sm3.PPC64LE.compress :=
  ⟨compress_verified.1, by decide +kernel⟩

namespace Update

theorem update_verified : Verified PPC64LE.target Impl.Sm3.PPC64LE.Stream.update Proof.Sm3.updatePPC64LE :=
  have h := MdStream.PPC64LE.Update.verified (name := "vg_sm3_compress") dims callee
    (VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7])
      (fun _ _ _ _ hp => MdStream.PPC64LE.Update.agree₀ hp) (by taint_decide_sum [VG.Proof.Sm3.PPC64LE.compressSum]))
    (by decide +kernel) (by decide +kernel)
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sm3.iv m hr hc, fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.PPC64LE.Update.sat params

end Update

namespace Finalize

theorem finalize_verified : Verified PPC64LE.target Impl.Sm3.PPC64LE.Stream.finalize Proof.Sm3.finalizePPC64LE :=
  have h := MdStream.PPC64LE.Finalize.verifiedD (name := "vg_sm3_compress") dims shape callee
    (VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
      (fun _ _ _ _ hp => MdStream.PPC64LE.Finalize.agree₀D hp) (by taint_decide_sum [VG.Proof.Sm3.PPC64LE.compressSum]))
    (by decide +kernel) (by decide +kernel)
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => by
      have := h Spec.Sm3.iv m hr trivial hc
      exact this.trans (List.take_of_length_le (Nat.le_of_eq (md.digest_length _))),
      fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.PPC64LE.Finalize.satD params 32

end Finalize

end VG.Proof.Sm3.PPC64LE.Stream

end

end

/-!
# SM3 on PPC64LE: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sm3/PPC64LE/Contract.lean`); these theorems move them to the shared
contracts of `Spec/Sm3/Contract.lean`, which the artifacts are emitted with.

`update` and `finalize` keep their working space (20 words: the compression
function's 112 bytes, then the registers the streaming code saves) in a frame
of their own: they are `updateScratch` and `finalizeScratch` (the shared
contracts with the working space as an argument, `Proof/Sm3/Scratch.lean`)
run in a frame that allocates it (`Verified.stackScratch`).
-/

@[expose] public section

namespace VG.Proof.Sm3.PPC64LE.Shared

open _root_.VG.PPC64LE

theorem init :
    Verified PPC64LE.target Impl.Sm3.PPC64LE.Stream.init (Spec.Sm3.initContract PPC64LE.abi) :=
  Proof.Sm3.PPC64LE.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sm3.initContract, Spec.Sm3.initSig, Proof.Sm3.initPPC64LE,
      PPC64LE.abi, PPC64LE.argRegs]
      [Proof.Sm3.PPC64LE.Stream.initSat] using Proof.Sm3.PPC64LE.Stream.initSat)

theorem updateScratch :
    Verified PPC64LE.target Impl.Sm3.PPC64LE.Stream.update (Proof.Sm3.updateScratchContract PPC64LE.abi 20 48) :=
  Proof.Sm3.PPC64LE.Stream.Update.update_verified.of_implies (by
    sig_implies [Proof.Sm3.updateScratchContract, Proof.Sm3.updateScratchSig, Spec.Sm3.updateSig,
      Proof.Sm3.updatePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [Proof.Sm3.PPC64LE.Stream.Update.sat,
        MdStream.PPC64LE.Update.sat, Impl.Sm3.PPC64LE.Stream.params] using Proof.Sm3.PPC64LE.Stream.Update.sat)

theorem finalizeScratch :
    Verified PPC64LE.target Impl.Sm3.PPC64LE.Stream.finalize (Proof.Sm3.finalizeScratchContract PPC64LE.abi 20 48) :=
  Proof.Sm3.PPC64LE.Stream.Finalize.finalize_verified.of_implies (by
    sig_implies [Proof.Sm3.finalizeScratchContract, Proof.Sm3.finalizeScratchSig, Spec.Sm3.finalizeSig,
      Proof.Sm3.finalizePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [Proof.Sm3.PPC64LE.Stream.Finalize.sat,
        MdStream.PPC64LE.Finalize.satD, Impl.Sm3.PPC64LE.Stream.params] using Proof.Sm3.PPC64LE.Stream.Finalize.sat)

theorem update : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 192 .r7 Impl.Sm3.PPC64LE.Stream.update)
    (Spec.Sm3.updateContract PPC64LE.abi (48 + 192)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sm3.updateSig) (nm := "scratch") (e := .u64) (n := 20)
    (stack := 48) (bytes := 192)
    (by rw [← Proof.Sm3.updateScratchContract_eq]; exact updateScratch) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm3.updatePost_local _)
    (fun vs m m₁ m₂ r hl _ hb h => Proof.Sm3.updatePostOut_local _ vs m m₁ m₂ r hl hb h)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalize : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 192 .r6 Impl.Sm3.PPC64LE.Stream.finalize)
    (Spec.Sm3.finalizeContract PPC64LE.abi (48 + 192)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sm3.finalizeSig) (nm := "scratch") (e := .u64) (n := 20)
    (stack := 48) (bytes := 192)
    (by rw [← Proof.Sm3.finalizeScratchContract_eq]; exact finalizeScratch) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm3.finalizePost_local _)
    (fun vs m m₁ m₂ r hl _ hb h => Proof.Sm3.finalizePostOut_local _ vs m m₁ m₂ r hl hb h)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sm3.PPC64LE.Shared
