module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm3.PostOut
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Sm3.RISCV64.Compress
public import VerifiedGarbage.Spec.Sm3.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.Sm3.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public import VerifiedGarbage.Proof.MdStream.RISCV64.Init
public meta import VerifiedGarbage.Proof.MdStream.RISCV64.Init
public import VerifiedGarbage.Proof.Sm3.Md
public meta import VerifiedGarbage.Proof.Sm3.Md
public meta import VerifiedGarbage.Proof.Sm3.RISCV64.Compress
public import VerifiedGarbage.Impl.Sm3.RISCV64.Stream
public meta import VerifiedGarbage.Impl.Sm3.RISCV64.Stream
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.MdStream.RISCV64.Words
meta import VerifiedGarbage.Proof.MdStream.RISCV64.Words
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sm3.Stream
meta import VerifiedGarbage.Proof.Sm3.Stream
import all Init.Data.Nat.Bitwise.Basic

/-! ### `Sm3.RISCV64.Stream`, which only this module used -/

section

/-!
# Streaming SM3 on RISC-V

`init` stores the initial hash value (`Proof/MdStream/RISCV64/Init.lean`), and
`update` and `finalize` are the generic streaming code
(`Impl/MdStream/RISCV64.lean`), so they are verified by the generic proofs
(`Proof/MdStream/RISCV64/`) for SM3's instance (`Proof/Sm3/Md.lean`), given
what SM3's own pieces do: its length field and digest (`shape`), that its
compression function is verified (`callee`), and that the taint analysis accepts its code.
-/

@[expose] public section

namespace VG.Proof.Sm3.RISCV64.Stream

open VG VG.RISCV64 VG.Proof.MdStream VG.Proof.MdStream.RISCV64
open VG.Impl.Sm3.RISCV64.Stream (params)

theorem callee : CalleeOk md Impl.Sm3.RISCV64.compress :=
  ⟨fun s ⟨h₁, h₂, h₃, h₄, h₅, _⟩ => compress_verified.1 s ⟨h₁, h₂, h₃, h₄, h₅⟩, by decide +kernel⟩

/-! ## The length field and the digest -/

theorem shape : ShapeD (P := params) md 32 where
  le := by decide
  len s hout := lenBE_ok (by decide) s hout
  out s hin hout hd := by
    refine (outBE_ok (n := 8) (by decide) s hin hout hd).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
      ⟨g, rd, wr, sp, ?_⟩
    rw [m, digest_eq, List.take_of_length_le (by rw [flat_length])]

/-! ## The functions -/

theorem init_verified : Verified RISCV64.target Impl.Sm3.RISCV64.Stream.init Proof.Sm3.initRISCV64 :=
  have h := MdStream.RISCV64.init_verified (n := 96) Spec.Sm3.iv.toList (by decide) (by decide)
    (VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0]) (fun _ _ _ _ h => initAgree h)
      (by taint_decide_sum [VG.Proof.Sm3.RISCV64.compressSum]))
  Verified.of_implies h ⟨fun _ h => h, fun s _ _ h => by
      refine (repr_iff (m := [])).mpr (md.repr_nil (stateAt_eq fun k hk => ?_))
      rw [h k (by simpa using hk), getElem!_pos _ k (by simpa using hk), Vector.getElem_toList],
    fun _ _ _ _ h => h, h.2.2⟩

theorem update_verified : Verified RISCV64.target Impl.Sm3.RISCV64.Stream.update Proof.Sm3.updateRISCV64 :=
  have h := MdStream.RISCV64.Update.verified (P := params) (name := "vg_sm3_compress") (by decide) callee
    (VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
      (fun _ _ _ _ hp => MdStream.RISCV64.Update.agree₀ hp) (by taint_decide_sum [VG.Proof.Sm3.RISCV64.compressSum]))
    ⟨MdStream.RISCV64.Update.sat 32, rfl, rfl, Region.disjoint_of_sep (by decide), by decide, by decide,
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide)⟩
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sm3.iv m hr hc, fun _ _ _ _ h => h, h.2.2⟩

theorem finalize_verified :
    Verified RISCV64.target Impl.Sm3.RISCV64.Stream.finalize Proof.Sm3.finalizeRISCV64 :=
  have h := MdStream.RISCV64.Finalize.verifiedD (P := params) (name := "vg_sm3_compress") (by decide) shape callee
    (keepsN_all _ (by decide))
    (VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
      (fun _ _ _ _ hp => MdStream.RISCV64.Finalize.agree₀ hp) (by taint_decide_sum [VG.Proof.Sm3.RISCV64.compressSum]))
    ⟨MdStream.RISCV64.Finalize.sat 32 32, rfl, rfl, Region.disjoint_of_sep (by decide), by decide, by decide,
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide)⟩
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => by
      have := h Spec.Sm3.iv m hr trivial hc
      exact this.trans (List.take_of_length_le (Nat.le_of_eq (md.digest_length _))),
      fun _ _ _ _ h => h, h.2.2⟩

end VG.Proof.Sm3.RISCV64.Stream

end

end

/-! ### `Sm3.RISCV64.Shared`, which only this module used -/

section

/-!
# SM3 on RISC-V: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written
against per-target contracts (`Proof/Sm3/RISCV64/Compress.lean`); these
theorems move them to the shared contracts of `Spec/Sm3/Contract.lean`,
which the artifacts are emitted with. `update` and `finalize` keep their
working space in a frame of their own, of 144 bytes
(`Impl.MdStream.RISCV64.frameBytes`), the `stack` of their contracts.
-/

@[expose] public section

namespace VG.Proof.Sm3.RISCV64.Shared

open _root_.VG.RISCV64

theorem init :
    Verified RISCV64.target Impl.Sm3.RISCV64.Stream.init (Spec.Sm3.initContract RISCV64.abi) :=
  Proof.Sm3.RISCV64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sm3.initContract, Spec.Sm3.initSig, Proof.Sm3.initRISCV64,
      RISCV64.abi, RISCV64.argRegs]
      [MdStream.RISCV64.initSat] using MdStream.RISCV64.initSat 96)

theorem update :
    Verified RISCV64.target Impl.Sm3.RISCV64.Stream.update (Spec.Sm3.updateContract RISCV64.abi 144) :=
  Proof.Sm3.RISCV64.Stream.update_verified.of_implies (by
    contract_implies [Spec.Sm3.updateContract, Spec.Sm3.updateSig, Spec.Sm3.updatePost,
      Proof.Sm3.updateRISCV64, RISCV64.abi, RISCV64.argRegs]
      [MdStream.RISCV64.Update.sat] using MdStream.RISCV64.Update.sat 32)

theorem finalize :
    Verified RISCV64.target Impl.Sm3.RISCV64.Stream.finalize (Spec.Sm3.finalizeContract RISCV64.abi 144) :=
  Proof.Sm3.RISCV64.Stream.finalize_verified.of_implies (by
    contract_implies [Spec.Sm3.finalizeContract, Spec.Sm3.finalizeSig, Spec.Sm3.finalizePost,
      Proof.Sm3.finalizeRISCV64, RISCV64.abi, RISCV64.argRegs]
      [MdStream.RISCV64.Finalize.sat] using MdStream.RISCV64.Finalize.sat 32 32)

end VG.Proof.Sm3.RISCV64.Shared

end

end

/-!
# SM3 on RISC-V, without secret residue

Each of the streaming functions as emitted (`Impl.Sm3.RISCV64.Fn`): the
function followed by `Impl.Scrub.RISCV64.scrubTail`, which clears the
caller-saved registers and the stack its frames used. Each theorem below
states that one meets its contract in constant time and returns without
secret residue (`VerifiedScrubbed`, by `RISCV64.Scrub.verifiedScrubbedAll`),
which is what its registration binds. Their postconditions read the memory
on return only within their buffers (`Proof/Sm3/PostOut.lean`).
-/

@[expose] public section

namespace VG.Proof.Sm3.RISCV64

open VG.RISCV64 VG.RISCV64.Scrub

/-- `vg_sm3_init` as emitted (`Impl.Sm3.RISCV64.Fn.init`) meets its contract in constant time
and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed target Impl.Sm3.RISCV64.Fn.init (Spec.Sm3.initContract RISCV64.abi) 0 :=
  verifiedScrubbedAll (api := Spec.Sm3.initApi) (W := 0)
    { code := Impl.Sm3.RISCV64.Stream.init, verified := Shared.init }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm3.initPost_out 64))
    (show scrubSide Impl.Sm3.RISCV64.Stream.init 0 0 [] = true by lit_decide)

/-- `vg_sm3_update` as emitted (`Impl.Sm3.RISCV64.Fn.update`) meets its contract in constant
time and returns without secret residue. -/
theorem update_scrubbed :
    VerifiedScrubbed target Impl.Sm3.RISCV64.Fn.update (Spec.Sm3.updateContract RISCV64.abi 144) 0 :=
  verifiedScrubbedAll (api := Spec.Sm3.updateApi) (W := 144)
    { code := Impl.Sm3.RISCV64.Stream.update, verified := Shared.update }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm3.updatePost_out 64))
    (show scrubSide Impl.Sm3.RISCV64.Stream.update 144 0 [] = true by lit_decide)

/-- `vg_sm3_finalize` as emitted (`Impl.Sm3.RISCV64.Fn.finalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_scrubbed :
    VerifiedScrubbed target Impl.Sm3.RISCV64.Fn.finalize (Spec.Sm3.finalizeContract RISCV64.abi 144) 0 :=
  verifiedScrubbedAll (api := Spec.Sm3.finalizeApi) (W := 144)
    { code := Impl.Sm3.RISCV64.Stream.finalize, verified := Shared.finalize }
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sm3.finalizePost_out 64))
    (show scrubSide Impl.Sm3.RISCV64.Stream.finalize 144 0 [] = true by lit_decide)

end VG.Proof.Sm3.RISCV64
