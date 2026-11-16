module

public import VerifiedGarbage.Proof.MdStream.AArch64.Update
public import VerifiedGarbage.Proof.MdStream.AArch64.Finalize
import VerifiedGarbage.Proof.MdStream.AArch64.Words
public import VerifiedGarbage.Proof.Sm3.Md
import VerifiedGarbage.Proof.Sm3.AArch64.Compress
public import VerifiedGarbage.Proof.Sm3.AArch64.Contract
import VerifiedGarbage.Proof.Sm3.AArch64.Lit
public import VerifiedGarbage.Impl.Sm3.AArch64.Stream
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MdStream.AArch64.Update
meta import VerifiedGarbage.Proof.MdStream.AArch64.Finalize
meta import VerifiedGarbage.Proof.MdStream.AArch64.Words
meta import VerifiedGarbage.Proof.Sm3.Md
meta import VerifiedGarbage.Proof.Sm3.AArch64.Compress
meta import VerifiedGarbage.Proof.Sm3.AArch64.Contract
meta import VerifiedGarbage.Proof.Sm3.AArch64.Lit
meta import VerifiedGarbage.Impl.Sm3.AArch64.Stream
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Streaming SM3 on AArch64: `update` and `finalize`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/AArch64.lean`), so they are verified by the generic proofs
(`Proof/MdStream/AArch64/`) for SM3's instance (`Proof/Sm3/Md.lean`), given
what SM3's own pieces do: its length field and digest (`shape`), and, of each
implementation of its compression function (`Compress`), that it is verified
and that the taint analysis accepts the streaming code calling it.
-/

@[expose] public section

namespace VG.Proof.Sm3.AArch64.Stream

open VG VG.AArch64 VG.Proof.MdStream VG.Proof.MdStream.AArch64

abbrev params := Impl.Sm3.AArch64.Stream.params

theorem dims : Dims params := ⟨by decide, by decide, by decide, by decide⟩

theorem shape : Shape (P := params) md where
  lenKeepsV := by lit_decide
  outKeepsV := by lit_decide
  len _ hout := len64_ok (d := params.N + params.B - params.L) (be := true) (by decide) hout
  out _ hin hout hd := by
    refine (out32_ok (n := 8) true (by decide) hin hout hd).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
      ⟨g, rd, wr, sp, ?_⟩
    rw [m, digest_eq]

namespace Update

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.AArch64.Update.sat params

end Update

namespace Finalize

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.AArch64.Finalize.sat params

end Finalize

end VG.Proof.Sm3.AArch64.Stream

namespace VG.Proof.Sm3.AArch64

open VG VG.AArch64 VG.Proof.MdStream VG.Proof.MdStream.AArch64
open VG.Impl.MdStream.AArch64

/-- An implementation of the compression function, with what the streaming
code calling it needs: that it is verified, pushes no frame and writes no
callee-saved vector register, and that the taint analysis accepts `update`
and `finalize` calling it, which call nothing deeper. -/
structure Compress where
  name : String
  code : Prog isa
  verified : Verified AArch64.target code Proof.Sm3.compressAArch64
  noFrames : code.noFrames = true
  keepsV : code.allInstrs keepsV = true
  suffix : String
  updateCT : ConstantTime isa (updK (P := Stream.params) md).pre (updK (P := Stream.params) md).pub
    (update Stream.params name code)
  finalizeCT : ConstantTime isa (finK (P := Stream.params) md).pre (finK (P := Stream.params) md).pub
    (finalize Stream.params name code)
  updateDepth : (updateMain Stream.params name code).aarch64Depth = 0
  finalizeDepth : (finalizeMain Stream.params name code).aarch64Depth = 0

namespace Compress

variable (v : Compress)

def update : Prog isa := Impl.MdStream.AArch64.update Stream.params v.name v.code
def finalize : Prog isa := Impl.MdStream.AArch64.finalize Stream.params v.name v.code

theorem callee : CalleeOk (P := Stream.params) md v.code := ⟨v.verified.1, v.noFrames, v.keepsV⟩

theorem update_verified : Verified AArch64.target v.update Proof.Sm3.updateAArch64 := by
  have h := MdStream.AArch64.Update.verified Stream.dims v.callee v.updateCT
    (by rw [v.updateDepth]; decide)
  exact h.of_implies ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sm3.iv m hr hc,
    fun _ _ _ _ h => h, h.2.2⟩

theorem finalize_verified : Verified AArch64.target v.finalize Proof.Sm3.finalizeAArch64 := by
  have h := MdStream.AArch64.Finalize.verified Stream.dims Stream.shape v.callee v.finalizeCT
    (by rw [v.finalizeDepth]; decide)
  exact h.of_implies ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Sm3.iv m hr trivial hc,
    fun _ _ _ _ h => h, h.2.2⟩

end Compress

end VG.Proof.Sm3.AArch64
