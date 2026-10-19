module

public import VerifiedGarbage.Proof.Sha512.Md
meta import VerifiedGarbage.Proof.Sha512.Md
public import VerifiedGarbage.Proof.MdStream.X86.Update
meta import VerifiedGarbage.Proof.MdStream.X86.Update
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sha512.X86.Compress
meta import VerifiedGarbage.Proof.Sha512.X86.Compress
public import VerifiedGarbage.Impl.Sha512.X86.Stream
meta import VerifiedGarbage.Impl.Sha512.X86.Stream
import VerifiedGarbage.Proof.Sha512.X86.Lit
meta import VerifiedGarbage.Proof.Sha512.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Impl.Sha256.X86.Stream
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sha512.Spec
meta import VerifiedGarbage.Impl.Sha256.X86.Stream
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha512.Spec

/-!
# Streaming SHA-512 on x86 (32-bit): `update`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/X86.lean`), so they are verified by the generic proofs
(`Proof/MdStream/X86/`) for the SHA-512 family's instance
(`Proof/Sha512/Md.lean`) with 272 bytes of scratch space, given that its
compression function is verified (`callee`) and that the taint analysis
accepts its code (which it checks together with the compression function's).
`Finalize.lean` adds what the family's length field and digest do.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86.Stream

open VG VG.X86 VG.Proof.MdStream VG.Proof.MdStream.X86

abbrev params := Impl.Sha512.X86.Stream.params

theorem dims : Dims params 272 := ⟨.inr rfl, by decide, by decide, by decide, by decide⟩

theorem callee : CalleeOk (P := params) md Impl.Sha512.X86.compress :=
  ⟨Compress.compress_verified.1, NoSp.of_all (by lit_decide), by lit_decide⟩

namespace Update

theorem update_verified : Verified X86.target Impl.Sha512.X86.Stream.update Proof.Sha512.updateX86 :=
  MdStream.X86.Update.verified (name := "vg_sha512_compress") dims callee
    (VG.Taint.constantTime (A := sseTaint) (MdStream.X86.Update.τ₀ params 272)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Update.agree₀ dims h₁ h₂ hp) (by taint_decide))

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.X86.Update.sat params 272

end Update

end VG.Proof.Sha512.X86.Stream
