module

public import VerifiedGarbage.Proof.Sha256.Arm.Stream.Md
meta import VerifiedGarbage.Proof.Sha256.Arm.Stream.Md
import VerifiedGarbage.Proof.Sha256.Digest
meta import VerifiedGarbage.Proof.Sha256.Digest
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Sha256.Arm.Lit
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Sha256.Arm.Lit
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.MdStream.Prefix
meta import VerifiedGarbage.Proof.MdStream.Arm.Words
meta import VerifiedGarbage.Proof.MdStream.Prefix
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Call
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Streaming SHA-224 on ARMv7: `finalize224`

`finalize224` is the generic `finalize` (`Impl/MdStream/Arm.lean`) with a
digest of the first 28 bytes of the final hash value (`params224`), so it is
verified by the generic proof of a `finalize` writing a prefix of the final
hash value (`Finalize.verifiedD`), given what writing that prefix does
(`ShapeD`), and constant time by the taint analysis of its code.
-/

@[expose] public section

namespace VG.Proof.Sha256.Arm.Stream.Finalize

open VG VG.Arm VG.Proof.MdStream VG.Proof.MdStream.Arm
open VG.Impl.Sha256.Arm.Stream (params224 finalize224)

theorem shape224 : ShapeD (P := params224) md 28 where
  le := by decide
  len := shape.len
  out s f₀ f₆ hin hout hd := by
    refine (out32_ok (n := 7) true (by decide) (by have : params224.N = 32 := rfl; omega) f₆
      (inRegions_prefix hin (by decide)) hout (hd.sub_left (Region.sub_prefix (by decide)))).mono
      fun s' ⟨g, rd, wr, sp, m⟩ => ⟨fun r h _ => g r h, rd, wr, sp, ?_⟩
    rw [m, digest_take _ _ (n := 7) (by decide)]

theorem finalize224_verified : Verified Arm.target finalize224 (MdStream.Arm.finKD (P := params224) md 28) :=
  MdStream.Arm.Finalize.verifiedD (P := params224) (name := "vg_sha256_compress")
    ⟨dims.1, dims.2, dims.3, dims.4, dims.5, dims.6⟩ shape224 (callee.withOut _)
    (VG.Taint.constantTime (A := taint) (MdStream.Arm.Finalize.τ₀D params224 28)
      (fun _ _ h₁ h₂ hp => MdStream.Arm.Finalize.agree₀D h₁ h₂ hp) (by taint_decide))

/-- A state satisfying the precondition of `finalize224`. -/
abbrev sat224 : State := MdStream.Arm.Finalize.satD params 28

end VG.Proof.Sha256.Arm.Stream.Finalize
