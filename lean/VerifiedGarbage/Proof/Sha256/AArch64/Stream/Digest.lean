import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Md
import VerifiedGarbage.Proof.Sha256.Digest

/-!
# Streaming SHA-224 on AArch64: the digest

SHA-224's `finalize` is the generic `finalize` (`Impl/MdStream/AArch64.lean`)
with a digest of the first 28 bytes of the final hash value (`params224`), so
it is verified by the generic proof of a `finalize` writing a prefix of the
final hash value (`Finalize.verifiedD`), given what writing that prefix does
(`ShapeD`).
-/

namespace VG.Proof.Sha256.AArch64.Stream

open VG VG.AArch64 VG.Proof.MdStream VG.Proof.MdStream.AArch64
open VG.Impl.Sha256.AArch64.Stream (params224)

theorem shape224 : ShapeD (P := params224) md 28 where
  le := by decide
  lenKeepsV := shape.lenKeepsV
  outKeepsV := by decide +kernel
  len := shape.len
  out s hin hout hd := by
    refine (out32_ok (n := 7) true (by decide) (inRegions_prefix hin (by decide)) hout
      (hd.sub_left (Region.sub_prefix (by decide)))).mono fun s' ⟨g, rd, wr, sp, m⟩ => ⟨g, rd, wr, sp, ?_⟩
    rw [m, digest_take _ _ (n := 7) (by decide)]

/-- A state satisfying the precondition of SHA-224's `finalize`. -/
abbrev Finalize.sat224 : State := MdStream.AArch64.Finalize.satD params 28

end VG.Proof.Sha256.AArch64.Stream
