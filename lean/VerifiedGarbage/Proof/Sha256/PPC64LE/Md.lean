module

public import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
public import VerifiedGarbage.Proof.Sha256.Md
import VerifiedGarbage.Proof.Sha256.PPC64LE.Compress
public import VerifiedGarbage.Impl.Sha256.PPC64LE.Md
import VerifiedGarbage.Proof.MdStream.PPC64LE.Words
import VerifiedGarbage.Proof.Sha256.Digest
import VerifiedGarbage.Proof.MdStream.Prefix
import VerifiedGarbage.Proof.Framework.RegionsSub
public import Mathlib.Data.List.Nodup
public import VerifiedGarbage.Impl.Sha256.PPC64LE

/-!
# SHA-256 and SHA-224 on PPC64LE, as Merkle–Damgård hash functions

What the generic proofs (`Proof/MdStream/PPC64LE/`, `Proof/Pbkdf2/PPC64LE/`)
need of SHA-256's and SHA-224's parameters (`Impl/Sha256/PPC64LE/Md.lean`):
their sizes, length field and digest (`shape`, `shape224`), and that the
compression function is verified (`callee`).
-/

@[expose] public section

namespace VG.Proof.Sha256.PPC64LE.Md

open VG VG.PPC64LE VG.Proof.MdStream VG.Proof.MdStream.PPC64LE
open VG.Impl.Sha256.PPC64LE (mdParams mdParams224)

theorem dims : Dims mdParams := ⟨by decide, by decide, by decide, by decide⟩

theorem shape : ShapeD (P := mdParams) md 32 where
  le := by decide
  len _ hout := len64_ok (d := mdParams.N + mdParams.B - mdParams.L) (be := true) (by decide) hout
  out _ hin hout hd := by
    refine (out32_ok (n := 8) true (by decide) hin hout hd).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
      ⟨g, rd, wr, sp, ?_⟩
    rw [m, digest_eq, List.take_of_length_le (by simp only [List.length_flatMap, bytes32_length]; decide)]

theorem shape224 : ShapeD (P := mdParams224) md 28 where
  le := by decide
  len := shape.len
  out s hin hout hd := by
    refine (out32_ok (n := 7) true (by decide) (inRegions_prefix hin (by decide)) hout
      (hd.sub_left (Region.sub_prefix (by decide)))).mono fun s' ⟨g, rd, wr, sp, m⟩ => ⟨g, rd, wr, sp, ?_⟩
    rw [m, digest_take _ _ (n := 7) (by decide)]

theorem callee : CalleeOk (P := mdParams) md Impl.Sha256.PPC64LE.compress :=
  ⟨compress_verified.1, by decide +kernel⟩

theorem callee224 : CalleeOk (P := mdParams224) md Impl.Sha256.PPC64LE.compress := callee.withOut _

end VG.Proof.Sha256.PPC64LE.Md
