module

public import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
public import VerifiedGarbage.Proof.Sha512.Md
import VerifiedGarbage.Proof.Sha512.PPC64LE.Compress
public import VerifiedGarbage.Impl.Sha512.PPC64LE.Md
import VerifiedGarbage.Proof.MdStream.PPC64LE.Words
import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
import VerifiedGarbage.Proof.Sha512.Digest
import VerifiedGarbage.Proof.MdStream.Prefix
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Sha512.PPC64LE

/-!
# The SHA-512 family on PPC64LE, as Merkle–Damgård hash functions

What the generic proofs (`Proof/MdStream/PPC64LE/`, `Proof/Pbkdf2/PPC64LE/`)
need of the SHA-512 family's parameters (`Impl/Sha512/PPC64LE/Md.lean`):
their sizes, length field and digest (`shape`, `shape384`, `shape512_256`,
`shape512_224`), and that the compression function is verified (`callee`).
-/

@[expose] public section

namespace VG.Proof.Sha512.PPC64LE.Md

open VG VG.PPC64LE VG.Proof.MdStream VG.Proof.MdStream.PPC64LE
open VG.Impl.MdStream.PPC64LE (out64)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame writeBytes_append)
open VG.Impl.Sha512.PPC64LE (mdParams mdParams384 mdParams512_256 mdParams512_224)

theorem dims : Dims mdParams := ⟨by decide, by decide, by decide, by decide⟩

theorem shape : ShapeD (P := mdParams) md 64 where
  le := by decide
  len _ hout := (len128_ok (d := 176) (by decide) hout).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
    ⟨g, rd, wr, sp, by rw [m, lenOf_split]; rfl⟩
  out _ hin hout hd := by
    refine (out64_ok (n := 8) (by decide) hin hout hd).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
      ⟨g, rd, wr, sp, ?_⟩
    rw [m, digest_take _ _ (n := 8) (by decide)]

/-- A digest of the first `n` words. -/
theorem shapeN {n : Nat} (hn : n ≤ 8) {o : List Instr} (ho : o = out64 n) :
    ShapeD (P := { mdParams with out := o }) md (8 * n) where
  le := by show 8 * n ≤ 64; omega
  len := shape.len
  out s hin hout hd := by
    subst ho
    refine (out64_ok (n := n) (by omega) (inRegions_prefix hin (by show 8 * n ≤ 64; omega)) hout
      (hd.sub_left (Region.sub_prefix (by show 8 * n ≤ 64; omega)))).mono fun s' ⟨g, rd, wr, sp, m⟩ => ⟨g, rd, wr, sp, ?_⟩
    rw [m, digest_take _ _ hn]

theorem shape384 : ShapeD (P := mdParams384) md 48 := shapeN (n := 6) (by decide) rfl

theorem shape512_256 : ShapeD (P := mdParams512_256) md 32 := shapeN (n := 4) (by decide) rfl

theorem shape512_224 : ShapeD (P := mdParams512_224) md 28 where
  le := by decide
  len := shape.len
  out s hin hout hd := by
    show WP isa (.block (out64 3 ++ Impl.Sha512.PPC64LE.Stream.outHi 3)) s _
    rw [WP.block_append_iff]
    refine WP.mono (out64_ok (n := 3) (by decide) (inRegions_prefix hin (by decide))
      (inRegions_prefix hout (by decide))
      ((hd.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))))
      fun s₁ ⟨g₁, rd₁, wr₁, sp₁, m₁⟩ => ?_
    simp only [Impl.Sha512.PPC64LE.Stream.outHi]
    refine wp_lwz (a := s.gpr .r26 + BitVec.ofNat 64 28) (by decide) (by rw [g₁ _ (by decide) (by decide)])
      (by rw [rd₁, wr₁]; exact InRegions.offset hin (by decide) (by decide)) fun s₂ u₂ => ?_
    refine wp_li (by decide) fun s₃ u₃ => wp_stwbrx (a := s.gpr .r28 + BitVec.ofNat 64 24)
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide) (by decide), u₃.gpr])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact InRegions.offset hout (by decide) (by decide)) fun s₄ g₄ => WP.block_nil
        ⟨fun r h8 h11 => ?_, by rw [g₄.rd, u₃.rd, u₂.rd, rd₁], by rw [g₄.wr, u₃.wr, u₂.wr, wr₁],
          by rw [g₄.sp, u₃.sp, u₂.sp, sp₁], ?_⟩
    · rw [g₄.gpr, u₃.other r h11, u₂.other r h8, g₁ r h8 h11]
    · -- The high half of word 3 is not overwritten by the first 24 bytes.
      have hread : s₁.mem.readW (s.gpr .r26 + BitVec.ofNat 64 28) 32 = s.mem.readW (s.gpr .r26 + BitVec.ofNat 64 28) 32 := by
        rw [m₁]
        refine (writeBytes_frame _ _ _ (Region.contains_self _ _)).readW
          (r := ⟨s.gpr .r26 + BitVec.ofNat 64 28, 4⟩) (Region.contains_self _ _) (fun r' hr' => ?_) (by decide)
        simp only [List.mem_singleton] at hr'
        subst hr'
        rw [length_flatMap_range _ (w := 8) (fun _ => by simp [bytes64]) 3]
        have hd' : Region.Disjoint ⟨s.gpr .r26, 64⟩ ⟨s.gpr .r28, 28⟩ := hd
        exact (hd'.sub_left (VG.Offset.sub_base (s.gpr .r26) (d := 28) (n := 4) (k := 64) (by decide))).sub_right
          (Region.sub_prefix (by decide))
      have hl : ((List.range 3).flatMap fun k =>
          bytes64 true (s.mem.readW (s.gpr .r26 + BitVec.ofNat 64 (8 * k)) 64)).length = 24 :=
        length_flatMap_range _ (w := 8) (fun _ => by simp [bytes64]) 3
      rw [g₄.mem, u₃.mem, u₂.mem, u₃.other _ (by decide), u₂.gpr, BitVec.setWidth_setWidth_of_le _ (by decide),
        BitVec.setWidth_eq, hread, m₁, show rev32 (s.mem.readW (s.gpr .r26 + BitVec.ofNat 64 28) 32) =
          (if true then rev32 (s.mem.readW (s.gpr .r26 + BitVec.ofNat 64 28) 32) else
            s.mem.readW (s.gpr .r26 + BitVec.ofNat 64 28) 32) from rfl, writeW32,
        show (24 : Nat) = _ from hl.symm, writeBytes_append _ _ _ _ (by rw [hl]; simp [bytes32]),
        digest_take28]

theorem callee : CalleeOk (P := mdParams) md Impl.Sha512.PPC64LE.compress :=
  ⟨compress_verified.1, by decide +kernel⟩

theorem callee384 : CalleeOk (P := mdParams384) md Impl.Sha512.PPC64LE.compress := callee.withOut _

theorem callee512_256 : CalleeOk (P := mdParams512_256) md Impl.Sha512.PPC64LE.compress := callee.withOut _

theorem callee512_224 : CalleeOk (P := mdParams512_224) md Impl.Sha512.PPC64LE.compress := callee.withOut _

end VG.Proof.Sha512.PPC64LE.Md
