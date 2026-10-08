import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Md
import VerifiedGarbage.Proof.Sha512.Digest

/-!
# Streaming SHA-384, SHA-512/256 and SHA-512/224 on AArch64: the digests

`finalizeDigestWith` is the generic `finalize` (`Impl/MdStream/AArch64.lean`)
with a digest of the first 48, 32 or 28 bytes of the final hash value
(`params384`, `params512_256`, `params512_224`), so it is verified by the
generic proof of a `finalize` writing a prefix of the final hash value
(`Finalize.verifiedD`), given what writing that prefix does (`ShapeD`).
-/

namespace VG.Proof.Sha512.AArch64.Stream

open VG VG.AArch64 VG.Proof.MdStream VG.Proof.MdStream.AArch64
open VG.Impl.MdStream.AArch64 (out64)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_frame)
open VG.Impl.Sha512.AArch64.Stream (outHi params384 params512_256 params512_224)

/-- `out64 n` writes the first `8 n` bytes of the digest. -/
theorem out64_take {n : Nat} (hn : n ≤ 8) (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .x19) 64)
    (hout : InRegions s.wr (s.gpr .x21) (8 * n)) (hd : Region.Disjoint ⟨s.gpr .x19, 64⟩ ⟨s.gpr .x21, 8 * n⟩) :
    WP isa (.block (out64 n)) s fun s' => (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .x21) ((md.digest (md.stateAt s.mem (s.gpr .x19))).take (8 * n)) :=
  (out64_ok (n := n) (by omega) (inRegions_prefix hin (by omega)) hout
    (hd.sub_left (Region.sub_prefix (by omega)))).mono
    fun _ ⟨g, rd, wr, sp, m⟩ => ⟨g, rd, wr, sp, by rw [m, digest_take _ _ hn]⟩

/-- `out64 3 ++ outHi 3` writes the first 28 bytes of the digest. -/
theorem out224_ok (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .x19) 64)
    (hout : InRegions s.wr (s.gpr .x21) 28) (hd : Region.Disjoint ⟨s.gpr .x19, 64⟩ ⟨s.gpr .x21, 28⟩) :
    WP isa (.block (out64 3 ++ outHi 3)) s fun s' => (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .x21) ((md.digest (md.stateAt s.mem (s.gpr .x19))).take 28) := by
  rw [WP.block_append_iff]
  refine (out64_ok (n := 3) (by decide) (inRegions_prefix hin (by decide)) (inRegions_prefix hout (by decide))
    ((hd.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)))).mono
    fun s₁ ⟨g₁, rd₁, wr₁, sp₁, m₁⟩ => ?_
  have hl : ((List.range 3).flatMap fun k =>
      bytes64 true (s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 (8 * k)) 64)).length = 24 :=
    length_flatMap_range _ (w := 8) (fun _ => by simp [bytes64]) 3
  -- The high half of word 3 is not yet overwritten.
  have hread : s₁.mem.readW (s.gpr .x19 + BitVec.ofNat 64 28) 32 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 28) 32 := by
    rw [m₁]
    refine (writeBytes_frame _ _ _ (R := ⟨s.gpr .x21, 28⟩) ?_).readW
      (r := ⟨s.gpr .x19 + BitVec.ofNat 64 28, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    · rw [hl]
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
      decide
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact hd.sub_left (sub_offset (by decide) (by decide))
  refine wp_ldr32 (a := s.gpr .x19 + BitVec.ofNat 64 28) (by decide) (by rw [g₁ _ (by decide)])
    (by rw [rd₁, wr₁]; exact InRegions.offset hin (by decide) (by decide)) fun s₂ u₂ => ?_
  refine wp_rev32 fun s₃ u₃ => wp_str32 (a := s.gpr .x21 + BitVec.ofNat 64 24) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide)])
    (by rw [u₃.wr, u₂.wr, wr₁]; exact InRegions.offset hout (by decide) (by decide)) fun s₄ g₄ =>
      WP.block_nil ⟨fun r h => by rw [g₄.gpr, u₃.other r h, u₂.other r h, g₁ r h],
        by rw [g₄.rd, u₃.rd, u₂.rd, rd₁], by rw [g₄.wr, u₃.wr, u₂.wr, wr₁],
        by rw [g₄.sp, u₃.sp, u₂.sp, sp₁], ?_⟩
  rw [g₄.mem, u₃.mem, u₂.mem, u₃.gpr, u₂.gpr, setWidth32, setWidth32, hread, m₁, digest_take28,
    ← writeBytes_append _ _ _ _ (by rw [hl]; simp [bytes32]), hl, ← writeW32 _ _ true]
  rfl

theorem shape384 : ShapeD (P := params384) md 48 where
  le := by decide
  lenKeepsV := shape.lenKeepsV
  outKeepsV := by decide +kernel
  len := shape.len
  out s hin hout hd := out64_take (n := 6) (by decide) s hin hout hd

theorem shape512_256 : ShapeD (P := params512_256) md 32 where
  le := by decide
  lenKeepsV := shape.lenKeepsV
  outKeepsV := by decide +kernel
  len := shape.len
  out s hin hout hd := out64_take (n := 4) (by decide) s hin hout hd

theorem shape512_224 : ShapeD (P := params512_224) md 28 where
  le := by decide
  lenKeepsV := shape.lenKeepsV
  outKeepsV := by decide +kernel
  len := shape.len
  out s hin hout hd := out224_ok s hin hout hd

/-- A state satisfying the precondition of `finalizeDigestWith` with a
`D`-byte digest. -/
abbrev Finalize.satD (D : Nat) : State := MdStream.AArch64.Finalize.satD params D

end VG.Proof.Sha512.AArch64.Stream
