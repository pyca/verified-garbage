import VerifiedGarbage.Proof.Sha512.X86.Stream.Finalize
import VerifiedGarbage.Proof.Sha512.Digest

/-!
# Streaming SHA-384, SHA-512/256 and SHA-512/224 on x86 (32-bit): `finalize`

`finalizeDigest` is the generic `finalize` (`Impl/MdStream/X86.lean`) with a
digest of the first 48, 32 or 28 bytes of the final hash value
(`params384`, `params512_256`, `params512_224`), so it is verified by the
generic proof of a `finalize` writing a prefix of the final hash value
(`Finalize.verified_roD`), given what writing that prefix does (`ShapeD`),
and constant time by the taint analysis of its code.
-/

namespace VG.Proof.Sha512.X86.Stream

open VG VG.X86 VG.Proof.MdStream VG.Proof.MdStream.X86
open VG.Impl.MdStream.X86 (out64)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_frame)
open VG.Impl.Sha512.X86.Stream (outHi params384 params512_256 params512_224 finalizeDigest)

/-- `out64 n` writes the first `8 n` bytes of the digest. -/
theorem out64_take {n : Nat} (hn : n ≤ 8) (s : State) (hbx : (s.gpr .ebx).toNat + 64 ≤ 2 ^ 32)
    (hax : (s.gpr .eax).toNat + 8 * n ≤ 2 ^ 32)
    (hin : InRegions (s.rd ++ s.wr) ((s.gpr .ebx).setWidth 64) 64)
    (hout : InRegions s.wr ((s.gpr .eax).setWidth 64) (8 * n))
    (hd : Region.Disjoint ⟨(s.gpr .ebx).setWidth 64, 64⟩ ⟨(s.gpr .eax).setWidth 64, 8 * n⟩) :
    WP isa (.block (out64 n)) s fun s' => (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mem = writeBytes s.mem ((s.gpr .eax).setWidth 64)
        ((md.digest (md.stateAt s.mem ((s.gpr .ebx).setWidth 64))).take (8 * n)) :=
  (out64_ok (n := n) (by omega) (by omega) hax (inRegions_prefix hin (by omega)) hout
    (hd.sub_left (Region.sub_prefix (by omega)))).mono
    fun _ ⟨g, rd, wr, m⟩ => ⟨g, rd, wr, by rw [m, digest_take_halves _ _ hn]⟩

/-- `out64 3 ++ outHi 3` writes the first 28 bytes of the digest. -/
theorem out224_ok (s : State) (hbx : (s.gpr .ebx).toNat + 64 ≤ 2 ^ 32)
    (hax : (s.gpr .eax).toNat + 28 ≤ 2 ^ 32)
    (hin : InRegions (s.rd ++ s.wr) ((s.gpr .ebx).setWidth 64) 64)
    (hout : InRegions s.wr ((s.gpr .eax).setWidth 64) 28)
    (hd : Region.Disjoint ⟨(s.gpr .ebx).setWidth 64, 64⟩ ⟨(s.gpr .eax).setWidth 64, 28⟩) :
    WP isa (.block (out64 3 ++ outHi 3)) s fun s' => (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mem = writeBytes s.mem ((s.gpr .eax).setWidth 64)
        ((md.digest (md.stateAt s.mem ((s.gpr .ebx).setWidth 64))).take 28) := by
  rw [WP.block_append_iff]
  refine (out64_ok (n := 3) (by decide) (by omega) (by omega) (inRegions_prefix hin (by decide))
    (inRegions_prefix hout (by decide))
    ((hd.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)))).mono
    fun s₁ ⟨g₁, rd₁, wr₁, m₁⟩ => ?_
  have hl : ((List.range 3).flatMap fun k =>
      bytes32 true (s.mem.readW ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (8 * k + 4)) 32) ++
        bytes32 true (s.mem.readW ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (8 * k)) 32)).length = 24 :=
    length_flatMap_range _ (w := 8) (fun _ => by simp [bytes32_length]) 3
  -- The high half of word 3 is not yet overwritten.
  have hread : s₁.mem.readW ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 28) 32 =
      s.mem.readW ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 28) 32 := by
    rw [m₁]
    refine (writeBytes_frame _ _ _ (R := ⟨(s.gpr .eax).setWidth 64, 28⟩) ?_).readW
      (r := ⟨(s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 28, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    · rw [hl]
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
      decide
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact hd.sub_left (sub_offset (by decide) (by decide))
  simp only [outHi]
  refine wp_movm (a := (s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 28)
    (by rw [ea_at, g₁ _ (by decide), addr_eq (by omega)])
    (by rw [rd₁, wr₁]; exact out_in hin (by decide) (by decide)) fun s₂ u₂ => wp_bswap fun s₃ u₃ => ?_
  refine wp_store (a := (s.gpr .eax).setWidth 64 + BitVec.ofNat 64 24)
    (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), addr_eq (by omega)])
    (by rw [u₃.wr, u₂.wr, wr₁]; exact out_in hout (by decide) (by decide)) fun s₄ u₄ =>
      WP.block_nil ⟨fun r h => by rw [u₄.gpr, u₃.other r h, u₂.other r h, g₁ r h],
        by rw [u₄.rd, u₃.rd, u₂.rd, rd₁], by rw [u₄.wr, u₃.wr, u₂.wr, wr₁], ?_⟩
  have w := fun (m : Mem) (a : Addr) (x : BitVec 32) => writeW32 m a true x
  simp only [ite_true] at w
  rw [u₄.mem, u₃.mem, u₂.mem, u₃.gpr, u₂.gpr, hread, w, m₁, digest_take28_halves,
    ← writeBytes_append _ _ _ _ (by rw [hl]; simp [bytes32_length]), hl]

theorem shape384 : ShapeD (P := params384) md 48 where
  le := by decide
  len := shape.len
  out s hbx hax hin hout hd := out64_take (n := 6) (by decide) s hbx hax hin hout hd

theorem shape512_256 : ShapeD (P := params512_256) md 32 where
  le := by decide
  len := shape.len
  out s hbx hax hin hout hd := out64_take (n := 4) (by decide) s hbx hax hin hout hd

theorem shape512_224 : ShapeD (P := params512_224) md 28 where
  le := by decide
  len := shape.len
  out s hbx hax hin hout hd := out224_ok s hbx hax hin hout hd

namespace Finalize

theorem finalize384_verified :
    Verified X86.target (finalizeDigest params384) (MdStream.X86.finKD (P := params384) md 272 48) :=
  MdStream.X86.Finalize.verified_roD (P := params384) (name := "vg_sha512_compress")
    ⟨dims.1, dims.2, dims.3, dims.4, dims.5⟩ shape384 (callee.withOut (out64 6))
    (VG.Taint.constantTime (A := sseTaint) (MdStream.X86.Finalize.τ₀D params384 272 48)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Finalize.agree₀D ⟨dims.1, dims.2, dims.3, dims.4, dims.5⟩
        (by decide) h₁ h₂ hp) (by taint_decide))

theorem finalize512_256_verified :
    Verified X86.target (finalizeDigest params512_256) (MdStream.X86.finKD (P := params512_256) md 272 32) :=
  MdStream.X86.Finalize.verified_roD (P := params512_256) (name := "vg_sha512_compress")
    ⟨dims.1, dims.2, dims.3, dims.4, dims.5⟩ shape512_256 (callee.withOut (out64 4))
    (VG.Taint.constantTime (A := sseTaint) (MdStream.X86.Finalize.τ₀D params512_256 272 32)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Finalize.agree₀D ⟨dims.1, dims.2, dims.3, dims.4, dims.5⟩
        (by decide) h₁ h₂ hp) (by taint_decide))

theorem finalize512_224_verified :
    Verified X86.target (finalizeDigest params512_224) (MdStream.X86.finKD (P := params512_224) md 272 28) :=
  MdStream.X86.Finalize.verified_roD (P := params512_224) (name := "vg_sha512_compress")
    ⟨dims.1, dims.2, dims.3, dims.4, dims.5⟩ shape512_224 (callee.withOut (out64 3 ++ outHi 3))
    (VG.Taint.constantTime (A := sseTaint) (MdStream.X86.Finalize.τ₀D params512_224 272 28)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Finalize.agree₀D ⟨dims.1, dims.2, dims.3, dims.4, dims.5⟩
        (by decide) h₁ h₂ hp) (by taint_decide))

/-- A state satisfying the precondition of `finalizeDigest` with a `D`-byte
digest. -/
abbrev satD (D : Nat) : State := MdStream.X86.Finalize.satRD params 272 D

end Finalize

end VG.Proof.Sha512.X86.Stream
