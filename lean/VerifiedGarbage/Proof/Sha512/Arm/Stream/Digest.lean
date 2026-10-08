import VerifiedGarbage.Proof.Sha512.Arm.Stream.Finalize
import VerifiedGarbage.Proof.Sha512.Digest

/-!
# Streaming SHA-384, SHA-512/256 and SHA-512/224 on ARMv7: `finalize`

`finalizeDigest` is the generic `finalize` (`Impl/MdStream/Arm.lean`) with a
digest of the first 48, 32 or 28 bytes of the final hash value
(`params384`, `params512_256`, `params512_224`), so it is verified by the
generic proof of a `finalize` writing a prefix of the final hash value
(`Finalize.verifiedD`), given what writing that prefix does (`ShapeD`), and
constant time by the taint analysis of its code.
-/

namespace VG.Proof.Sha512.Arm.Stream.Finalize

open VG VG.Arm VG.Proof.MdStream VG.Proof.MdStream.Arm
open VG.Impl.Sha512.Arm.Stream (outW outHi params384 params512_256 params512_224 finalizeDigest)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_frame)
open VG.Proof.Sha512.Arm (readW_hi)
open VG.Spec.Sha512 (stateAt wordBytes)

/-- The first `n` words of the hash value, big-endian, are the first `8 n`
bytes of its output. -/
theorem take_flatMap_wordBytes (l : List Spec.Sha512.Word) (n : Nat) :
    (l.flatMap wordBytes).take (8 * n) = (l.take n).flatMap wordBytes := by
  induction l generalizing n with
  | nil => simp
  | cons w l ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [List.flatMap_cons, List.take_succ_cons, List.flatMap_cons, List.take_append,
        List.take_of_length_le (by simp [wordBytes]; omega), show 8 * (n + 1) - (wordBytes w).length = 8 * n by
          simp [wordBytes]; omega, ih]

/-- The first `n` words of the digest, to `r6`, where `8 n` bytes may be written. -/
theorem out_take {n : Nat} (hn : n ≤ 8) (s : State) (f₀ : (s.gpr .r0).toNat + 64 ≤ 2 ^ 32)
    (f₆ : (s.gpr .r6).toNat + 8 * n ≤ 2 ^ 32) (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0)) 64)
    (hout : InRegions s.wr (State.addr (s.gpr .r6)) (8 * n))
    (hd : Region.Disjoint ⟨State.addr (s.gpr .r0), 64⟩ ⟨State.addr (s.gpr .r6), 8 * n⟩) :
    WP isa (.block ((List.range n).flatMap outW)) s fun s' => (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (State.addr (s.gpr .r6))
        ((Proof.Sha512.md.digest (Proof.Sha512.md.stateAt s.mem (State.addr (s.gpr .r0)))).take (8 * n)) := by
  rw [← List.append_nil ((List.range n).flatMap outW)]
  refine out_ok (W := 8 * n) (by omega) f₀ f₆ hd n (Nat.le_refl _) [] s _ rfl rfl hin hout
    fun s' g rd wr sp m => WP.block_nil ⟨g, rd, wr, sp, ?_⟩
  rw [m]
  exact congrArg _ (take_flatMap_wordBytes _ n).symm

/-- `(List.range 3).flatMap outW ++ outHi 3` writes the first 28 bytes of the digest. -/
theorem out224_ok (s : State) (f₀ : (s.gpr .r0).toNat + 64 ≤ 2 ^ 32) (f₆ : (s.gpr .r6).toNat + 28 ≤ 2 ^ 32)
    (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0)) 64)
    (hout : InRegions s.wr (State.addr (s.gpr .r6)) 28)
    (hd : Region.Disjoint ⟨State.addr (s.gpr .r0), 64⟩ ⟨State.addr (s.gpr .r6), 28⟩) :
    WP isa (.block ((List.range 3).flatMap outW ++ outHi 3)) s fun s' =>
      (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (State.addr (s.gpr .r6))
        ((Proof.Sha512.md.digest (Proof.Sha512.md.stateAt s.mem (State.addr (s.gpr .r0)))).take 28) := by
  refine out_ok (W := 28) (by decide) f₀ f₆ hd 3 (by decide) _ s _ rfl rfl hin hout
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  have hl : (((stateAt s.mem (State.addr (s.gpr .r0))).toList.take 3).flatMap wordBytes).length = 24 :=
    flat_length _ 3 (by decide)
  -- The high half of word 3 is not yet overwritten.
  have hread : s₁.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 28) 32 =
      s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 28) 32 := by
    rw [m₁]
    refine (writeBytes_frame _ _ _ (R := ⟨State.addr (s.gpr .r6), 28⟩) ?_).readW
      (r := ⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 28, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    · rw [hl]; simpa using Offset.contains_base (State.addr (s.gpr .r6)) (d := 0) (n := 24) (k := 28)
        (by decide) (by decide)
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact hd.sub_left (Offset.sub_base _ (by decide))
  simp only [outHi]
  refine wp_ldr (a := State.addr (s.gpr .r0) + BitVec.ofNat 64 28) (by decide)
    (by rw [g₁ _ (by decide) (by decide), addr_add (by omega)])
    (by rw [rd₁, wr₁]; exact InRegions.offset hin (by decide) (by decide)) fun s₂ u₂ => wp_rev fun s₃ u₃ => ?_
  refine wp_str (a := State.addr (s.gpr .r6) + BitVec.ofNat 64 24) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide) (by decide), addr_add (by omega)])
    (by rw [u₃.wr, u₂.wr, wr₁]; exact InRegions.offset hout (by decide) (by decide)) fun s₄ g₄ =>
      WP.block_nil ⟨fun r h9 h10 => by rw [g₄.gpr, u₃.other r h10, u₂.other r h10, g₁ r h9 h10],
        by rw [g₄.rd, u₃.rd, u₂.rd, rd₁], by rw [g₄.wr, u₃.wr, u₂.wr, wr₁], by rw [g₄.sp, u₃.sp, u₂.sp, sp₁], ?_⟩
  have e24 : ((Proof.Sha512.md.digest (Proof.Sha512.md.stateAt s.mem (State.addr (s.gpr .r0)))).take 28) =
      ((stateAt s.mem (State.addr (s.gpr .r0))).toList.take 3).flatMap wordBytes ++
        Spec.Sha256.wordBytes (s.mem.readW (State.addr (s.gpr .r0) + BitVec.ofNat 64 28) 32) := by
    rw [Proof.Sha512.digest_take28, ← Proof.Sha512.digest_take _ _ (n := 3) (by decide),
      show Proof.Sha512.md.digest (Proof.Sha512.md.stateAt s.mem (State.addr (s.gpr .r0))) =
        (stateAt s.mem (State.addr (s.gpr .r0))).toList.flatMap wordBytes from rfl,
      take_flatMap_wordBytes]
    rfl
  rw [g₄.mem, u₃.mem, u₃.gpr, u₂.gpr, u₂.mem, hread, writeW_rev, m₁, e24, ← hl,
    writeBytes_append _ _ _ _ (by rw [hl]; simp [Spec.Sha256.wordBytes])]

theorem shape384 : ShapeD (P := params384) Proof.Sha512.md 48 where
  le := by decide
  len := shape.len
  out s f₀ f₆ hin hout hd := out_take (n := 6) (by decide) s f₀ f₆ hin hout hd

theorem shape512_256 : ShapeD (P := params512_256) Proof.Sha512.md 32 where
  le := by decide
  len := shape.len
  out s f₀ f₆ hin hout hd := out_take (n := 4) (by decide) s f₀ f₆ hin hout hd

theorem shape512_224 : ShapeD (P := params512_224) Proof.Sha512.md 28 where
  le := by decide
  len := shape.len
  out s f₀ f₆ hin hout hd := out224_ok s f₀ f₆ hin hout hd

theorem finalize384_verified :
    Verified Arm.target (finalizeDigest params384) (MdStream.Arm.finKD (P := params384) Proof.Sha512.md 48) :=
  MdStream.Arm.Finalize.verifiedD (P := params384) (name := "vg_sha512_compress")
    ⟨dims.1, dims.2, dims.3, dims.4, dims.5, dims.6⟩ shape384 (callee.withOut ((List.range 6).flatMap outW))
    (VG.Taint.constantTime (A := taint) (MdStream.Arm.Finalize.τ₀D params384 48)
      (fun _ _ h₁ h₂ hp => MdStream.Arm.Finalize.agree₀D h₁ h₂ hp) (by taint_decide))

theorem finalize512_256_verified :
    Verified Arm.target (finalizeDigest params512_256)
      (MdStream.Arm.finKD (P := params512_256) Proof.Sha512.md 32) :=
  MdStream.Arm.Finalize.verifiedD (P := params512_256) (name := "vg_sha512_compress")
    ⟨dims.1, dims.2, dims.3, dims.4, dims.5, dims.6⟩ shape512_256 (callee.withOut ((List.range 4).flatMap outW))
    (VG.Taint.constantTime (A := taint) (MdStream.Arm.Finalize.τ₀D params512_256 32)
      (fun _ _ h₁ h₂ hp => MdStream.Arm.Finalize.agree₀D h₁ h₂ hp) (by taint_decide))

theorem finalize512_224_verified :
    Verified Arm.target (finalizeDigest params512_224)
      (MdStream.Arm.finKD (P := params512_224) Proof.Sha512.md 28) :=
  MdStream.Arm.Finalize.verifiedD (P := params512_224) (name := "vg_sha512_compress")
    ⟨dims.1, dims.2, dims.3, dims.4, dims.5, dims.6⟩ shape512_224
    (callee.withOut ((List.range 3).flatMap outW ++ outHi 3))
    (VG.Taint.constantTime (A := taint) (MdStream.Arm.Finalize.τ₀D params512_224 28)
      (fun _ _ h₁ h₂ hp => MdStream.Arm.Finalize.agree₀D h₁ h₂ hp) (by taint_decide))

/-- A state satisfying the precondition of `finalizeDigest` with a `D`-byte
digest. -/
abbrev satD (D : Nat) : State := MdStream.Arm.Finalize.satD params D

end VG.Proof.Sha512.Arm.Stream.Finalize
