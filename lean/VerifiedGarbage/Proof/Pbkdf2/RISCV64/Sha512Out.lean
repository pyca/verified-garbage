module

public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Calls
public import VerifiedGarbage.Proof.Sha512.Md
public import VerifiedGarbage.Impl.Sha512.RISCV64.Stream
import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Finalize
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# PBKDF2-HMAC's iteration on RISC-V: the SHA-512 family's digest

The code writing the first `n` doublewords of SHA-512's digest, big-endian,
from the hash value at `s1` to `s3`, and for SHA-512/224 the high half of
the fourth after three (as the streaming `finalize`s do,
`Impl/Sha512/RISCV64/Stream.lean`): what the iteration needs of it
(`OutOk`, `out_ok`, `out224_ok`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha512Out

open VG.RISCV64 VG.RISCV64.ByteLoad
open VG.Impl.Sha512.RISCV64.Stream (outW outHi)
open VG.WriteBytes (writeBytes writeBytes_frame writeBytes_append writeBytes_nil)
open VG.Spec.Sha512 (stateAt wordBytes)
open VG.Proof.Sha512.RISCV64.Stream.Finalize (flat_length take_flatMap_wordBytes beBytes_wordBytes beBytes_word
  take28)

/-- `k` doublewords of the digest are written. -/
structure OutI (s : State) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  keep : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t4 → t.gpr r = s.gpr r
  mem : t.mem = writeBytes s.mem (s.gpr .s3) (((stateAt s.mem (s.gpr .s1)).toList.take k).flatMap wordBytes)

theorem contains_pre (p : Addr) {n len : Nat} (h : n ≤ len) : (⟨p, len⟩ : Region).Contains p n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

section
variable {s : State} {D : Nat} (hD : D ≤ 64) (hin : InRegions (s.rd ++ s.wr) (s.gpr .s1) 64)
  (hout : InRegions s.wr (s.gpr .s3) D) (hd : Region.Disjoint ⟨s.gpr .s1, 64⟩ ⟨s.gpr .s3, D⟩)
include hD hin hout hd

theorem step {k : Nat} (hk : 8 * k + 8 ≤ D) {t : State} (h : OutI s k t) {rest : List Instr}
    {Q : State → Prop} (hnext : ∀ t', OutI s (k + 1) t' → WP isa (.block rest) t' Q) :
    WP isa (.block (outW k ++ rest)) t Q := by
  have hx1 : t.gpr .s1 = s.gpr .s1 := h.keep _ (by decide) (by decide) (by decide)
  have hx3 : t.gpr .s3 = s.gpr .s3 := h.keep _ (by decide) (by decide) (by decide)
  have hP := flat_length (stateAt s.mem (s.gpr .s1)) k (by omega)
  simp only [outW, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Words64.loadLE64_ok (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by omega)
    (by rw [hx1, h.rd, h.wr]; exact VG.CallLay.inRegions_sub hin (by omega) (by omega))) fun t₁ u₁ => ?_
  have k3 : t₁.gpr .s3 = s.gpr .s3 := by rw [u₁.other _ (by decide) (by decide) (by decide), hx3]
  rw [WP.block_append_iff]
  refine WP.mono (storeBE_ok (by decide) (by decide) (by decide) (by decide) (by omega)
    fun j hj => ?_) fun t₃ e₃ => hnext t₃ ?_
  · rw [k3, u₁.wr, h.wr]
    exact VG.CallLay.inRegions_sub hout (by omega) (by omega)
  subst e₃
  refine ⟨u₁.rd.trans h.rd, u₁.wr.trans h.wr, u₁.sp.trans h.sp, fun r a b c => ?_, ?_⟩
  · rw [RegUpd.gpr_write_of_ne _ _ b]
    show t₁.gpr r = _
    rw [u₁.other _ a b c]
    exact h.keep r a b c
  · have hread : t.mem.readW (s.gpr .s1 + BitVec.ofNat 64 (8 * k)) 64 =
        (stateAt s.mem (s.gpr .s1))[k]'(by omega) := by
      rw [h.mem, (writeBytes_frame (R := ⟨s.gpr .s3, D⟩) s.mem (s.gpr .s3) _ (contains_pre _ (by omega))).readW
        (r := ⟨s.gpr .s1 + BitVec.ofNat 64 (8 * k), 8⟩) (Region.contains_self _ _) ?_ (by decide)]
      · simp [stateAt]
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (Offset.sub_base _ (by omega))
    rw [RegUpd.mem_write]
    show writeBytes t₁.mem (t₁.gpr .s3 + _) (beBytes 8 (t₁.gpr .t1)) = _
    rw [k3, u₁.gpr, u₁.mem, hx1, hread, beBytes_wordBytes]
    rw [h.mem, ← hP, writeBytes_append _ _ _ _ (by rw [hP]; simp [wordBytes]; omega), List.take_add_one,
      List.getElem?_eq_getElem (by simp; omega), Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, Vector.getElem_toList]

theorem all {n : Nat} (hn : 8 * n ≤ D) {rest : List Instr} {Q : State → Prop}
    (hrest : ∀ t, OutI s n t → WP isa (.block rest) t Q) :
    ∀ j ≤ n, ∀ t, OutI s (n - j) t →
      WP isa (.block (((List.range n).drop (n - j)).flatMap outW ++ rest)) t Q := by
  intro j
  induction j with
  | zero =>
    intro _ t h
    rw [Nat.sub_zero, List.drop_eq_nil_of_le (by simp), List.flatMap_nil, List.nil_append]
    exact hrest t (by rwa [Nat.sub_zero] at h)
  | succ j ih =>
    intro hj t h
    rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons, List.append_assoc,
      List.getElem_range]
    refine step hD hin hout hd (by omega) h fun t' h' => ?_
    rw [show n - (j + 1) + 1 = n - j by omega]
    exact ih (by omega) t' (by rwa [show n - (j + 1) + 1 = n - j by omega] at h')

end

/-- What `OutOk` asks of the code, from `s`, for `D` bytes. -/
abbrev Post (D : Nat) (s s' : State) : Prop :=
  (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t4 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
    s'.mem = writeBytes s.mem (s.gpr .s3) ((Proof.Sha512.md.digest (Proof.Sha512.md.stateAt s.mem (s.gpr .s1))).take D)

/-- The first `n` doublewords of the digest. -/
theorem out_ok (n : Nat) (hn : n ≤ 8) : OutOk Proof.Sha512.md (8 * n) ((List.range n).flatMap outW) := by
  intro s hin hout hd
  have := all (s := s) (D := 8 * n) (by omega) hin hout hd (n := n) (Nat.le_refl _) (rest := [])
    (Q := Post (8 * n) s)
    (fun t h => WP.block_nil ⟨h.keep, h.rd, h.wr, h.sp, by
      rw [h.mem]; congr 1
      show _ = ((stateAt s.mem (s.gpr .s1)).toList.flatMap wordBytes).take (8 * n)
      rw [take_flatMap_wordBytes]⟩) n (Nat.le_refl _) s
    ⟨rfl, rfl, rfl, fun _ _ _ _ => rfl, by simp [writeBytes_nil]⟩
  rwa [Nat.sub_self, List.drop_zero, List.append_nil] at this

/-- The first three doublewords and the high half of the fourth, 28 bytes. -/
theorem out224_ok : OutOk Proof.Sha512.md 28 ((List.range 3).flatMap outW ++ outHi 3) := by
  intro s hin hout hd
  have := all (s := s) (D := 28) (by omega) hin hout hd (n := 3) (by decide) (rest := outHi 3)
    (Q := Post 28 s) (fun t h => ?_) 3 (Nat.le_refl _) s
    ⟨rfl, rfl, rfl, fun _ _ _ _ => rfl, by simp [writeBytes_nil]⟩
  · rwa [Nat.sub_self, List.drop_zero] at this
  have hx1 : t.gpr .s1 = s.gpr .s1 := h.keep _ (by decide) (by decide) (by decide)
  have hx3 : t.gpr .s3 = s.gpr .s3 := h.keep _ (by decide) (by decide) (by decide)
  have hP : (((stateAt s.mem (s.gpr .s1)).toList.take 3).flatMap wordBytes).length = 24 :=
    flat_length (stateAt s.mem (s.gpr .s1)) 3 (by decide)
  rw [← List.append_nil (outHi 3)]
  simp only [outHi, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadLE32_ok (by decide) (by decide) (by decide) (by omega)
    (by rw [hx1, h.rd, h.wr]; exact VG.CallLay.inRegions_sub hin (by omega) (by omega))) fun t₁ e₁ => ?_
  subst e₁
  rw [WP.block_append_iff]
  refine WP.mono (storeBE_ok (by decide) (by decide) (by decide) (by decide) (by omega)
    fun j hj => ?_) fun t₃ e₃ => WP.block_nil ?_
  · rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.wr_write,
      RegUpd.wr_write, hx3, h.wr]
    exact VG.CallLay.inRegions_sub hout (by omega) (by omega)
  subst e₃
  refine ⟨fun r a b c => ?_, h.rd, h.wr, h.sp, ?_⟩
  · simp only [RegUpd.gpr_write, a, b, ite_false]
    exact h.keep r a b c
  · have hread : t.mem.readW (s.gpr .s1 + BitVec.ofNat 64 (8 * 3 + 4)) 32 =
        s.mem.readW (s.gpr .s1 + BitVec.ofNat 64 28) 32 := by
      rw [h.mem, (writeBytes_frame (R := ⟨s.gpr .s3, 28⟩) s.mem (s.gpr .s3) _ (contains_pre _ (by omega))).readW
        (r := ⟨s.gpr .s1 + BitVec.ofNat 64 (8 * 3 + 4), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact hd.sub_left (Offset.sub_base _ (by omega))
    simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ↓reduceIte, hx1, hx3, hread, beBytes_word]
    rw [h.mem, show (8 * 3 : Nat) = (((stateAt s.mem (s.gpr .s1)).toList.take 3).flatMap wordBytes).length
        from hP.symm,
      writeBytes_append _ _ _ _ (by rw [hP]; simp [Spec.Sha256.wordBytes]), ← take28]
    rfl

end VG.Proof.Pbkdf2.RISCV64.Sha512Out
