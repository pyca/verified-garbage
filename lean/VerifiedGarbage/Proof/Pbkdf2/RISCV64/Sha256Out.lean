module

public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Calls
public import VerifiedGarbage.Proof.Sha256.Md
public import VerifiedGarbage.Impl.Sha256.RISCV64.Stream
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Finalize
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# PBKDF2-HMAC's iteration on RISC-V: SHA-256's digest

The code writing the first `n` words of SHA-256's digest, big-endian, from
the hash value at `s1` to `s3` (as SHA-256's streaming `finalize` does,
`Impl/Sha256/RISCV64/Stream.lean`): what the iteration needs of it
(`OutOk`, `out_ok`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha256Out

open VG.RISCV64 VG.RISCV64.ByteLoad
open VG.Impl.Sha256.RISCV64.Stream (outW)
open VG.WriteBytes (writeBytes writeBytes_frame writeBytes_append writeBytes_nil)
open VG.Spec.Sha256 (stateAt wordBytes)
open VG.Proof.Sha256.RISCV64.Stream.Finalize (flat_length take_flatMap_wordBytes beBytes_word)

/-- `k` words of the digest are written. -/
structure OutI (s : State) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  keep : ∀ r, r ≠ .t1 → r ≠ .t2 → t.gpr r = s.gpr r
  mem : t.mem = writeBytes s.mem (s.gpr .s3) (((stateAt s.mem (s.gpr .s1)).toList.take k).flatMap wordBytes)

theorem contains_pre (p : Addr) {n len : Nat} (h : n ≤ len) : (⟨p, len⟩ : Region).Contains p n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

section
variable {s : State} {D : Nat} (hD : D ≤ 32) (hin : InRegions (s.rd ++ s.wr) (s.gpr .s1) 32)
  (hout : InRegions s.wr (s.gpr .s3) D) (hd : Region.Disjoint ⟨s.gpr .s1, 32⟩ ⟨s.gpr .s3, D⟩)
include hD hin hout hd

theorem step {k : Nat} (hk : 4 * k + 4 ≤ D) {t : State} (h : OutI s k t) {rest : List Instr}
    {Q : State → Prop} (hnext : ∀ t', OutI s (k + 1) t' → WP isa (.block rest) t' Q) :
    WP isa (.block (outW k ++ rest)) t Q := by
  have hx1 : t.gpr .s1 = s.gpr .s1 := h.keep _ (by decide) (by decide)
  have hx3 : t.gpr .s3 = s.gpr .s3 := h.keep _ (by decide) (by decide)
  have hP := flat_length (stateAt s.mem (s.gpr .s1)) k (by omega)
  simp only [outW, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadLE32_ok (by decide) (by decide) (by decide) (by omega)
    (by rw [hx1, h.rd, h.wr]; exact VG.CallLay.inRegions_sub hin (by omega) (by omega))) fun t₁ e₁ => ?_
  subst e₁
  rw [WP.block_append_iff]
  refine WP.mono (storeBE_ok (by decide) (by decide) (by decide) (by decide) (by omega)
    fun j hj => ?_) fun t₃ e₃ => hnext t₃ ?_
  · rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.wr_write,
      RegUpd.wr_write, hx3, h.wr]
    exact VG.CallLay.inRegions_sub hout (by omega) (by omega)
  subst e₃
  refine ⟨h.rd, h.wr, h.sp, fun r a b => ?_, ?_⟩
  · simp only [RegUpd.gpr_write, a, b, ite_false]
    exact h.keep r a b
  · have hread : t.mem.readW (s.gpr .s1 + BitVec.ofNat 64 (4 * k)) 32 =
        (stateAt s.mem (s.gpr .s1))[k]'(by omega) := by
      rw [h.mem, (writeBytes_frame (R := ⟨s.gpr .s3, D⟩) s.mem (s.gpr .s3) _ (contains_pre _ (by omega))).readW
        (r := ⟨s.gpr .s1 + BitVec.ofNat 64 (4 * k), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
      · simp [stateAt]
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (Offset.sub_base _ (by omega))
    simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ↓reduceIte, hx1, hx3, hread, beBytes_word]
    rw [h.mem, ← hP, writeBytes_append _ _ _ _ (by rw [hP]; simp [wordBytes]; omega), List.take_add_one,
      List.getElem?_eq_getElem (by simp; omega), Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, Vector.getElem_toList]

theorem all {n : Nat} (hn : 4 * n ≤ D) {rest : List Instr} {Q : State → Prop}
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

/-- The first `n` words of the digest. -/
theorem out_ok (n : Nat) (hn : n ≤ 8) : OutOk Proof.Sha256.md (4 * n) ((List.range n).flatMap outW) := by
  intro s hin hout hd
  have := all (s := s) (D := 4 * n) (by omega) hin hout hd (n := n) (Nat.le_refl _) (rest := [])
    (Q := fun s' => (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t4 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .s3) ((Proof.Sha256.md.digest (Proof.Sha256.md.stateAt s.mem (s.gpr .s1))).take (4 * n)))
    (fun t h => WP.block_nil ⟨fun r a b _ => h.keep r a b, h.rd, h.wr, h.sp, by
      rw [h.mem]; congr 1
      show _ = ((stateAt s.mem (s.gpr .s1)).toList.flatMap wordBytes).take (4 * n)
      rw [take_flatMap_wordBytes]⟩) n (Nat.le_refl _) s
    ⟨rfl, rfl, rfl, fun _ _ _ => rfl, by simp [writeBytes_nil]⟩
  rwa [Nat.sub_self, List.drop_zero, List.append_nil] at this

end VG.Proof.Pbkdf2.RISCV64.Sha256Out
