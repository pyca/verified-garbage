import VerifiedGarbage.Proof.Ed448.AArch64.ScalarOperands
import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLit
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.TCB.AArch64.Target

/-!
# Ed448 scalar reduction on AArch64: the whole function

The contract the proof is written against (the facts of
`Spec.Ed448.scalarReduceContract` it uses, stated for AArch64), and the
correctness of `vg_ed448_scalar_reduce` against it: the working space is
written only where the callee-saved registers are saved, so the input is
read unchanged; they are restored before the result is written.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps word off Outside ofs contains_sc)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-- A buffer of `n` bytes is its own encoding. -/
theorem bytesAt_encode (m : Mem) (q : Addr) (n : Nat) :
    bytesAt m q n = Spec.Ed448.encodeLE n (decodeLE (bytesAt m q n)) := by
  rw [encodeLE_eq, decodeLE_eq, bytesAt_eq, Proof.X25519.leNum_bytesAt_read,
    ← Proof.X25519.bytesAt_leBytes]

/-- `vg_ed448_scalar_reduce(out = x0, wide = x1, scratch = x2)`. -/
def scalarReduceLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x1, 114⟩] ∧ s.wr = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x2, 8192⟩] ∧
    (⟨s.gpr .x1, 114⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩
  post s t := bytesAt t.mem (s.gpr .x0) 57 = Spec.Ed448.scalarReduce (bytesAt s.mem (s.gpr .x1) 114)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2

/-- `finish`: the callee-saved registers restored, and the remainder written to the 57 bytes at `q`. -/
theorem finish_ok {s : State} {base q : Addr} (hb : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) {g : Reg → BitVec 64} (hsv : Saved base g s.mem)
    (hq : s.gpr .x0 = q) (hwo : (⟨q, 57⟩ : Region) ∈ s.wr) :
    WP isa (.block finish) s fun t =>
      bytesAt t.mem q 57 = Spec.Ed448.encodeLE 57 (rem s) ∧ (∀ p ∈ saved, t.gpr p.1 = g p.1) ∧
      (∀ r, r ∉ Reg.x12 :: savedRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp := by
  rw [finish, List.append_assoc, WP.block_append_iff]
  refine WP.mono (restoreRegs_ok hb hw hsv) fun a ⟨ra, ka⟩ => ?_
  have qa : a.gpr .x0 = q := (ka.gpr _ (by decide)).trans hq
  refine WP.mono (outStore_ok qa (ka.wr ▸ hwo)) fun t ⟨vt, _, gt, _, _, spt⟩ => ?_
  refine ⟨?_, fun p hp => (gt _ ((by decide : ∀ p ∈ saved, p.1 ≠ .x12) p hp)).trans (ra p hp),
    fun r hr => ?_, spt.trans ka.sp⟩
  · rw [bytesAt_encode, vt, show rem a = rem s from Keeps.rv_eq ka (by decide)]
  · simp only [List.mem_cons, not_or] at hr
    rw [gt r hr.1, ka.gpr r hr.2]

theorem scalarReduce_correct {s : State} (hs : scalarReduceLocal.pre s) :
    WP isa scalarReduce s fun t => abiPreserved s t ∧ scalarReduceLocal.post s t := by
  apply WP.withPreservedV (hc := by lit_decide)
  obtain ⟨hr, hw, hd⟩ := hs
  have hws : (⟨s.gpr .x2, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  have hwo : (⟨s.gpr .x0, 57⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [scalarReduce]
  apply WP.seq
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (saveRegs_ok .x2 rfl hws) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₁) fun s₂ ⟨c₂, k₂⟩ => ?_
  have x1₂ : s₂.gpr .x1 = s.gpr .x1 := (k₂.gpr _ (by decide)).trans (congrFun g₁ _)
  have rdw₂ : s₂.rd ++ s₂.wr = s.rd ++ s.wr := by rw [k₂.rd, k₂.wr, rd₁, wr₁]
  have inw : ∀ d n, d + n ≤ 114 → InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x1 + BitVec.ofNat 64 d) n :=
    fun d n h => ⟨⟨s.gpr .x1, 114⟩, by rw [rdw₂, hr]; simp,
      by rw [x1₂]; exact Offset.contains_base _ h (by omega)⟩
  refine WP.mono (init114_ok s₂ (inw 112 1 (by omega)) (inw 113 1 (by omega)))
    fun s₃ ⟨v₃, b₃, k₃⟩ => ?_
  have c₃ : Consts s₃ := c₂.of_keeps k₃ (by decide)
  have x1₃ : s₃.gpr .x1 = s.gpr .x1 := (k₃.gpr _ (by decide)).trans x1₂
  have m₃ : s₃.mem = s₁.mem := k₃.mem.trans k₂.mem
  apply WP.seq
  have hi : LoopInv 114 s₃ 14 s₃ := by
    refine ⟨by decide, by decide, b₃, ?_, Keeps.refl _ _⟩
    rw [v₃, k₃.mem, k₃.gpr .x1 (by decide)]
    simp only [Nat.reduceMul, Nat.reduceSub]
    have hlt := decodeLE_lt' (bytesAt s₂.mem (s₂.gpr .x1 + BitVec.ofNat 64 112) 2)
    rw [bytesAt_length] at hlt
    have : (256 : Nat) ^ 2 < L := by decide +kernel
    exact (Nat.mod_eq_of_lt (by omega)).symm
  refine WP.mono (scalarLoop_ok s₃ c₃ (by decide) hi fun k hk => by
      rw [k₃.rd, k₃.wr, ← x1₂.trans x1₃.symm]
      exact inw (8 * k) 8 (by omega)) fun s₄ ⟨v₄, k₄⟩ => ?_
  have x2₄ : s₄.gpr .x2 = s.gpr .x2 := by
    rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), g₁]
  have x0₄ : s₄.gpr .x0 = s.gpr .x0 := by
    rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), g₁]
  have wr₄ : s₄.wr = s.wr := by rw [k₄.wr, k₃.wr, k₂.wr, wr₁]
  have sv₄ : Saved (s.gpr .x2) s.gpr s₄.mem := by rw [k₄.mem, m₃]; exact sv₁
  refine WP.mono (finish_ok x2₄ (wr₄ ▸ hws) sv₄ x0₄ (wr₄ ▸ hwo)) fun t ⟨bt, rt, gt, spt⟩ => ?_
  refine ⟨⟨fun r hpres => ?_, spt.trans (k₄.sp.trans (k₃.sp.trans (k₂.sp.trans sp₁)))⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hpres
    rcases hpres with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt (.x19, 0) (by decide)
    · exact rt (.x20, 8) (by decide)
    · exact rt (.x21, 16) (by decide)
    · exact rt (.x22, 24) (by decide)
    · exact rt (.x23, 32) (by decide)
    · exact rt (.x24, 40) (by decide)
    · exact rt (.x25, 48) (by decide)
    · exact rt (.x26, 56) (by decide)
    all_goals
      rw [gt _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), g₁]
  · show bytesAt t.mem (s.gpr .x0) 57 = Spec.Ed448.scalarReduce (bytesAt s.mem (s.gpr .x1) 114)
    rw [bt, v₄, x1₃, m₃, bytesAt_outside o₁ (by decide) hd (by decide)]
    rfl

end VG.Proof.Ed448.AArch64
