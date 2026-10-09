import VerifiedGarbage.Proof.X25519.X86_64.Adx.Mul
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd

/-!
# X25519 on x86-64: squaring with BMI2 and ADX

`sqrX o a`: the square `[a]²` into `r8–r15` (`sqr4_ok`, `SqrProd.lean`),
reduced as in `mulX`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- `r ∉ [...]` and `a ≠ b` for literal registers. -/
local macro "nd" : tactic => `(tactic| decide)

theorem sqrX_eq (o a : Nat) :
    sqrX o a = (sqrA a ++ (sqrB a ++ (sqrC a ++ sqrD a))) ++ (reduceX ++ store4 o) := by
  simp only [sqrX, List.append_assoc]

/-- `[o] = [a]²`, at most `2p`. -/
theorem sqrXBnd_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) :
    WP isa (.block (sqrX o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base a ∧
        fe s'.mem base o ≤ 2 * VG.Spec.X25519.P := by
  rw [sqrX_eq, WP.block_append_iff]
  refine WP.mono (sqr4_ok hs ha) fun s₄ ⟨e4, k4⟩ => ?_
  have hs₄ := hs.of_keeps k4 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (reduceX_ok s₄) fun s₅ ⟨e5, b5, k5⟩ => ?_
  have hs₅ := hs₄.of_keeps k5 (by nd)
  refine WP.mono (store4_ok hs₅ ho) fun s₆ ⟨m6, g6, rd6, wr6⟩ => ?_
  have M : s₅.mem = s.mem := k5.2.1.trans k4.2.1
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_, by rw [m6, fe_st4 _ _ (by omega)]; exact b5⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr
    rw [g6, k5.1 r (by simp [*]), k4.1 r (by simp [*])]
  · rw [rd6, k5.2.2.1, k4.2.2.1]
  · rw [wr6, k5.2.2.2, k4.2.2.2]
  · rw [m6, M]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_mul
    rw [m6, fe_st4 _ _ (by omega), e5, e4]

/-- `[o] = [a]²`. -/
theorem sqrX_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) :
    WP isa (.block (sqrX o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base a :=
  WP.mono (sqrXBnd_ok hs ho ha) fun _ ⟨h, e, _⟩ => ⟨h, e⟩

theorem sqr2X_eq (o a : Nat) :
    sqr2X o a = (sqrA a ++ (sqrB a ++ (sqrC a ++ sqrD a))) ++ (reduceX2 ++ store4 o) := by
  simp only [sqr2X, List.append_assoc]

/-- `[o] = 2 · [a]²`. -/
theorem sqr2X_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) :
    WP isa (.block (sqr2X o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o =
        F s.mem base a * F s.mem base a + F s.mem base a * F s.mem base a := by
  rw [sqr2X_eq, WP.block_append_iff]
  refine WP.mono (sqr4_ok hs ha) fun s₄ ⟨e4, k4⟩ => ?_
  have hs₄ := hs.of_keeps k4 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (reduceX2_ok s₄) fun s₅ ⟨e5, k5⟩ => ?_
  have hs₅ := hs₄.of_keeps k5 (by nd)
  refine WP.mono (store4_ok hs₅ ho) fun s₆ ⟨m6, g6, rd6, wr6⟩ => ?_
  have M : s₅.mem = s.mem := k5.2.1.trans k4.2.1
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr
    rw [g6, k5.1 r (by simp [*]), k4.1 r (by simp [*])]
  · rw [rd6, k5.2.2.1, k4.2.2.1]
  · rw [wr6, k5.2.2.2, k4.2.2.2]
  · rw [m6, M]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_mul2
    rw [m6, fe_st4 _ _ (by omega), e5]
    exact congrArg (fun x => 2 * x % VG.Spec.X25519.P) e4

end VG.Proof.X25519.X86_64
