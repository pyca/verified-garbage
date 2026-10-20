module

public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Inv
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! # A row of `t̂` between the pairs of the matrix

`row_step`: row `r` of `t̂`, once the matrix holds its entries (`Kem16.kgRow`,
proven by `fused_row_readyW` over `Â` as memory holds it), keeps the
interleaved invariant `IL`: it writes neither the matrix, the third state, nor the
blocks of `ek` the third state has absorbed. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)

variable {P : KemLay}

theorem stR_scratch (s₀ : State) : stR (kA s₀ 3) = R (kA s₀) 3 0 200 := by
  simp only [stR, R, ptr_zero]

/-- The writes of row `i` miss the third state. -/
theorem row_st {s₀ : State} (hp : Pre P s₀) (i : Nat) (hi : i < P.k) :
    ∀ q ∈ rowWrites P s₀ i, (stR (kA s₀ 3)).Disjoint q := by
  have hw := hp.wf
  intro q hq
  rw [stR_scratch]
  simp only [rowWrites, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inr (.inl (by lom)))
  · exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inl (by decide))
  · exact hp.args.rdisj (by decide) (by decide) (by kl) (by kl) (.inl (by decide))

/-- The writes of row `i` lie in the written arguments. -/
theorem row_wr {s₀ s : State} (hp : Pre P s₀) (hk : KB P s₀ s) (i : Nat) (hi : i < P.k) :
    ∀ q ∈ rowWrites P s₀ i, ∃ q' ∈ s.wr, Region.Sub q q' := by
  have hw := hp.wf
  intro q hq
  rw [hk.wr, hp.wr]
  simp only [rowWrites, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨⟨kA s₀ 3, kL P 3⟩, by simp, R.sub (by kl)⟩
  · exact ⟨⟨kA s₀ 1, kL P 1⟩, by simp, R.sub (by kl)⟩
  · exact ⟨⟨kA s₀ 2, kL P 2⟩, by simp, R.sub (by kl)⟩

/-- **A row of `t̂`**, once the matrix holds its entries. -/
theorem row_step {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P) {n r h : Nat}
    (hrk : r < P.k) (hn : P.k * (r + 1) ≤ n) (H : IL P s₀ n r h s) :
    WP isa (Impl.MlKem.AArch64.Kem16.kgRow P r) s (IL P s₀ n (r + 1) h) := by
  have hw := hp.wf
  have kb := H.b.kb
  have tl : TLW P s₀ s.mem (s.gpr .x24) n r s :=
    ⟨⟨kb, H.b.rho, H.b.sig, rfl, H.le, fun e he => ⟨H.b.red e he, rfl⟩⟩, H.sp, H.dk, H.rows⟩
  have rt := readonly_rows hp kb H.tables.gamma H.tables.gammaRead H.tables.gammaApart
  have ha : (polyRegion (s.gpr .x28 + BitVec.ofNat 64 (TP P))).Disjoint
      ⟨s.syms "VG_MLKEM_GAMMA", 512⟩ := by
    rw [kb.x28]
    exact (rt.apart r hrk _ (by simp [rowWrites])).symm
  refine WP.mono_syms (fused_row_readyW hp hr hrk hn tl H.errors rt.table rt.read ha)
    fun t ⟨tlt, et, ft⟩ hs => ?_
  have kbt := tlt.c.kb
  have entries : ∀ e < n, polyAtW 16 t.mem (AR s₀ e) = polyAtW 16 s.mem (AR s₀ e) :=
    fun e he => (tlt.c.ahat e he).2
  have hek : 136 * h ≤ kL P 1 := by
    have := Nat.mul_le_mul_left 384 H.rk
    have := H.hr
    have := hw.facts
    simp only [kL]; lom
  have hek' : 136 * h ≤ P.ekLen := hek
  have hek0 : 0 + 136 * h ≤ kL P 1 := by omega
  have hhr := H.hr
  refine ⟨⟨kbt, tlt.c.rho, tlt.c.sig, by rw [tlt.c.x24]; exact H.b.acc, fun e he => (tlt.c.ahat e he).1,
    fun e he => ?_⟩, tlt.sp, et, tlt.dk, ?_, hn, H.le, by omega, ?_, by omega, ?_,
    H.tstk.of hs (by rw [kbt.sp, kb.sp])⟩
  · have r₀ := H.b.res e he
    simp only [aAtW, cw, ite_true] at r₀ ⊢
    rw [show kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * e) = AR s₀ e from rfl, entries e he]
    exact r₀
  · intro i' hi'
    have hrow : P.k * (i' + 1) ≤ n :=
      Nat.le_trans (Nat.mul_le_mul_left P.k (show i' + 1 ≤ r + 1 by omega)) hn
    rw [tVW_congr (m := t.mem) (m' := s.mem) fun j hj => entries _ (lt_row hrow hj)]
    exact tlt.ek i' hi'
  · rw [VG.Proof.Sha3.AArch64.Hybrid.X3.stateAt_frame ft (row_st hp r hrk), H.hash]
    refine hstate_prefix hek' ?_
    have e1 : kA s₀ 1 = kA s₀ 1 + BitVec.ofNat 64 0 := (ptr_zero _).symm
    rw [e1, bytesAt_frame ft (fun q hq => ?_) (by have := kL_le hw 1; omega)]
    simp only [rowWrites, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hp.args.rdisj (b₁ := 1) (o₁ := 0) (by decide) (by decide) hek0 (by kl) (.inl (by decide))
    · exact hp.args.rdisj (b₁ := 1) (o₁ := 0) (by decide) (by decide) hek0 (by kl)
        (.inr (.inl (by have := H.hr; omega)))
    · exact hp.args.rdisj (b₁ := 1) (o₁ := 0) (by decide) (by decide) hek0 (by kl) (.inl (by decide))
  · exact H.tables.frame hs (by rw [kbt.rd, kb.rd]) (by rw [kbt.wr, kb.wr]) (by rw [kbt.sp, kb.sp])
      (ft.sub (row_wr hp kb r hrk))

end VG.Proof.MlKem.AArch64.KeyGen
