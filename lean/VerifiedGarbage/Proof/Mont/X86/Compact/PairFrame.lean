module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Row

/-! # The paired-word loop's frame does not depend on its arithmetic values -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem pairLoop_frame {s : State} {W : Addr} {L S bx w N : Nat}
    (hw : Ws s W L) (positive : 0 < N) (even : N % 2 = 0)
    (hedi : PtrAt s W .edi S) (hecx : PtrAt s W .ecx bx) (hebp : PtrAt s W .ebp w)
    (hesi : (s.gpr .esi).toNat = 4 * N)
    (multFit : S + Rt.multOff + 4 ≤ L) (srcFit : bx + 4 * N ≤ L) (dstFit : w + 4 * N ≤ L) :
    WP isa (.loop (.block Rt.pairStep) .ne) s fun t =>
      Outside W w (4 * N) s.mem t.mem ∧ PtrAt t W .ebp (w + 4 * N) ∧
      PtrAt t W .ecx (bx + 4 * N) ∧ (t.gpr .esi).toNat = 0 ∧ Keeps clob6 s t := by
  have nowrap := hw.nowrap
  let I : Nat → State → Prop := fun j t =>
    Keeps clob6 s t ∧ PtrAt t W .ecx (bx + 4 * j) ∧ PtrAt t W .ebp (w + 4 * j) ∧
    (t.gpr .esi).toNat = 4 * (N - j) ∧ Outside W w (4 * j) s.mem t.mem
  have initial : I 0 s := by
    refine ⟨Keeps.refl _ _, ?_, ?_, ?_, ?_⟩
    · simpa only [Nat.mul_zero, Nat.add_zero] using hecx
    · simpa only [Nat.mul_zero, Nat.add_zero] using hebp
    · simpa only [Nat.sub_zero] using hesi
    · exact Outside.refl _ _ _ _
  refine WP.mono (WP.loop (M := isa) (Q := I N)
    (fun m t => ∃ j, m = N - j ∧ j < N ∧ j % 2 = 0 ∧ I j t) ?_ N s
    ⟨0, rfl, positive, rfl, initial⟩) ?_
  · rintro m t ⟨j, rfl, index, pair, K, cx, bp, count, O⟩
    have pairFit : j + 2 ≤ N := by omega
    have ht := hw.of_keeps K
    have di : PtrAt t W .edi S := by rw [PtrAt, K.1 .edi (by decide)]; exact hedi
    unfold Rt.pairStep
    rw [List.append_assoc]
    refine WP.block_append (WP.mono (macAt_ok (mo := Rt.multOff) (d := 0) ht di cx bp multFit
      (by omega) (by omega)) fun a ⟨M₁, _, K₁⟩ => ?_)
    have W₁ : Outside W (w + 4 * j) 4 t.mem a.mem := by
      rw [M₁, Nat.add_zero]
      exact writeW32_outside _ _ _ (by omega)
    have O₁ : Outside W w (4 * (j + 1)) s.mem a.mem :=
      (O.mono (by omega) (by omega)).trans (W₁.mono (by omega) (by omega))
    have di₁ : PtrAt a W .edi S := by rw [PtrAt, K₁.1 .edi (by decide)]; exact di
    have cx₁ : PtrAt a W .ecx (bx + 4 * j) := by rw [PtrAt, K₁.1 .ecx (by decide)]; exact cx
    have bp₁ : PtrAt a W .ebp (w + 4 * j) := by rw [PtrAt, K₁.1 .ebp (by decide)]; exact bp
    refine WP.block_append (WP.mono (macAt_ok (mo := Rt.multOff) (d := 4)
      (ht.of_keeps K₁) di₁ cx₁ bp₁ multFit (by omega) (by omega)) fun b ⟨M₂, _, K₂⟩ => ?_)
    have W₂ : Outside W (w + 4 * j + 4) 4 a.mem b.mem := by
      rw [M₂]
      exact writeW32_outside _ _ _ (by omega)
    have O₂ : Outside W w (4 * (j + 2)) s.mem b.mem :=
      (O₁.mono (by omega) (by omega)).trans (W₂.mono (by omega) (by omega))
    have Kab := K₁.trans K₂
    have cx₂ : PtrAt b W .ecx (bx + 4 * j) := by rw [PtrAt, Kab.1 .ecx (by decide)]; exact cx
    have bp₂ : PtrAt b W .ebp (w + 4 * j) := by rw [PtrAt, Kab.1 .ebp (by decide)]; exact bp
    have count₂ : (b.gpr .esi).toNat = 4 * (N - j) := by rw [Kab.1 .esi (by decide)]; exact count
    refine WP.mono (pairCtl_ok cx₂ bp₂ count₂ pairFit) fun u ⟨Mu, cu, pu, su, zu, Ku⟩ => ?_
    have next : I (j + 2) u := by
      refine ⟨(K.trans (Kab.mono (by decide))).trans (Ku.mono (by decide)), ?_, ?_, su, ?_⟩
      · rw [show bx + 4 * (j + 2) = bx + 4 * j + 8 by omega]; exact cu
      · rw [show w + 4 * (j + 2) = w + 4 * j + 8 by omega]; exact pu
      · rw [Mu]; exact O₂
    by_cases done : j + 2 = N
    · exact Or.inl ⟨by simp only [eval, zu, done, decide_true, Option.map_some, Bool.not_true], done ▸ next⟩
    · exact Or.inr ⟨by simp only [eval, zu, decide_eq_false done, Option.map_some, Bool.not_false],
        N - (j + 2), by omega, j + 2, rfl, by omega, by omega, next⟩
  · rintro t ⟨K, C, P, Count, O⟩
    exact ⟨O, P, C, by simpa only [Nat.sub_self, Nat.mul_zero] using Count, K⟩

end VG.Proof.Mont.X86.Compact
