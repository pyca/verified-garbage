module

import VerifiedGarbage.Proof.Mont.X86.Compact.Length
public import VerifiedGarbage.Proof.Mont.X86.Rt.Row
public import VerifiedGarbage.Proof.Mont.X86.Compact.Args

/-! # Paired-word product rows in the prepared workspace -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

/-- The window of `N + 2` words at `ebp = W + w` `+= [edi + Rt.multOff] ·` the
number of `N` words at the offset argument `xi`, when the sum fits. -/
theorem mulRow_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws s W L) (ha : Args s W L A)
    (base : (A 0).toNat = W.toNat) {bx S w N : Nat}
    (width : w32 s.mem W 48 * 8 = 4 * N) (hN : 0 < N) (hN32 : 4 * N < 2 ^ 32)
    (headerFit : 52 ≤ L) (headerApart : 52 ≤ w)
    (ptr : List Instr)
    (ptr_ok : ∀ t, t.mem = s.mem → Ws t W L → Args t W L A →
      WP isa (.block ptr) t fun u => PtrAt u W .ecx bx ∧
        u.mem = t.mem ∧ Keeps [.ecx, .edx] t u)
    (hedi : PtrAt s W .edi S) (hebp : PtrAt s W .ebp w)
    (hbL : bx + 4 * N ≤ L) (hwL : w + 4 * N + 8 ≤ L) (hmL : S + Rt.multOff + 4 ≤ L)
    (hsep : bx + 4 * N ≤ w ∨ w + 4 * N + 8 ≤ bx) (hsm : S + Rt.multOff + 4 ≤ w ∨ w + 4 * N + 8 ≤ S + Rt.multOff)
    (hlt : val32 s.mem W w (N + 2) + w32 s.mem W (S + Rt.multOff) * val32 s.mem W bx N < 2 ^ (32 * (N + 2))) :
    WP isa (Compact.mulRow ptr) s fun u =>
      Outside W w (4 * N + 8) s.mem u.mem ∧
      val32 u.mem W w (N + 2) = val32 s.mem W w (N + 2) + w32 s.mem W (S + Rt.multOff) * val32 s.mem W bx N ∧
      PtrAt u W .ebp w ∧ Keeps clob6 s u := by
  have hnw := hw.nowrap
  unfold Compact.mulRow
  -- The pointer to the number, and the count.
  have width_ok : w32 s.mem W 48 * 2 ^ (3 + 0) % 2 ^ 32 = 4 * N := by
    rw [show 2 ^ (3 + 0) = 8 from rfl, width, Nat.mod_eq_of_lt hN32]
  have setup : WP isa (.block ([.mov .ebx (.imm 0)] ++ ptr ++ Compact.lenTimes .esi .eax 0)) s
      fun (t : State) => Keeps [.eax, .ebx, .ecx, .edx, .esi] s t ∧ t.mem = s.mem ∧ t.gpr .ebx = 0 ∧ PtrAt t W .ecx bx ∧
        (t.gpr .esi).toNat = 4 * N := by
    simp only [List.cons_append, List.nil_append]
    refine wp_movS rfl fun s₀ u₀ _ => ?_
    refine WP.block_append (WP.mono (ptr_ok s₀ u₀.mem (hw.of_keeps u₀.keeps) (ha.of_upd u₀ (by decide)))
      fun s₁ ⟨e₁, m₁, K₁⟩ => ?_)
    have ha₁ : Args s₁ W L A := (ha.of_upd u₀ (by decide)).of_keeps K₁ (by decide) (by rw [m₁]; exact Outs.refl _ _ _)
    refine WP.mono (lenTimes_ok ((hw.of_keeps u₀.keeps).of_keeps K₁) ha₁ base headerFit 0)
      fun s₂ ⟨l₂, m₂, K₂⟩ => ?_
    refine ⟨((u₀.keeps.mono (by decide)).widen K₁).widen K₂,
      by rw [m₂, m₁, u₀.mem], ?_, ?_, ?_⟩
    · rw [K₂.1 _ (by decide), K₁.1 _ (by decide), u₀.gpr]
    · rw [PtrAt, K₂.1 _ (by decide)]; exact e₁
    · rw [l₂, m₁, u₀.mem, width_ok]
  refine WP.seq (WP.mono setup fun t₀ ⟨K₀, m₀, ebx₀, ecx₀, esi₀⟩ => ?_)
  -- The loop: `j` steps done.
  let I : Nat → State → Prop := fun j t =>
    Keeps clob6 s t ∧ PtrAt t W .ecx (bx + 4 * j) ∧ PtrAt t W .ebp (w + 4 * j) ∧
    (t.gpr .esi).toNat = 4 * (N - j) ∧ Outside W w (4 * j) s.mem t.mem ∧
    val32 t.mem W w j + 2 ^ (32 * j) * (t.gpr .ebx).toNat =
      val32 s.mem W w j + w32 s.mem W (S + Rt.multOff) * val32 s.mem W bx j
  have I₀ : I 0 t₀ := by
    refine ⟨K₀.mono (by decide), by simpa using ecx₀, ?_, by simpa using esi₀, by rw [m₀]; exact Outside.refl _ _ _ _, ?_⟩
    · rw [PtrAt, K₀.1 _ (by decide)]; simpa using hebp
    · rw [ebx₀]; simp [val32]
  have hNe : N % 2 = 0 := by omega
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := I N)
    (fun m t => ∃ j, m = N - j ∧ j < N ∧ j % 2 = 0 ∧ I j t) ?_ N t₀ ⟨0, by omega, hN, rfl, I₀⟩) ?_)
  · rintro m t ⟨j, rfl, hj, hje, K, ecx, ebp, esi, O, V⟩
    have hj2 : j + 2 ≤ N := by omega
    have ht := hw.of_keeps K
    have edi : PtrAt t W .edi S := by rw [PtrAt, K.1 _ (by decide)]; exact hedi
    unfold Rt.pairStep
    rw [List.append_assoc]
    -- The word `j`.
    refine WP.block_append (WP.mono (macAt_ok (mo := Rt.multOff) (d := 0) ht edi ecx ebp (by omega) (by omega) (by omega))
      fun u₁ ⟨mu₁, bu₁, Ku₁⟩ => ?_)
    have mk : w32 t.mem W (S + Rt.multOff) = w32 s.mem W (S + Rt.multOff) := O.w32 (by omega) (by omega)
    have bk : w32 t.mem W (bx + 4 * j + 0) = w32 s.mem W (bx + 4 * j) := O.w32 (by omega) (by omega)
    have tk : w32 t.mem W (w + 4 * j + 0) = w32 s.mem W (w + 4 * j) := O.w32 (by omega) (by omega)
    rw [mk, bk, tk] at mu₁ bu₁
    rw [Nat.add_zero] at mu₁
    have Wr₁ := writeW32_outside t.mem W (d := w + 4 * j)
      (BitVec.ofNat 32 (w32 s.mem W (S + Rt.multOff) * w32 s.mem W (bx + 4 * j) + (t.gpr .ebx).toNat +
        w32 s.mem W (w + 4 * j))) (by omega)
    rw [← mu₁] at Wr₁
    have O₁ : Outside W w (4 * (j + 1)) s.mem u₁.mem :=
      (O.mono (Nat.le_refl _) (by omega)).trans (Wr₁.mono (by omega) (by omega))
    have V₁ : val32 u₁.mem W w (j + 1) + 2 ^ (32 * (j + 1)) * (u₁.gpr .ebx).toNat =
        val32 s.mem W w (j + 1) + w32 s.mem W (S + Rt.multOff) * val32 s.mem W bx (j + 1) :=
      row_word V (Wr₁.val32 (by omega) (by omega)) (by rw [mu₁, w32_write_self, BitVec.toNat_ofNat]) bu₁
    -- The word `j + 1`.
    have hw₁ := hw.of_keeps (K.trans (Ku₁.mono (by decide)))
    have edi₁ : PtrAt u₁ W .edi S := by rw [PtrAt, Ku₁.1 _ (by decide)]; exact edi
    have ecx₁ : PtrAt u₁ W .ecx (bx + 4 * j) := by rw [PtrAt, Ku₁.1 _ (by decide)]; exact ecx
    have ebp₁ : PtrAt u₁ W .ebp (w + 4 * j) := by rw [PtrAt, Ku₁.1 _ (by decide)]; exact ebp
    refine WP.block_append (WP.mono (macAt_ok (mo := Rt.multOff) (d := 4) hw₁ edi₁ ecx₁ ebp₁ (by omega) (by omega) (by omega))
      fun u₂ ⟨mu₂, bu₂, Ku₂⟩ => ?_)
    have mk₁ : w32 u₁.mem W (S + Rt.multOff) = w32 s.mem W (S + Rt.multOff) := O₁.w32 (by omega) (by omega)
    have bk₁ : w32 u₁.mem W (bx + 4 * j + 4) = w32 s.mem W (bx + 4 * (j + 1)) := by
      rw [show bx + 4 * j + 4 = bx + 4 * (j + 1) by omega]; exact O₁.w32 (by omega) (by omega)
    have tk₁ : w32 u₁.mem W (w + 4 * j + 4) = w32 s.mem W (w + 4 * (j + 1)) := by
      rw [show w + 4 * j + 4 = w + 4 * (j + 1) by omega]; exact O₁.w32 (by omega) (by omega)
    rw [mk₁, bk₁, tk₁] at mu₂ bu₂
    rw [show w + 4 * j + 4 = w + 4 * (j + 1) by omega] at mu₂
    have Wr₂ := writeW32_outside u₁.mem W (d := w + 4 * (j + 1))
      (BitVec.ofNat 32 (w32 s.mem W (S + Rt.multOff) * w32 s.mem W (bx + 4 * (j + 1)) + (u₁.gpr .ebx).toNat +
        w32 s.mem W (w + 4 * (j + 1)))) (by omega)
    rw [← mu₂] at Wr₂
    have O₂ : Outside W w (4 * (j + 2)) s.mem u₂.mem :=
      (O₁.mono (Nat.le_refl _) (by omega)).trans (Wr₂.mono (by omega) (by omega))
    have V₂ : val32 u₂.mem W w (j + 1 + 1) + 2 ^ (32 * (j + 1 + 1)) * (u₂.gpr .ebx).toNat =
        val32 s.mem W w (j + 1 + 1) + w32 s.mem W (S + Rt.multOff) * val32 s.mem W bx (j + 1 + 1) :=
      row_word V₁ (Wr₂.val32 (by omega) (by omega)) (by rw [mu₂, w32_write_self, BitVec.toNat_ofNat]) bu₂
    -- The pointers and the count.
    have K₂ : Keeps [.eax, .ebx, .edx] t u₂ := Ku₁.trans Ku₂
    have ecx₂ : PtrAt u₂ W .ecx (bx + 4 * j) := by rw [PtrAt, K₂.1 _ (by decide)]; exact ecx
    have ebp₂ : PtrAt u₂ W .ebp (w + 4 * j) := by rw [PtrAt, K₂.1 _ (by decide)]; exact ebp
    have esi₂ : (u₂.gpr .esi).toNat = 4 * (N - j) := by rw [K₂.1 _ (by decide)]; exact esi
    refine WP.mono (pairCtl_ok ecx₂ ebp₂ esi₂ hj2) fun u ⟨mu, cu, pu, su, zu, Ku⟩ => ?_
    have I' : I (j + 2) u := by
      refine ⟨(K.trans (K₂.mono (by decide))).trans (Ku.mono (by decide)),
        by rw [show bx + 4 * (j + 2) = bx + 4 * j + 8 by omega]; exact cu,
        by rw [show w + 4 * (j + 2) = w + 4 * j + 8 by omega]; exact pu, su, by rw [mu]; exact O₂, ?_⟩
      rw [mu, Ku.1 _ (by decide)]
      exact V₂
    by_cases hjN : j + 2 = N
    · exact .inl ⟨by simp only [eval, zu, hjN, decide_true, Option.map_some, Bool.not_true], hjN ▸ I'⟩
    · exact .inr ⟨by simp only [eval, zu, decide_eq_false hjN, Option.map_some, Bool.not_false],
        N - (j + 2), by omega, j + 2, rfl, by omega, by omega, I'⟩
  · intro t ⟨K, _, ebp, _, O, V⟩
    have ht := hw.of_keeps K
    -- The carry into the window's top two words.
    have hhi : val32 t.mem W (w + 4 * N) 2 = val32 s.mem W (w + 4 * N) 2 := O.val32 (by omega) (by omega)
    have hsplit : val32 s.mem W w (N + 2) =
        val32 s.mem W w N + 2 ^ (32 * N) * val32 s.mem W (w + 4 * N) 2 := val32_append _ _ _ _ _
    rw [pow32_add, show 32 * 2 = 64 by rfl] at hlt
    have hP : 0 < 2 ^ (32 * N) := Nat.two_pow_pos _
    have hlt₁ : val32 t.mem W (w + 4 * N) 2 + (t.gpr .ebx).toNat < 2 ^ 64 := by
      rw [hhi]
      rw [hsplit] at hlt
      refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (32 * N)) ?_
      rw [Nat.mul_add]
      have := val32_lt t.mem W w N
      omega
    unfold Compact.carryUp
    rw [List.append_assoc]
    refine WP.block_append (WP.mono (carry_ok ht ebp (by omega) hlt₁) fun t₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have Kt₁ : Keeps clob6 s t₁ := K.trans (K₁.mono (by decide))
    have Ost₁ : Outside W w (4 * N + 8) s.mem t₁.mem :=
      (O.mono (Nat.le_refl _) (by omega)).trans (O₁.mono (by omega) (by omega))
    have ha₁ : Args t₁ W L A := ha.of_keeps Kt₁ (by decide)
      (Outs.of_outside (Ost₁.mono (by omega) (by omega)) (List.mem_singleton_self _))
    have width₁ : w32 t₁.mem W 48 = w32 s.mem W 48 := Ost₁.w32 (by omega) (by omega)
    refine WP.block_append (WP.mono (lenTimes_ok (hw.of_keeps Kt₁) ha₁ base headerFit 0) fun t₂ ⟨l₂, m₂, K₂⟩ => ?_)
    refine wp_subS rfl fun t₃ u₃ _ => WP.block_nil ?_
    have ebp₂ : PtrAt t₂ W .ebp (w + 4 * N) := by rw [PtrAt, K₂.1 _ (by decide), K₁.1 _ (by decide)]; exact ebp
    refine ⟨by rw [u₃.mem, m₂]; exact Ost₁, ?_, ?_, (Kt₁.trans (K₂.mono (by decide))).trans (u₃.keeps.mono (by decide))⟩
    · rw [u₃.mem, m₂, val32_append, V₁, O₁.val32 (d := w) (k := N) (by omega) (by omega), hhi, hsplit, Nat.mul_add]
      have hlow : val32 t.mem W w N + 2 ^ (32 * N) * (t.gpr .ebx).toNat =
          val32 s.mem W w N + w32 s.mem W (S + Rt.multOff) * val32 s.mem W bx N := V
      omega
    · rw [PtrAt, u₃.gpr, ptr_sub ebp₂ _ (by rw [l₂, width₁, width_ok]; omega), l₂, width₁, width_ok]
      congr 2; omega

end VG.Proof.Mont.X86.Compact
