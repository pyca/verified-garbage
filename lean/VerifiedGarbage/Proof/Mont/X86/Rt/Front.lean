module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Save
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.Mont.X86.MulRt
import VerifiedGarbage.Proof.Mont.X86.OutsZ
import VerifiedGarbage.Proof.Mont.X86.Rt.Blocks
import VerifiedGarbage.Proof.Mont.X86.Rt.Row
import VerifiedGarbage.Proof.Mont.X86.Rt.Rows
import VerifiedGarbage.Proof.Mont.X86.Rt.Stages

/-! # The run-time width multiplication up to its rows

`save`, `zeroAcc` and `rows`: the accumulator's high half and top word `T`,
below `2 M`, with `2^(32 N) T ≡ A B` modulo `M`; the callee-saved registers
saved; only the function's range changed (`front_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt VG.Proof.Mont VG.Proof.Mont.X86

/-- A number apart from the function's range keeps its value across changes within it. -/
theorem outsS_val32 {W : Addr} {N S x k : Nat} {m m' : Mem} {rs : List (Nat × Nat)} (O : Outs W rs m m')
    (hr : ∀ r ∈ rs, S ≤ r.1 ∧ r.1 + r.2 ≤ S + 12 * N + 56)
    (h : x + 4 * k ≤ S ∨ S + 12 * N + 56 ≤ x) (hk : x + 4 * k ≤ 2 ^ 64) :
    val32 m' W x k = val32 m W x k :=
  O.val32 (fun r hr' => by have := hr r hr'; omega) hk

theorem front_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws s W L) (ha : Args s W L A)
    {N S mo inv o a b : Nat} (V : ArgVals A W N S mo inv o a b) (hL : Lay L N S mo inv a b)
    (hN : 0 < N) (hN32 : 4 * N < 2 ^ 32)
    (hinv : (val32 s.mem W mo N * w32 s.mem W inv + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem W b N < val32 s.mem W mo N) :
    WP isa (.seq (.block save) (.seq zeroAcc rows)) s fun u =>
      Outs W [(S, 12 * N + 56)] s.mem u.mem ∧ SavedAt u.mem W S s.gpr ∧
      PtrAt u W .ebp (S + accOff + 4 * N) ∧
      val32 u.mem W (S + accOff + 4 * N) (N + 1) < 2 * val32 s.mem W mo N ∧
      (∃ U, 2 ^ (32 * N) * val32 u.mem W (S + accOff + 4 * N) (N + 1) =
        val32 s.mem W a N * val32 s.mem W b N + U * val32 s.mem W mo N) ∧
      u.gpr .esp = s.gpr .esp ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  have hn := hw.nowrap
  have hscr := hL.scr
  have hmo := hL.mo_le
  have hinvL := hL.inv_le
  have hal := hL.a_le
  have hbl := hL.b_le
  have hsmo := hL.smo
  have hsinv := hL.sinv
  have hsa := hL.sa
  have hsb := hL.sb
  have eacc := accOff_eq
  have emul := multOff_eq
  refine WP.seq (WP.mono (save_ok hw ha V.ws V.s (by omega_using [hscr])) fun s₁ ⟨edi₁, sv₁, O₁, K₁⟩ => ?_)
  have hw₁ := hw.of_keeps K₁
  have F₁ : Outs W [(S, 12 * N + 56)] s.mem s₁.mem :=
    Outs.widen (Outs.of_outside O₁ (List.mem_singleton_self _))
      fun y hy r hr => by
        have := hy _ (List.mem_singleton_self _)
        simp only [List.mem_singleton] at hr; subst hr; simp only at this ⊢; omega
  have scr₁ : ∀ r ∈ [(S, 12 * N + 56)], S ≤ r.1 ∧ r.1 + r.2 ≤ S + 12 * N + 56 := by simp; omega
  have toL : ∀ {m m' : Mem}, Outs W [(S, 12 * N + 56)] m m' → Outs W [(0, L)] m m' := fun O =>
    Outs.widen O fun y hy r hr => by
      have := hy _ (List.mem_singleton_self _)
      simp only [List.mem_singleton] at hr; subst hr; simp only at this ⊢; omega
  have ha₁ : Args s₁ W L A := ha.of_keeps K₁ (by decide) (toL F₁)
  have mo₁ : val32 s₁.mem W mo N = val32 s.mem W mo N := outsS_val32 F₁ scr₁ hsmo (by omega_using [hmo, hn])
  have b₁ : val32 s₁.mem W b N = val32 s.mem W b N := outsS_val32 F₁ scr₁ hsb (by omega_using [hbl, hn])
  have a₁ : val32 s₁.mem W a N = val32 s.mem W a N := outsS_val32 F₁ scr₁ hsa (by omega_using [hal, hn])
  have inv₁ : w32 s₁.mem W inv = w32 s.mem W inv := by
    have := outsS_val32 (k := 1) F₁ scr₁ (by omega_using [hsinv]) (by omega_using [hinvL, hn])
    simpa [val32] using this
  refine WP.seq (WP.mono (zero_ok hw₁ ha₁ V hL hN32 edi₁) fun s₂ ⟨Z₂, O₂, K₂⟩ => ?_)
  have hw₂ := hw₁.of_keeps K₂
  have F₂ : Outs W [(S, 12 * N + 56)] s₁.mem s₂.mem :=
    Outs.widen (Outs.of_outside O₂ (List.mem_singleton_self _)) fun y hy r hr => by
      have := hy _ (List.mem_singleton_self _)
      simp only [List.mem_singleton] at hr; subst hr; simp only at this ⊢; omega
  have ha₂ : Args s₂ W L A := ha₁.of_keeps K₂ (by decide) (toL F₂)
  have edi₂ : PtrAt s₂ W .edi S := by rw [PtrAt, K₂.1 _ (by decide)]; exact edi₁
  have mo₂ : val32 s₂.mem W mo N = val32 s.mem W mo N := by
    rw [outsS_val32 F₂ scr₁ hsmo (by omega_using [hmo, hn]), mo₁]
  have b₂ : val32 s₂.mem W b N = val32 s.mem W b N := by
    rw [outsS_val32 F₂ scr₁ hsb (by omega_using [hbl, hn]), b₁]
  have a₂ : val32 s₂.mem W a N = val32 s.mem W a N := by
    rw [outsS_val32 F₂ scr₁ hsa (by omega_using [hal, hn]), a₁]
  have inv₂ : w32 s₂.mem W inv = w32 s.mem W inv := by
    have := outsS_val32 (k := 1) F₂ scr₁ (by omega_using [hsinv]) (by omega_using [hinvL, hn])
    simp only [val32, Nat.mul_zero, Nat.add_zero] at this
    rw [this, inv₁]
  refine WP.mono (rowsAll_ok hw₂ ha₂ V hL hN hN32 edi₂ mo₂ (by rw [inv₂]; exact hinv) (by rw [b₂]; exact hB) Z₂)
    fun u ⟨s₂', K₂', m₂', I⟩ => ?_
  have F₃ : Outs W [(S, 12 * N + 56)] s₂.mem u.mem := by
    rw [← m₂']
    exact Outs.widen I.out fun y hy r hr => by
      have := hy _ (List.mem_singleton_self _)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only at this ⊢ <;> omega
  have Ftot := (F₁.trans F₂).trans F₃
  have Ku : Keeps [.eax, .ebp, .ebx, .ecx, .edx, .esi, .edi] s u :=
    ((K₁.mono (by decide)).trans ((K₂.mono (by decide)).trans (K₂'.mono (by decide)))).trans (I.keeps.mono (by decide))
  refine ⟨Ftot, ?_, ?_, ?_, ?_, Ku.1 _ (by decide), Ku.2.1, Ku.2.2⟩
  · -- The saved words lie apart from what the zeroing and the rows change.
    have sv₂ := sv₁.of_outs (Outs.of_outside O₂ (List.mem_singleton_self _)) (by simp; omega_using [eacc])
      (by omega_using [hscr, hn])
    rw [← m₂'] at sv₂
    exact sv₂.of_outs I.out (by simp; omega_using [eacc, emul]) (by omega_using [hscr, hn])
  · have := I.ebp; simpa using this
  · have := I.lt
    rw [show 2 * N + 1 - N = N + 1 by omega_using []] at this
    exact this
  · obtain ⟨U, hU⟩ := I.cong
    refine ⟨U, ?_⟩
    rw [show 2 * N + 1 - N = N + 1 by omega_using [], m₂', a₂, b₂] at hU
    exact hU

end VG.Proof.Mont.X86.Rt
