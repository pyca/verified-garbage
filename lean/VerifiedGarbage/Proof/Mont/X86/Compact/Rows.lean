module

import VerifiedGarbage.Proof.Mont.X86.Compact.RowFull
import VerifiedGarbage.Proof.Mont.X86.OutsZ
public import VerifiedGarbage.Proof.Mont.X86.Compact.Bounds
public import VerifiedGarbage.Proof.Mont.X86.Compact.Metadata
public import VerifiedGarbage.Proof.Mont.X86.Rt.Row
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # All paired-word CIOS rows in the compact prepared workspace -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

/-- The rows' invariant after `i` rows, from the state `s` before them. -/
structure LoopInvR (W : Addr) (N S a b m i : Nat) (s t : State) : Prop where
  ebp : PtrAt t W .ebp (S + Compact.accOff + 4 * i)
  out : Outs W [(S + Compact.accOff, 4 * (2 * N + 1)), (S + Rt.multOff, 4)] s.mem t.mem
  keeps : Keeps clob6 s t
  lt : val32 t.mem W (S + Compact.accOff + 4 * i) (2 * N + 1 - i) < 2 * m
  cong : ∃ U, 2 ^ (32 * i) * val32 t.mem W (S + Compact.accOff + 4 * i) (2 * N + 1 - i) =
    val32 s.mem W a i * val32 s.mem W b N + U * m

/-- A number apart from both ranges a row changes. -/
theorem outs_val32 {W : Addr} {N S x k : Nat} {m m' : Mem}
    (O : Outs W [(S + Compact.accOff, 4 * (2 * N + 1)), (S + Rt.multOff, 4)] m m')
    (h : x + 4 * k ≤ S ∨ S + 8 * N + 28 ≤ x) (hk : x + 4 * k ≤ 2 ^ 64) :
    val32 m' W x k = val32 m W x k :=
  O.val32 (by
    intro r hr
    have acc : Compact.accOff = 24 := rfl; have mult : Rt.multOff = 20 := rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> omega) hk

/-- The rows: from the invariant at 0 to the invariant at `N`. -/
theorem loopR_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws s W L) (ha : Args s W L A)
    {N S mo a b m : Nat} (base : (A 0).toNat = W.toNat)
    (V : Metadata s.mem W A N S mo a b) (hL : Lay L N S mo a b)
    (hN : 0 < N) (hN32 : 4 * N < 2 ^ 32) (hedi : PtrAt s W .edi S)
    (hm : val32 s.mem W mo N = m) (hinv : (m * w32 s.mem W 56 + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem W b N < m) {t : State} (h0 : LoopInvR W N S a b m 0 s t) :
    WP isa (.loop Compact.row .ne) t fun u => LoopInvR W N S a b m N s u := by
  have hn := hw.nowrap
  have := hL.scr
  have := hL.mo_le
  have header := hL.header
  have := hL.a_le
  have := hL.b_le
  have acc : Compact.accOff = 24 := rfl
  have mult : Rt.multOff = 20 := rfl
  refine WP.loop (M := isa)
    (fun n t' => ∃ i, n = N - i ∧ i < N ∧ LoopInvR W N S a b m i s t') ?_ N t ⟨0, rfl, hN, h0⟩
  rintro n t' ⟨i, rfl, hi, I⟩
  have hw' := hw.of_keeps I.keeps
  have hedi' : PtrAt t' W .edi S := by rw [PtrAt, I.keeps.1 _ (by decide)]; exact hedi
  have ha' : Args t' W L A := ha.of_keeps I.keeps (by decide) (Outs.widen I.out fun y hy r hr => by
    have := hy _ (List.mem_singleton_self _)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only at this ⊢ <;> omega)
  have hm' : val32 t'.mem W mo N = m := by
    rw [outs_val32 I.out hL.smo (by omega), hm]
  have hb' : val32 t'.mem W b N = val32 s.mem W b N := outs_val32 I.out hL.sb (by omega)
  have ha₁ : w32 t'.mem W (a + 4 * i) = w32 s.mem W (a + 4 * i) := by
    have := outs_val32 (k := 1) (x := a + 4 * i) I.out (by have := hL.sa; omega) (by omega)
    simpa [val32] using this
  have hinv' : (m * w32 t'.mem W 56 + 1) % 2 ^ 32 = 0 := by
    have := outs_val32 (k := 1) (x := 56) I.out (by omega) (by omega)
    simp only [val32, Nat.mul_zero, Nat.add_zero] at this
    rw [this]; exact hinv
  have metadata : Metadata t'.mem W A N S mo a b := by
    have O : Outside W S (8 * N + 28) s.mem t'.mem := fun x hx => I.out x fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega
    exact V.keep O (by omega)
  refine WP.mono (row_ok hw' ha' base metadata hL hN32 hi hedi' I.ebp hm' hinv' (hb' ▸ hB) I.lt)
    fun u ⟨hp, hz, O, ⟨q, hq⟩, hT, K⟩ => ?_
  rw [hb', ha₁] at hq
  have I' : LoopInvR W N S a b m (i + 1) s u := by
    refine ⟨hp, I.out.trans O, I.keeps.trans K, hT, ?_⟩
    obtain ⟨U, hU⟩ := I.cong
    refine ⟨U + 2 ^ (32 * i) * q, ?_⟩
    rw [pow32_succ, val32_succ, Nat.mul_assoc, Nat.mul_left_comm, hq]
    generalize 2 ^ (32 * i) = P at *
    grind
  by_cases hNi : i + 1 = N
  · refine .inl ⟨by simp only [eval, hz, hNi, decide_true, Option.map_some, Bool.not_true], hNi ▸ I'⟩
  · exact .inr ⟨by simp only [eval, hz, decide_eq_false hNi, Option.map_some, Bool.not_false],
      N - (i + 1), by omega, i + 1, rfl, by omega, I'⟩

end VG.Proof.Mont.X86.Compact
