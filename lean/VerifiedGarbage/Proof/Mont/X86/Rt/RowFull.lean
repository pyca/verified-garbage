module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Blocks
public import VerifiedGarbage.Proof.Mont.X86.Loop
import VerifiedGarbage.Proof.Framework.Omega

/-! # A row of the run-time width multiplication, as CIOS

Row `i` adds `a_i B` and then `q M` to the accumulator's window from word
`i`, with `q` making its low word zero, so the accumulator from word `i + 1`
is `(T + a_i B + q M) / 2³²` and stays below `2 M` (`rowRt_ok`), as
`Dynamic.row_ok` for the code at fixed offsets.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt VG.Proof.Mont VG.Proof.Mont.X86

/-- The offsets of the multiplication in the working space, `N = 2 n` words a
number: the function's range at `S` (`12 N + 56` bytes) apart from the
modulus, its inverse and the operands. -/
structure Lay (L N S mo inv a b : Nat) : Prop where
  scr : S + 12 * N + 56 ≤ L
  mo_le : mo + 4 * N ≤ L
  inv_le : inv + 4 ≤ L
  a_le : a + 4 * N ≤ L
  b_le : b + 4 * N ≤ L
  smo : mo + 4 * N ≤ S ∨ S + 12 * N + 56 ≤ mo
  sinv : inv + 4 ≤ S ∨ S + 12 * N + 56 ≤ inv
  sa : a + 4 * N ≤ S ∨ S + 12 * N + 56 ≤ a
  sb : b + 4 * N ≤ S ∨ S + 12 * N + 56 ≤ b

/-- The arguments: the working space, `8 n = 4 N`, and the offsets. -/
structure ArgVals (A : Nat → BitVec 32) (W : Addr) (N S mo inv o a b : Nat) : Prop where
  ws : (A 0).toNat = W.toNat
  n : (A 2).toNat * 8 = 4 * N
  mo : (A 3).toNat = mo
  inv : (A 4).toNat = inv
  s : (A 5).toNat = S
  o : (A 6).toNat = o
  a : (A 7).toNat = a
  b : (A 8).toNat = b

/-- A row's change to its window, within the accumulator. -/
theorem outs_window {W : Addr} {S N w : Nat} {m m' : Mem} (O : Outside W w (4 * N + 8) m m')
    (h₁ : S + accOff ≤ w) (h₂ : w + 4 * N + 8 ≤ S + accOff + 4 * (2 * N + 1)) :
    Outs W [(S + accOff, 4 * (2 * N + 1)), (S + multOff, 4)] m m' := fun x hx =>
  O x (by
    have := hx _ (List.mem_cons_self ..)
    simp only at this
    omega)

/-- A row. -/
theorem rowRt_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws s W L) (ha : Args s W L A)
    {N S mo inv o a b i m : Nat} (V : ArgVals A W N S mo inv o a b) (hL : Lay L N S mo inv a b)
    (hN32 : 4 * N < 2 ^ 32) (hi : i < N)
    (hedi : PtrAt s W .edi S) (hebp : PtrAt s W .ebp (S + accOff + 4 * i))
    (hm : val32 s.mem W mo N = m) (hinv : (m * w32 s.mem W inv + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem W b N < m)
    (hT : val32 s.mem W (S + accOff + 4 * i) (2 * N + 1 - i) < 2 * m) :
    WP isa Rt.row s fun u =>
      PtrAt u W .ebp (S + accOff + 4 * (i + 1)) ∧
      u.zf = some (decide (i + 1 = N)) ∧
      Outs W [(S + accOff, 4 * (2 * N + 1)), (S + multOff, 4)] s.mem u.mem ∧
      (∃ q, 2 ^ 32 * val32 u.mem W (S + accOff + 4 * (i + 1)) (2 * N + 1 - (i + 1)) =
        val32 s.mem W (S + accOff + 4 * i) (2 * N + 1 - i) + w32 s.mem W (a + 4 * i) * val32 s.mem W b N +
          q * m) ∧
      val32 u.mem W (S + accOff + 4 * (i + 1)) (2 * N + 1 - (i + 1)) < 2 * m ∧
      Keeps clob6 s u := by
  have hN : 0 < N := by omega_arith
  have hn := hw.nowrap
  have := hL.scr
  have := hL.mo_le
  have := hL.inv_le
  have := hL.a_le
  have := hL.b_le
  have := accOff_eq
  have := multOff_eq
  have hmP : m < 2 ^ (32 * N) := hm ▸ val32_lt _ _ _ _
  have hP : 0 < 2 ^ (32 * N) := Nat.two_pow_pos _
  have hpow : 2 ^ (32 * (N + 2)) = 2 ^ (32 * N) * 2 ^ 64 := by rw [pow32_add]
  -- The window: the accumulator's words from `i`, of which only the low
  -- `N + 2` may be nonzero.
  obtain ⟨w, ew⟩ : ∃ w, S + accOff + 4 * i = w := ⟨_, rfl⟩
  rw [ew] at hT hebp
  have hsplit : ∀ mem : Mem, val32 mem W w (2 * N + 1 - i) =
      val32 mem W w (N + 2) + 2 ^ (32 * (N + 2)) * val32 mem W (w + 4 * (N + 2)) (N - 1 - i) := by
    intro mem
    rw [show 2 * N + 1 - i = (N + 2) + (N - 1 - i) by omega_arith, val32_append]
  have habove : val32 s.mem W (w + 4 * (N + 2)) (N - 1 - i) = 0 := by
    rw [hsplit] at hT
    rcases Nat.eq_zero_or_pos (val32 s.mem W (w + 4 * (N + 2)) (N - 1 - i)) with h | h
    · exact h
    · have : 2 ^ (32 * (N + 2)) * 1 ≤ 2 ^ (32 * (N + 2)) * val32 s.mem W (w + 4 * (N + 2)) (N - 1 - i) :=
        Nat.mul_le_mul_left _ h
      have : 2 * 2 ^ (32 * N) ≤ 2 ^ (32 * (N + 2)) := by rw [hpow]; omega_arith
      omega_arith
  have hTw : val32 s.mem W w (N + 2) = val32 s.mem W w (2 * N + 1 - i) := by
    rw [hsplit s.mem, habove]; omega_arith
  unfold Rt.row
  -- `a_i` into the multiplier word.
  refine WP.seq (WP.mono (loadA_ok hw ha V.ws V.a (i := i) hedi (by rw [ew]; exact hebp) (by omega_arith) (by omega_arith))
    fun s₁ ⟨m₁, K₁⟩ => ?_)
  have k₁ : Keeps clob6 s s₁ := K₁.mono (by decide)
  have hw₁ := hw.of_keeps k₁
  have O₁ : Outside W (S + multOff) 4 s.mem s₁.mem := by rw [m₁]; exact writeW32_outside _ _ _ (by omega_arith)
  have ha₁ : Args s₁ W L A := ha.of_keeps k₁ (by decide)
    (Outs.of_outside (O₁.mono (by omega_arith) (by omega_arith)) (List.mem_singleton_self _))
  have edi₁ : PtrAt s₁ W .edi S := by rw [PtrAt, k₁.1 _ (by decide)]; exact hedi
  have ebp₁ : PtrAt s₁ W .ebp w := by rw [PtrAt, K₁.1 _ (by decide)]; exact hebp
  have mult₁ : w32 s₁.mem W (S + multOff) = w32 s.mem W (a + 4 * i) := by rw [m₁, w32_write_self]
  have win₁ : val32 s₁.mem W w (N + 2) = val32 s.mem W w (N + 2) := O₁.val32 (by omega_arith) (by omega_arith)
  have b₁ : val32 s₁.mem W b N = val32 s.mem W b N := O₁.val32 (by have := hL.sb; omega_arith) (by omega_arith)
  have mo₁ : val32 s₁.mem W mo N = m := by rw [O₁.val32 (by have := hL.smo; omega_arith) (by omega_arith), hm]
  have inv₁ : w32 s₁.mem W inv = w32 s.mem W inv := O₁.w32 (by have := hL.sinv; omega_arith) (by omega_arith)
  -- The window `+= a_i B`.
  have hlt₁ : val32 s₁.mem W w (N + 2) + w32 s₁.mem W (S + multOff) * val32 s₁.mem W b N <
      2 ^ (32 * (N + 2)) := by
    rw [win₁, b₁, hTw, hpow]
    have := (s₁.mem.readW (off W (S + multOff)) 32).isLt
    have : w32 s₁.mem W (S + multOff) * val32 s.mem W b N ≤ (2 ^ 32 - 1) * val32 s.mem W b N :=
      Nat.mul_le_mul_right _ (by simp only [w32]; omega_arith)
    have : 2 ^ (32 * N) * 2 ^ 32 ≤ 2 ^ (32 * N) * 2 ^ 64 := Nat.mul_le_mul_left _ (by decide)
    have : m * 2 ^ 32 < 2 ^ (32 * N) * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hmP (by decide)
    omega_arith
  refine WP.seq (WP.mono (mulRow_ok hw₁ ha₁ V.ws (xi := 8) (by decide) V.b V.n hN hN32 edi₁ ebp₁
    hL.b_le (by omega_arith) (by omega_arith) (by have := hL.sb; omega_arith) (by omega_arith) hlt₁) fun s₂ ⟨O₂, V₂, ebp₂, K₂⟩ => ?_)
  have k₂ : Keeps clob6 s s₂ := k₁.trans K₂
  have hw₂ := hw.of_keeps k₂
  have edi₂ : PtrAt s₂ W .edi S := by rw [PtrAt, k₂.1 _ (by decide)]; exact hedi
  have ha₂ : Args s₂ W L A := ha₁.of_keeps K₂ (by decide)
    (Outs.of_outside (O₂.mono (by omega_arith) (by omega_arith)) (List.mem_singleton_self _))
  rw [win₁, b₁, mult₁, hTw] at V₂
  -- `[mult] = q`, from the window's low word.
  refine WP.seq (WP.mono (redDigitRt_ok hw₂ ha₂ V.ws V.inv edi₂ ebp₂ (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₆ ⟨q₆, K₆, O₆⟩ => ?_)
  have k₆ : Keeps clob6 s s₆ := k₂.trans (K₆.mono (by decide))
  have hw₆ := hw.of_keeps k₆
  have edi₆ : PtrAt s₆ W .edi S := by rw [PtrAt, k₆.1 _ (by decide)]; exact hedi
  have ebp₆ : PtrAt s₆ W .ebp w := by rw [PtrAt, K₆.1 _ (by decide)]; exact ebp₂
  have ha₆ : Args s₆ W L A := ha₂.of_keeps K₆ (by decide)
    (Outs.of_outside (O₆.mono (by omega_arith) (by omega_arith)) (List.mem_singleton_self _))
  have t0 : w32 s₂.mem W w = val32 s₂.mem W w (N + 2) % 2 ^ 32 := by
    rw [val32]
    have := (s₂.mem.readW (off W w) 32).isLt
    simp only [w32]
    omega_arith
  have inv₂ : w32 s₂.mem W inv = w32 s.mem W inv := by
    rw [O₂.w32 (by have := hL.sinv; omega_arith) (by omega_arith), inv₁]
  rw [inv₂, t0] at q₆
  -- The window `+= q m`.
  have win₆ : val32 s₆.mem W w (N + 2) = val32 s₂.mem W w (N + 2) := O₆.val32 (by omega_arith) (by omega_arith)
  have hmo₆ : val32 s₆.mem W mo N = m := by
    rw [O₆.val32 (by have := hL.smo; omega_arith) (by omega_arith), O₂.val32 (by have := hL.smo; omega_arith) (by omega_arith), mo₁]
  have hq : w32 s₆.mem W (S + multOff) < 2 ^ 32 := (s₆.mem.readW (off W (S + multOff)) 32).isLt
  have hlt₆ : val32 s₆.mem W w (N + 2) + w32 s₆.mem W (S + multOff) * val32 s₆.mem W mo N <
      2 ^ (32 * (N + 2)) := by
    rw [win₆, V₂, hmo₆, hpow]
    have hW1 := row_lt (q := 0) (a := w32 s.mem W (a + 4 * i)) hT (s.mem.readW (off W (a + 4 * i)) 32).isLt
      hB (by decide)
    have : w32 s₆.mem W (S + multOff) * m ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul_right _ (by omega_arith)
    have : m * 2 ^ 32 < 2 ^ (32 * N) * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hmP (by decide)
    have : 2 ^ (32 * N) * 2 ^ 32 ≤ 2 ^ (32 * N) * 2 ^ 64 := Nat.mul_le_mul_left _ (by decide)
    omega_arith
  refine WP.seq (WP.mono (mulRow_ok hw₆ ha₆ V.ws (xi := 3) (by decide) V.mo V.n hN hN32 edi₆ ebp₆
    hL.mo_le (by omega_arith) (by omega_arith) (by have := hL.smo; omega_arith) (by omega_arith) hlt₆) fun s₇ ⟨O₇, V₇, ebp₇, K₇⟩ => ?_)
  have k₇ : Keeps clob6 s s₇ := k₆.trans K₇
  have hw₇ := hw.of_keeps k₇
  have edi₇ : PtrAt s₇ W .edi S := by rw [PtrAt, k₇.1 _ (by decide)]; exact hedi
  have ha₇ : Args s₇ W L A := ha₆.of_keeps K₇ (by decide)
    (Outs.of_outside (O₇.mono (by omega_arith) (by omega_arith)) (List.mem_singleton_self _))
  rw [win₆, V₂, hmo₆] at V₇
  -- `ebp` up a word, and the end of the rows.
  refine WP.mono (rowEnd_ok hw₇ ha₇ V.n hN32 edi₇ (by rw [ew]; exact ebp₇) hi (by omega_arith))
    fun u ⟨ebpu, zu, mu, Ku⟩ => ?_
  -- The new window, and what changed.
  have hO : Outs W [(S + accOff, 4 * (2 * N + 1)), (S + multOff, 4)] s.mem u.mem := by
    rw [mu]
    have e₁ : Outs W [(S + accOff, 4 * (2 * N + 1)), (S + multOff, 4)] s.mem s₁.mem :=
      Outs.of_outside O₁ (by simp)
    have e₂ := outs_window (S := S) (N := N) (m := s₁.mem) O₂ (by omega_using [ew]) (by omega_using [ew, hi])
    have e₆ : Outs W [(S + accOff, 4 * (2 * N + 1)), (S + multOff, 4)] s₂.mem s₆.mem :=
      Outs.of_outside O₆ (by simp)
    have e₇ := outs_window (S := S) (N := N) (m := s₆.mem) O₇ (by omega_using [ew]) (by omega_using [ew, hi])
    exact ((e₁.trans e₂).trans e₆).trans e₇
  have habove' : val32 u.mem W (w + 4 * (N + 2)) (N - 1 - i) = 0 := by
    rw [mu, O₇.val32 (by omega_arith) (by omega_arith), O₆.val32 (by omega_arith) (by omega_arith), O₂.val32 (by omega_arith) (by omega_arith),
      O₁.val32 (by omega_arith) (by omega_arith), habove]
  have hW2 : val32 u.mem W w (N + 2) = val32 s.mem W w (2 * N + 1 - i) +
      w32 s.mem W (a + 4 * i) * val32 s.mem W b N + w32 s₆.mem W (S + multOff) * m := by
    rw [mu, V₇]
  have hlow : val32 u.mem W w (N + 2) % 2 ^ 32 = 0 := by
    rw [hW2, ← V₂, q₆, ← Nat.mod_add_mod]; exact mont_low32 _ _ _ hinv
  have hT' : val32 u.mem W (S + accOff + 4 * (i + 1)) (2 * N + 1 - (i + 1)) =
      val32 u.mem W (w + 4) (N + 1) := by
    rw [show S + accOff + 4 * (i + 1) = w + 4 by omega_arith, show 2 * N + 1 - (i + 1) = (N + 1) + (N - 1 - i) by omega_arith,
      val32_append, show w + 4 + 4 * (N + 1) = w + 4 * (N + 2) by omega_arith, habove', Nat.mul_zero, Nat.add_zero]
  have hsh : val32 u.mem W w (N + 2) = w32 u.mem W w + 2 ^ 32 * val32 u.mem W (w + 4) (N + 1) := rfl
  have h32 : w32 u.mem W w < 2 ^ 32 := (u.mem.readW (off W w) 32).isLt
  have hW : 2 ^ 32 * val32 u.mem W (w + 4) (N + 1) = val32 u.mem W w (N + 2) := by omega_arith
  have hlt := row_lt (a := w32 s.mem W (a + 4 * i)) hT (s.mem.readW (off W (a + 4 * i)) 32).isLt hB hq
  refine ⟨ebpu, zu, hO, ⟨w32 s₆.mem W (S + multOff), ?_⟩, ?_, k₇.trans (Ku.mono (by decide))⟩
  · rw [hT', hW, hW2, ew]
  · rw [hT']
    rw [← hW2, ← hW] at hlt
    omega_arith

end VG.Proof.Mont.X86.Rt
