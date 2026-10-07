import VerifiedGarbage.Proof.Mont.X86_64.MulPX

/-!
# Montgomery arithmetic on x86-64: P-521's squares with BMI2 and ADX

`sqrPX o a` (`Impl/Mont/X86_64.lean`) writes `[a]² R⁻¹ mod p` to `[o]` for
`p = 2⁵²¹ - 1` (`sqrPX_ok`, `mulPX_ok`'s statement with `b = a`):

* the rows of the products of two different words (`sRows_ok`): row 0
  puts `a_0 [a_1 …]` in the rotating registers of `mulPX` by one carry
  chain (`sRow0_ok`), and each later row `i` adds `a_i [a_(i+1) …]` to them
  (`sRow_ok`, `sRow_inv`), their sum `sCross` below `[a]_(i+1) [a]`
  (`sCross_le`);
* the squares (`sDiagK_ok`, `sDiags_ok`): each of the 18 words doubled
  through CF and `a_k²` added through OF, words 0 … 8 in the temporary area
  and 9 … 17 in the registers (`sqWord`);
* `2 sCross + sDg = [a]²` (`sq_ident`), so the accumulator holds `[a]²`,
  and `mulPX`'s reduction and final reduction follow (`xRed_ok`, `xCanon_ok`).
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono madd_ok movRdx_ok mulx_ok of_setReg of_setFlags)

theorem sWin_fresh {i : Nat} (hi : i < 8) : FreshX (sWin i) := by
  have h : ∀ i < 8, FreshX (sWin i) := by unfold FreshX; decide
  exact h i hi

theorem sWin_length (i : Nat) : (sWin i).length = 9 - i := by simp [sWin]

theorem regsVal_sWin (s : State) (i : Nat) : regsVal s (sWin i) = hval (xg s) (2 * i + 1) (9 - i) :=
  regsVal_xAccs s (9 - i) (2 * i + 1)

theorem mem_sWin {i : Nat} {r : Reg} (h : r ∈ sWin i) : ∃ j, j < 9 - i ∧ r = xAcc (2 * i + 1 + j) := by
  simp only [sWin, List.mem_map, List.mem_range] at h
  obtain ⟨j, hj, rfl⟩ := h
  exact ⟨j, hj, rfl⟩

/-- The carries of a row of `sqrPX` are zero when its sum fits. -/
theorem sRow_arith {G R x₆ x₅ H P : Nat} {o₅ o₆ c₅ : Bool} (hHP : H + P < R * 2 ^ 64)
    (e₅ : G + R * x₅ + R * o₅.toNat + R * 2 ^ 64 * c₅.toNat = H + P)
    (e₆ : x₆ + 2 ^ 64 * o₆.toNat = x₅ + o₅.toNat) : G + R * x₆ = H + P := by
  cases c₅
  · rw [Bool.toNat_false, Nat.mul_zero, Nat.add_zero, Nat.add_assoc, ← Nat.mul_add] at e₅
    cases o₆
    · rw [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at e₆
      rw [e₆]; exact e₅
    · rw [Bool.toNat_true, Nat.mul_one] at e₆
      have h1 : R * 2 ^ 64 ≤ R * (x₅ + o₅.toNat) := Nat.mul_le_mul_left R (e₆ ▸ Nat.le_add_left _ _)
      exact absurd hHP (Nat.not_lt.mpr (e₅ ▸ Nat.le_trans h1 (Nat.le_add_left _ _)))
  · rw [Bool.toNat_true, Nat.mul_one] at e₅
    exact absurd hHP (Nat.not_lt.mpr (e₅ ▸ Nat.le_add_left _ _))

/-- Row `i < 8`: word `i` stored, `t += 2^(64 (i + 1)) a_i [a + 8 (i + 1)]_(8 - i)`
relative to word `i`. -/
theorem sRow_ok {s : State} {base : Addr} {size c₀ : Nat} (hs : ScrC s base size c₀) {M : Mod} {a : Nat}
    (i : Nat) (hi : i < 8) (ha : a + 72 ≤ size) (ht : M.tmp + 8 * i + 8 ≤ size)
    (hat : a + 72 ≤ M.tmp + 8 * i ∨ M.tmp + 8 * i + 8 ≤ a)
    (hB : hval (xg s) i 9 + (2 ^ 64) ^ (i + 1) * ((word s.mem base (a + 8 * i)).toNat *
      wordsVal s.mem base (a + 8 * (i + 1)) (8 - i)) < (2 ^ 64) ^ 10) :
    WP isa (.block (sRow M c₀ a i)) s fun s' =>
      (word s'.mem base (M.tmp + 8 * i)).toNat + 2 ^ 64 * hval (xg s') (i + 1) 9 =
        hval (xg s) i 9 + (2 ^ 64) ^ (i + 1) * ((word s.mem base (a + 8 * i)).toNat *
          wordsVal s.mem base (a + 8 * (i + 1)) (8 - i)) ∧
      KeepRegs (.rax :: .rcx :: .rdx :: xRegs) s s' ∧ Outside base (M.tmp + 8 * i) 8 s.mem s'.mem := by
  have hnw := hs.nowrap
  obtain ⟨hia, hic, hid, hii, -⟩ := xAcc_ne i
  rw [sRow, List.append_assoc, WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (storeXC_ok hs (xAcc i) ht) fun s₁ ⟨m₁, g₁, cf₁, of₁, rd₁, wr₁⟩ => ?_
  have hs₁ : ScrC s₁ base size c₀ := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movZero_ok s₁ (xAcc i)) fun s₂ ⟨z₂, cf₂, of₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by simpa using Ne.symm hii)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movRdx_ok s₂ (readSrc_rc hs₂ (d := a + 8 * i) (by omega))) fun s₃ ⟨d₃, _, _, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (xorRax_ok s₃) fun s₄ ⟨c₄, o₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (maddStepsC_ok (8 - i) (sWin i) hs₄ (d := a + 8 * (i + 1)) (by omega)
    (by rw [sWin_length]; omega) (sWin_fresh hi) c₄ o₄) fun s₅ ⟨c₅, o₅, cf₅, of₅, e₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (by
    simp only [List.mem_cons, not_or]
    refine ⟨by decide, by decide, fun h => ?_⟩
    obtain ⟨j, -, hj⟩ := mem_sWin (List.mem_of_mem_take h)
    exact (xAcc_ne _).2.2.2.1 hj.symm)
  obtain ⟨hka, -, -, -, -⟩ := xAcc_ne (i + 9)
  refine WP.mono (xTail_ok s₅ of₅ hka) fun s₆ ⟨o₆, _, cf₆, e₆, k₆⟩ => ?_
  -- The memory.
  have hm₄ : s₄.mem = s₁.mem := k₄.2.1.trans (k₃.2.1.trans k₂.2.1)
  have hm₆ : s₆.mem = s₄.mem := k₆.2.1.trans k₅.2.1
  have O₁ : Outside base (M.tmp + 8 * i) 8 s.mem s₁.mem := by
    rw [m₁]; exact writeW_outside _ _ _ (by omega)
  have hw : (word s₆.mem base (M.tmp + 8 * i)).toNat = xg s i := by
    rw [hm₆, hm₄, m₁, word_writeW_self]; rfl
  have hA₄ : wordsVal s₄.mem base (a + 8 * (i + 1)) (8 - i) = wordsVal s.mem base (a + 8 * (i + 1)) (8 - i) := by
    rw [hm₄]; exact O₁.wordsVal (by omega) (by omega)
  have hdx₄ : s₄.gpr .rdx = word s.mem base (a + 8 * i) := by
    rw [k₄.1 .rdx (by decide), d₃, k₂.2.1]
    exact O₁.word (by omega) (by omega)
  -- The registers through the steps.
  have hx₄ : ∀ c, i < c → c < i + 9 → xg s₄ c = xg s c := fun c h1 h2 => by
    simp only [xg]
    rw [k₄.1 _ (by simpa using (xAcc_ne c).1), k₃.1 _ (by simpa using (xAcc_ne c).2.2.1),
      k₂.1 _ (by simpa using (xAcc_ne_of h1 h2).symm), g₁]
  have h₄₉ : xg s₄ (i + 9) = 0 := by
    simp only [xg, xAcc_add9]
    rw [k₄.1 _ (by simpa using hia), k₃.1 _ (by simpa using hid), z₂]; rfl
  have notW : ∀ c, i < c → c ≤ 2 * i → xAcc c ∉ sWin i := fun c h1 h2 h => by
    obtain ⟨j, hj, e⟩ := mem_sWin h
    exact xAcc_ne_of (show c < 2 * i + 1 + j by omega) (by omega) e
  have h₆ : ∀ c, i < c → c ≤ 2 * i → xg s₆ c = xg s c := fun c h1 h2 => by
    simp only [xg]
    rw [k₆.1 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(xAcc_ne c).1, xAcc_ne_of (by omega) (by omega)⟩), k₅.1 _ (by
      simp only [List.mem_cons, not_or]
      exact ⟨(xAcc_ne c).2.1, (xAcc_ne c).1, fun h => notW c h1 h2 (List.mem_of_mem_take h)⟩)]
    exact hx₄ c h1 (by omega)
  have h₆' : ∀ c, 2 * i + 1 ≤ c → c < i + 9 → xg s₆ c = xg s₅ c := fun c h1 h2 => by
    simp only [xg]
    rw [k₆.1 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(xAcc_ne c).1, xAcc_ne_of (by omega) (by omega)⟩)]
  -- The values.
  rw [List.take_of_length_le (by rw [sWin_length]; omega), regsVal_sWin, regsVal_sWin, hdx₄, hA₄,
    show 9 - i = (8 - i) + 1 by omega, hval_succ_last, hval_succ_last,
    show 2 * i + 1 + (8 - i) = i + 9 by omega, h₄₉] at e₅
  change xg s₆ (i + 9) + 2 ^ 64 * o₆.toNat = xg s₅ (i + 9) + o₅.toNat at e₆
  have hL : hval (xg s₆) (i + 1) i = hval (xg s) (i + 1) i :=
    hval_congr fun c h1 h2 => h₆ c (by omega) (by omega)
  have hH₄ : hval (xg s₄) (2 * i + 1) (8 - i) = hval (xg s) (2 * i + 1) (8 - i) :=
    hval_congr fun c h1 h2 => hx₄ c (by omega) (by omega)
  have hH₆ : hval (xg s₆) (2 * i + 1) (8 - i) = hval (xg s₅) (2 * i + 1) (8 - i) :=
    hval_congr fun c h1 h2 => h₆' c (by omega) (by omega)
  have hS' : hval (xg s₆) (i + 1) 9 = hval (xg s₆) (i + 1) i + (2 ^ 64) ^ i *
      (hval (xg s₆) (2 * i + 1) (8 - i) + (2 ^ 64) ^ (8 - i) * xg s₆ (i + 9)) := by
    have h := hval_add (xg s₆) (i + 1) i ((8 - i) + 1)
    rw [show i + ((8 - i) + 1) = 9 by omega, show i + 1 + i = 2 * i + 1 by omega,
      hval_succ_last (xg s₆) (2 * i + 1) (8 - i), show 2 * i + 1 + (8 - i) = i + 9 by omega] at h
    exact h
  have hS : hval (xg s) i 9 = xg s i + 2 ^ 64 * (hval (xg s) (i + 1) i + (2 ^ 64) ^ i *
      hval (xg s) (2 * i + 1) (8 - i)) := by
    have h := hval_add (xg s) (i + 1) i (8 - i)
    rw [show i + (8 - i) = 8 by omega, show i + 1 + i = 2 * i + 1 by omega] at h
    rw [show (9 : Nat) = 8 + 1 from rfl, hval, h]
  rw [hH₄] at e₅
  rw [hH₆] at hS'
  refine ⟨?_, ?_, ?_⟩
  · rw [hw, hS', hL]
    rw [hS] at hB ⊢
    have hX : (2 ^ 64) ^ (i + 1) = 2 ^ 64 * (2 ^ 64) ^ i := by rw [pow64_succ']
    have h10 : (2 ^ 64 : Nat) ^ 10 = 2 ^ 64 * ((2 ^ 64) ^ i * (2 ^ 64) ^ (9 - i)) := by
      rw [← Nat.pow_add, show i + (9 - i) = 9 by omega, pow64_succ']
    have h9 : (2 ^ 64 : Nat) ^ (9 - i) = (2 ^ 64) ^ (8 - i) * 2 ^ 64 := by
      rw [show 9 - i = (8 - i) + 1 by omega, Nat.pow_succ]
    rw [hX] at hB ⊢
    rw [h10, h9] at hB
    rw [Nat.pow_mul, Nat.pow_mul, show (2 ^ 64 : Nat) ^ (8 - i + 1) = (2 ^ 64) ^ (8 - i) * 2 ^ 64 from
      Nat.pow_succ ..] at e₅
    simp only [Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at e₅
    generalize (2 ^ 64 : Nat) ^ i = Q at *
    generalize (2 ^ 64 : Nat) ^ (8 - i) = R at *
    generalize (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base (a + 8 * (i + 1)) (8 - i) = P at *
    generalize hval (xg s) (i + 1) i = L at *
    generalize hval (xg s) (2 * i + 1) (8 - i) = H at *
    generalize hval (xg s₅) (2 * i + 1) (8 - i) = G at *
    generalize xg s₆ (i + 9) = x₆ at *
    generalize xg s₅ (i + 9) = x₅ at *
    generalize xg s i = x₀ at *
    have hHP : H + P < R * 2 ^ 64 := by
      have h1 : 2 ^ 64 * (Q * (H + P)) < 2 ^ 64 * (Q * (R * 2 ^ 64)) := by
        rw [Nat.mul_add Q, Nat.mul_add (2 ^ 64)]
        rw [Nat.mul_assoc] at hB
        omega
      exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_mul_lt_mul_left h1)
    have hGH : G + R * x₆ = H + P := sRow_arith hHP e₅ e₆
    rw [hGH, Nat.mul_add Q, Nat.mul_add (2 ^ 64), Nat.mul_add (2 ^ 64), Nat.mul_assoc (2 ^ 64) Q P]
    omega
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, not_or] at hr
      obtain ⟨ra, rc, rd, rx⟩ := hr
      have rx' : ∀ k, xAcc k ≠ r := fun k h => rx (h ▸ (xAcc_ne k).2.2.2.2)
      rw [k₆.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨ra, (rx' _).symm⟩),
        k₅.1 r (by
          simp only [List.mem_cons, not_or]
          refine ⟨rc, ra, fun h => ?_⟩
          obtain ⟨j, -, hj⟩ := mem_sWin (List.mem_of_mem_take h)
          exact rx' _ hj.symm),
        k₄.1 r (by simpa using ra), k₃.1 r (by simpa using rd), k₂.1 r (by simpa using (rx' i).symm), g₁]
    · rw [k₆.2.2.1, k₅.2.2.1, k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, rd₁]
    · rw [k₆.2.2.2, k₅.2.2.2, k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, wr₁]
  · rw [hm₆, hm₄]; exact O₁


/-- The products of two different words of `f`'s nine, by rows, low-first:
row `r` is `2^(64 (2r + 1)) f_r [f_(r+1) …]_(8-r)`. -/
def sCross (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | r + 1 => sCross f r + (2 ^ 64) ^ (2 * r + 1) * (f r * hval f (r + 1) (8 - r))

theorem sCross_le (f : Nat → Nat) : ∀ n, n ≤ 9 → sCross f n ≤ hval f 0 n * hval f 0 9
  | 0, _ => by simp [sCross, hval]
  | n + 1, hn => by
    have ih := sCross_le f n (by omega)
    have hW : hval f 0 9 = hval f 0 (n + 1) + (2 ^ 64) ^ (n + 1) * hval f (n + 1) (8 - n) := by
      have := hval_add f 0 (n + 1) (8 - n)
      rwa [show n + 1 + (8 - n) = 9 by omega, Nat.zero_add] at this
    have hS : hval f 0 (n + 1) = hval f 0 n + (2 ^ 64) ^ n * f n := by rw [hval_succ_last, Nat.zero_add]
    have hT : (2 ^ 64) ^ (n + 1) * hval f (n + 1) (8 - n) ≤ hval f 0 9 := by omega
    have e : (2 ^ 64) ^ (2 * n + 1) * (f n * hval f (n + 1) (8 - n)) =
        (2 ^ 64) ^ n * f n * ((2 ^ 64) ^ (n + 1) * hval f (n + 1) (8 - n)) := by
      rw [show 2 * n + 1 = n + (n + 1) by omega, Nat.pow_add, Nat.mul_assoc, Nat.mul_assoc,
        Nat.mul_left_comm (f n)]
    rw [sCross, hS, Nat.add_mul, e]
    exact Nat.add_le_add ih (Nat.mul_le_mul_left _ hT)

/-- Row `n < 8` after the first `n`: from the low `n` words of the products
of two different words in the temporary area and the others in `xWin n`, the
same for `n + 1`. -/
theorem sRow_inv {s₀ s : State} {base : Addr} {size c₀ : Nat} (hs : ScrC s₀ base size c₀) {M : Mod} {a : Nat}
    (ha : a + 72 ≤ size) (ht : M.tmp + 72 ≤ size) (hat : a + 72 ≤ M.tmp ∨ M.tmp + 72 ≤ a) {n : Nat}
    (hn : n < 8) (k : KeepRegs (.rax :: .rcx :: .rdx :: xRegs) s₀ s)
    (O : Outside base M.tmp 72 s₀.mem s.mem)
    (e : wordsVal s.mem base M.tmp n + (2 ^ 64) ^ n * hval (xg s) n 9 =
      sCross (fun j => (word s₀.mem base (a + 8 * j)).toNat) n) :
    WP isa (.block (sRow M c₀ a n)) s fun s' =>
      KeepRegs (.rax :: .rcx :: .rdx :: xRegs) s₀ s' ∧ Outside base M.tmp 72 s₀.mem s'.mem ∧
      wordsVal s'.mem base M.tmp (n + 1) + (2 ^ 64) ^ (n + 1) * hval (xg s') (n + 1) 9 =
        sCross (fun j => (word s₀.mem base (a + 8 * j)).toNat) (n + 1) := by
    have hnw := hs.nowrap
    have hsS : ScrC s base size c₀ := hs.of_keepRegs k (by decide)
    generalize hf : (fun j => (word s₀.mem base (a + 8 * j)).toNat) = f at e
    have hA : (word s.mem base (a + 8 * n)).toNat = f n := by
      rw [← hf, O.word (by omega) (by omega)]
    have hBv : wordsVal s.mem base (a + 8 * (n + 1)) (8 - n) = hval f (n + 1) (8 - n) := by
      rw [O.wordsVal (by omega) (by omega), ← hf, wordsVal_hval]
    have hW : hval f 0 9 < (2 ^ 64) ^ 9 := by
      rw [← hf, ← wordsVal_hval s₀.mem base a 0 9, Nat.mul_zero, Nat.add_zero, ← Nat.pow_mul]
      exact wordsVal_lt _ _ _ 9
    have hF : hval f 0 (n + 1) < (2 ^ 64) ^ (n + 1) := by
      rw [← hf, ← wordsVal_hval s₀.mem base a 0 (n + 1), Nat.mul_zero, Nat.add_zero, ← Nat.pow_mul]
      exact wordsVal_lt _ _ _ _
    have hC := sCross_le f (n + 1) (by omega)
    have hX : (2 ^ 64) ^ (2 * n + 1) = (2 ^ 64) ^ n * (2 ^ 64) ^ (n + 1) := by
      rw [← Nat.pow_add, show n + (n + 1) = 2 * n + 1 by omega]
    have hrow : hval (xg s) n 9 + (2 ^ 64) ^ (n + 1) * ((word s.mem base (a + 8 * n)).toNat *
        wordsVal s.mem base (a + 8 * (n + 1)) (8 - n)) < (2 ^ 64) ^ 10 := by
      rw [hA, hBv]
      have h1 : (2 ^ 64) ^ n * (hval (xg s) n 9 + (2 ^ 64) ^ (n + 1) * (f n * hval f (n + 1) (8 - n))) ≤
          sCross f (n + 1) := by
        rw [sCross, Nat.mul_add, ← Nat.mul_assoc, ← hX, ← e]
        omega
      have h2 : hval f 0 (n + 1) * hval f 0 9 < (2 ^ 64) ^ n * (2 ^ 64) ^ 10 := by
        rw [← Nat.pow_add, show n + 10 = (n + 1) + 9 by omega, Nat.pow_add]
        exact Nat.mul_lt_mul'' hF hW
      exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt h1 (Nat.lt_of_le_of_lt hC h2))
    refine WP.mono (sRow_ok hsS n (by omega) (by omega) (by omega) (by omega) hrow)
      fun s' ⟨e', k', O'⟩ => ⟨k.trans k', O.trans (O'.mono (by omega) (by omega)), ?_⟩
    rw [hA, hBv] at e'
    rw [wordsVal_succ_last s'.mem, O'.wordsVal (by omega) (by omega), sCross, ← e, hX]
    have hQ1 : (2 ^ 64 : Nat) ^ (n + 1) = (2 ^ 64) ^ n * 2 ^ 64 := Nat.pow_succ ..
    rw [hQ1] at e' ⊢
    generalize (2 ^ 64 : Nat) ^ n = Q at *
    generalize f n * hval f (n + 1) (8 - n) = FB at *
    generalize (word s'.mem base (M.tmp + 8 * n)).toNat = w at *
    generalize hval (xg s') (n + 1) 9 = V' at *
    generalize hval (xg s) n 9 = V at *
    generalize (2 : Nat) ^ 64 = X at *
    rw [Nat.mul_assoc Q X V', Nat.add_assoc, ← Nat.mul_add, e', Nat.mul_add,
      ← Nat.add_assoc, Nat.mul_assoc, Nat.mul_assoc Q (Q * X) FB, Nat.mul_assoc Q X FB]


/-- `xor eax, eax`: `rax` and both carries clear. -/
theorem xorRaxZ_ok (s : State) :
    WP isa (.block [.alu32 .xor .rax (.reg .rax)]) s fun s' =>
      s'.gpr .rax = 0 ∧ s'.cf = some false ∧ Keeps [.rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32,
    Option.bind_some, State.setReg32, BitVec.xor_self, RegUpd.gpr_setReg_self,
    RegUpd.cf_setReg, arithFlags, State.setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, (by trivial), fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- Row 0 of the products of two different words: word 0, zero, stored at
`[tmp]`, and `a_0 [a_1 …]` in the words `1 … 9`, whatever they held before. -/
theorem sRow0_ok {s : State} {base : Addr} {size c₀ : Nat} (hs : ScrC s base size c₀) {M : Mod} {a : Nat}
    (ha : a + 72 ≤ size) (ht : M.tmp + 8 ≤ size) (hat : a + 72 ≤ M.tmp ∨ M.tmp + 8 ≤ a) :
    WP isa (.block (sRow0 M c₀ a)) s fun s' =>
      (word s'.mem base M.tmp).toNat = 0 ∧
      hval (xg s') 1 9 = (word s.mem base a).toNat * wordsVal s.mem base (a + 8) 8 ∧
      KeepRegs (.rax :: .rcx :: .rdx :: xRegs) s s' ∧ Outside base M.tmp 8 s.mem s'.mem := by
  have hnw := hs.nowrap
  obtain ⟨h1a, -, h1d, h1i, -⟩ := xAcc_ne 1
  obtain ⟨h2a, -, h2d, h2i, -⟩ := xAcc_ne 2
  have h12 : xAcc 2 ≠ xAcc 1 := (xAcc_ne_of (show 1 < 2 by omega) (by omega)).symm
  rw [sRow0, List.append_assoc, WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (xorRaxZ_ok s) fun s₁ ⟨z₁, c₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (storeXC_ok hs₁ .rax ht) fun s₂ ⟨m₂, g₂, cf₂, _, rd₂, wr₂⟩ => ?_
  have hs₂ : ScrC s₂ base size c₀ := ⟨by rw [g₂]; exact hs₁.rdi, by rw [wr₂]; exact hs₁.wr, hs₁.nowrap⟩
  have O₂ : Outside base M.tmp 8 s.mem s₂.mem := by
    rw [m₂, k₁.2.1]; exact writeW_outside _ _ _ (by omega)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movRdx_ok s₂ (readSrc_rc hs₂ (d := a) (by omega))) fun s₃ ⟨d₃, cf₃, _, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (mulx_ok s₃ (readSrc_rc hs₃ (d := a + 8) (by omega)) (fun _ h => nomatch h) h12)
    fun s₄ ⟨e₄, cf₄, _, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm h2i, Ne.symm h1i⟩)
  -- The words of `a`, apart from `[tmp]`.
  have hm₄ : s₄.mem = s₂.mem := k₄.2.1.trans k₃.2.1
  have hA : word s₂.mem base a = word s.mem base a := O₂.word (by omega) (by omega)
  have hA1 : word s₃.mem base (a + 8) = word s.mem base (a + 8) := by
    rw [k₃.2.1]; exact O₂.word (by omega) (by omega)
  have hW : wordsVal s₄.mem base (a + 16) 7 = wordsVal s.mem base (a + 16) 7 := by
    rw [hm₄]; exact O₂.wordsVal (by omega) (by omega)
  have hdx₄ : s₄.gpr .rdx = word s.mem base a := by
    rw [k₄.1 .rdx (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨Ne.symm h2d, Ne.symm h1d⟩), d₃, hA]
  rw [d₃, hA, hA1] at e₄
  change xg s₄ 1 + 2 ^ 64 * xg s₄ 2 = _ at e₄
  have hAv := (word s.mem base a).isLt
  have hW7 : wordsVal s.mem base (a + 16) 7 < (2 ^ 64) ^ 7 := by
    rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ 7
  have hrow : xg s₄ 2 + (s₄.gpr .rdx).toNat * wordsVal s₄.mem base (a + 16) 7 < (2 ^ 64) ^ (7 + 1) := by
    rw [hdx₄, hW, pow64_succ']
    have h1 : 2 ^ 64 * xg s₄ 2 < 2 ^ 64 * 2 ^ 64 := by
      have := Nat.mul_lt_mul_of_lt_of_lt hAv (word s.mem base (a + 8)).isLt
      omega
    have h2 : (word s.mem base a).toNat * wordsVal s.mem base (a + 16) 7 ≤
        (2 ^ 64 - 1) * wordsVal s.mem base (a + 16) 7 := Nat.mul_le_mul_right _ (by omega)
    have h3 : (2 ^ 64 - 1) * wordsVal s.mem base (a + 16) 7 + wordsVal s.mem base (a + 16) 7 =
        2 ^ 64 * wordsVal s.mem base (a + 16) 7 := by rw [← Nat.succ_mul]
    have h4 : 2 ^ 64 * wordsVal s.mem base (a + 16) 7 + 2 ^ 64 ≤ 2 ^ 64 * (2 ^ 64) ^ 7 := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hW7
    have h5 : xg s₄ 2 < 2 ^ 64 := Nat.lt_of_mul_lt_mul_left h1
    omega
  refine WP.mono (accRow_ok hs₄ (k := 7) (j := 2) (d := a + 16) (by omega) (by omega) (by omega)
    (cf₄.trans (cf₃.trans (cf₂.trans c₁))) hrow) fun s₅ ⟨e₅, k₅⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [k₅.2.1, hm₄, m₂, word_writeW_self, z₁]; rfl
  · have hx₁ : xg s₅ 1 = xg s₄ 1 := congrArg BitVec.toNat (k₅.1 _ fun h => by
      rcases List.mem_cons.mp h with h | h
      · exact h1a h
      · obtain ⟨i, hi, e⟩ := mem_xSpan h
        exact xAcc_ne_of (show 1 < 2 + i by omega) (by omega) e)
    have hWv : wordsVal s.mem base (a + 8) 8 =
        (word s.mem base (a + 8)).toNat + 2 ^ 64 * wordsVal s.mem base (a + 16) 7 := by
      rw [show a + 16 = a + 8 + 8 by omega]; rfl
    rw [hval, hx₁, e₅, hdx₄, hW, hWv]
    generalize (word s.mem base a).toNat = A at *
    generalize wordsVal s.mem base (a + 16) 7 = W at *
    generalize (word s.mem base (a + 8)).toNat = B1 at *
    rw [Nat.mul_add A B1, Nat.mul_left_comm A (2 ^ 64) W, Nat.mul_add (2 ^ 64)]
    omega
  · have hr' : ∀ r, r ∉ Reg.rax :: Reg.rcx :: Reg.rdx :: xRegs →
        r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ ∀ k, xAcc k ≠ r := fun r hr => by
      simp only [List.mem_cons, not_or] at hr
      exact ⟨hr.1, hr.2.1, hr.2.2.1, fun k h => hr.2.2.2 (h ▸ (xAcc_ne k).2.2.2.2)⟩
    refine ⟨fun r hr => ?_, ?_, ?_⟩
    · obtain ⟨ra, -, rd, rx⟩ := hr' r hr
      rw [k₅.1 r (by
          simp only [List.mem_cons, not_or]
          exact ⟨ra, not_mem_xSpan rx 2 7⟩),
        k₄.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨(rx 2).symm, (rx 1).symm⟩),
        k₃.1 r (by simpa using rd), g₂, k₁.1 r (by simpa using ra)]
    · rw [k₅.2.2.1, k₄.2.2.1, k₃.2.2.1, rd₂, k₁.2.2.1]
    · rw [k₅.2.2.2, k₄.2.2.2, k₃.2.2.2, wr₂, k₁.2.2.2]
  · rw [k₅.2.1, hm₄]; exact O₂

/-- The first `n + 1 ≤ 8` rows: the low `n + 1` words of the products of two
different words stored in the temporary area, the others in `xWin (n + 1)`. -/
theorem sRows_ok {s₀ : State} {base : Addr} {size c₀ : Nat} (hs : ScrC s₀ base size c₀) {M : Mod} {a : Nat}
    (ha : a + 72 ≤ size) (ht : M.tmp + 72 ≤ size) (hat : a + 72 ≤ M.tmp ∨ M.tmp + 72 ≤ a) :
    ∀ n ≤ 7, WP isa (.block ((List.range (n + 1)).flatMap (sRowV M c₀ a))) s₀ fun s =>
      KeepRegs (.rax :: .rcx :: .rdx :: xRegs) s₀ s ∧ Outside base M.tmp 72 s₀.mem s.mem ∧
      wordsVal s.mem base M.tmp (n + 1) + (2 ^ 64) ^ (n + 1) * hval (xg s) (n + 1) 9 =
        sCross (fun j => (word s₀.mem base (a + 8 * j)).toNat) (n + 1)
  | 0, _ => by
    rw [show (List.range (0 + 1)).flatMap (sRowV M c₀ a) = sRow0 M c₀ a by simp [sRowV]]
    refine WP.mono (sRow0_ok hs ha (by omega) (by omega)) fun s ⟨z, e, k, O⟩ =>
      ⟨k, O.mono (Nat.le_refl _) (by omega), ?_⟩
    have hWv : wordsVal s₀.mem base (a + 8) 8 = hval (fun j => (word s₀.mem base (a + 8 * j)).toNat) 1 8 := by
      have := wordsVal_hval s₀.mem base a 1 8
      simpa using this
    have h1 : wordsVal s.mem base M.tmp (0 + 1) = (word s.mem base M.tmp).toNat := by simp [wordsVal]
    rw [h1, z, e, hWv]
    simp only [sCross, Nat.zero_add, Nat.mul_zero, Nat.add_zero, Nat.pow_one, Nat.sub_zero]
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (sRows_ok hs ha ht hat n (by omega)) fun s ⟨k, O, e⟩ => ?_
    rw [sRowV, ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
    exact sRow_inv hs ha ht hat (by omega) k O e

/-- `sDbl` in memory: `[tmp + 8w] = 2 [tmp + 8w] + d` with both carries. -/
theorem sDblM_ok {s : State} {base : Addr} {size c₀ : Nat} (hs : ScrC s base size c₀) {M : Mod} {w : Nat}
    (hw : M.tmp + 8 * w + 8 ≤ size) {d : Reg} (hd : d ≠ .rdx) {c o : Bool} (hc : s.cf = some c)
    (ho : s.of = some o) :
    WP isa (.block [.mov .rdx (.mem (rc c₀ (M.tmp + 8 * w))), .adcx .rdx (.reg .rdx), .adox .rdx (.reg d),
      .store (rc c₀ (M.tmp + 8 * w)) .rdx]) s fun s' => ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
      (word s'.mem base (M.tmp + 8 * w)).toNat + 2 ^ 64 * (c'.toNat + o'.toNat) =
        2 * (word s.mem base (M.tmp + 8 * w)).toNat + (s.gpr d).toNat + c.toNat + o.toNat ∧
      KeepRegs [.rdx] s s' ∧ Outside base (M.tmp + 8 * w) 8 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movRdx_ok s (readSrc_rc hs hw)) fun s₁ ⟨d₁, c₁, o₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (adcxS_ok s₁ (x := .rdx) (src := .reg .rdx) rfl (fun _ h => nomatch h) (c₁.trans hc))
    fun s₂ ⟨c₂, cf₂, of₂, e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (adoxS_ok s₂ (x := .rdx) (src := .reg d) rfl (fun _ h => nomatch h)
    (of₂.trans (o₁.trans ho))) fun s₃ ⟨o₃, of₃, cf₃, e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (storeXC_ok hs₃ .rdx hw) fun s₄ ⟨m₄, g₄, cf₄, of₄, rd₄, wr₄⟩ => ?_
  have hm₃ : s₃.mem = s.mem := k₃.2.1.trans (k₂.2.1.trans k₁.2.1)
  have hd₂ : s₂.gpr d = s.gpr d := by
    rw [k₂.1 d (by simpa using hd), k₁.1 d (by simpa using hd)]
  refine ⟨c₂, o₃, by rw [cf₄, cf₃, cf₂], by rw [of₄, of₃], ?_,
    ⟨fun r hr => ?_, by rw [rd₄, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1], by rw [wr₄, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]⟩, ?_⟩
  · rw [m₄, word_writeW_self]
    rw [d₁] at e₂
    rw [hd₂] at e₃
    change (s₂.gpr .rdx).toNat + 2 ^ 64 * c₂.toNat = (word s.mem base (M.tmp + 8 * w)).toNat +
      (word s.mem base (M.tmp + 8 * w)).toNat + c.toNat at e₂
    change (s₃.gpr .rdx).toNat + 2 ^ 64 * o₃.toNat = (s₂.gpr .rdx).toNat + (s.gpr d).toNat + o.toNat at e₃
    omega
  · simp only [List.mem_singleton] at hr
    rw [g₄, k₃.1 r (by simpa using hr), k₂.1 r (by simpa using hr), k₁.1 r (by simpa using hr)]
  · rw [m₄, hm₃]; exact writeW_outside _ _ _ (by omega)

/-- `sDbl` in a register: `t = 2 t + d` with both carries. -/
theorem sDblR_ok (s : State) {t d : Reg} (htd : t ≠ d) {c o : Bool} (hc : s.cf = some c)
    (ho : s.of = some o) :
    WP isa (.block [.adcx t (.reg t), .adox t (.reg d)]) s fun s' => ∃ c' o', s'.cf = some c' ∧
      s'.of = some o' ∧ (s'.gpr t).toNat + 2 ^ 64 * (c'.toNat + o'.toNat) =
        2 * (s.gpr t).toNat + (s.gpr d).toNat + c.toNat + o.toNat ∧ Keeps [t] s s' := by
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (adcxS_ok s (x := t) (src := .reg t) rfl (fun _ h => nomatch h) hc)
    fun s₁ ⟨c₁, cf₁, of₁, e₁, k₁⟩ => ?_
  refine WP.mono (adoxS_ok s₁ (x := t) (src := .reg d) rfl (fun _ h => nomatch h) (of₁.trans ho))
    fun s₂ ⟨o₂, of₂, cf₂, e₂, k₂⟩ => ?_
  have hd : s₁.gpr d = s.gpr d := k₁.1 d (by simpa using Ne.symm htd)
  refine ⟨c₁, o₂, by rw [cf₂, cf₁], of₂, ?_, (k₁.trans k₂)⟩
  change (s₁.gpr t).toNat + 2 ^ 64 * c₁.toNat = (s.gpr t).toNat + (s.gpr t).toNat + c.toNat at e₁
  change (s₂.gpr t).toNat + 2 ^ 64 * o₂.toNat = (s₁.gpr t).toNat + (s₁.gpr d).toNat + o.toNat at e₂
  rw [hd] at e₂
  omega


/-- Word `w < 18` of the square's accumulator: in the temporary area for
`w ≤ 8`, else in `xAcc w`. -/
def sqWord (M : Mod) (base : Addr) (s : State) (w : Nat) : Nat :=
  if w ≤ 8 then (word s.mem base (M.tmp + 8 * w)).toNat else xg s w

/-- `sDbl`: word `w` doubled and `d` added, the other words unchanged. -/
theorem sDbl_ok {s : State} {base : Addr} {size c₀ : Nat} (hs : ScrC s base size c₀) {M : Mod}
    (htmp : M.tmp + 72 ≤ size) {w : Nat} (hw : w < 18) {d : Reg} (hd : d = .rax ∨ d = .rcx) {c o : Bool}
    (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block (sDbl M c₀ w d)) s fun s' => ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
      sqWord M base s' w + 2 ^ 64 * (c'.toNat + o'.toNat) =
        2 * sqWord M base s w + (s.gpr d).toNat + c.toNat + o.toNat ∧
      (∀ w', w' < 18 → w' ≠ w → sqWord M base s' w' = sqWord M base s w') ∧
      KeepRegs (.rdx :: xRegs) s s' ∧ s'.gpr .rax = s.gpr .rax ∧ s'.gpr .rcx = s.gpr .rcx ∧
      Outside base M.tmp 72 s.mem s'.mem := by
  have hnw := hs.nowrap
  have hdx : d ≠ .rdx := by rcases hd with rfl | rfl <;> decide
  unfold sDbl
  split
  · rename_i hw8
    refine WP.mono (sDblM_ok hs (M := M) (w := w) (by omega) hdx hc ho)
      fun s' ⟨c', o', cf', of', e, k, O⟩ => ⟨c', o', cf', of', ?_, fun w' hw' hne => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [sqWord, hw8, ↓reduceIte]; exact e
    · simp only [sqWord]
      split
      · exact congrArg BitVec.toNat (O.word (by omega) (by omega))
      · simp only [xg]; rw [k.gpr _ (by simpa using (xAcc_ne w').2.2.1)]
    · exact k.mono (by sub_regs)
    · exact k.gpr _ (by decide)
    · exact k.gpr _ (by decide)
    · exact O.mono (by omega) (by omega)
  · rename_i hw8
    have htd : xAcc w ≠ d := by
      rcases hd with rfl | rfl
      · exact (xAcc_ne w).1
      · exact (xAcc_ne w).2.1
    refine WP.mono (sDblR_ok s htd hc ho)
      fun s' ⟨c', o', cf', of', e, k⟩ => ⟨c', o', cf', of', ?_, fun w' hw' hne => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [sqWord, hw8, ↓reduceIte, xg]; exact e
    · simp only [sqWord]
      split
      · rw [k.2.1]
      · simp only [xg]
        rw [k.1 _ (by
          simp only [List.mem_singleton]
          rcases Nat.lt_or_gt_of_ne hne with h | h
          · exact xAcc_ne_of h (by omega)
          · exact (xAcc_ne_of h (by omega)).symm)]
    · exact (Keeps.regs k).mono (by
        intro q hq
        simp only [List.mem_singleton] at hq
        exact hq ▸ List.mem_cons_of_mem _ (xAcc_ne w).2.2.2.2)
    · exact k.1 _ (by simpa using (xAcc_ne w).1.symm)
    · exact k.1 _ (by simpa using (xAcc_ne w).2.1.symm)
    · rw [k.2.1]; exact Outside.refl _ _ _ _


/-- Step `k < 9` of the squares: words `2k`, `2k + 1` doubled and `a_k²`
added, with the carries in and out. -/
theorem sDiagK_ok {s : State} {base : Addr} {size c₀ : Nat} (hs : ScrC s base size c₀) {M : Mod} {a : Nat}
    (htmp : M.tmp + 72 ≤ size) (ha : a + 72 ≤ size) {k : Nat} (hk : k < 9) {c o : Bool}
    (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block (sDiagK M c₀ a k)) s fun s' => ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
      sqWord M base s' (2 * k) + 2 ^ 64 * sqWord M base s' (2 * k + 1) + 2 ^ 64 * 2 ^ 64 * (c'.toNat + o'.toNat) =
        2 * (sqWord M base s (2 * k) + 2 ^ 64 * sqWord M base s (2 * k + 1)) +
          (word s.mem base (a + 8 * k)).toNat * (word s.mem base (a + 8 * k)).toNat + c.toNat + o.toNat ∧
      (∀ w', w' < 18 → w' ≠ 2 * k → w' ≠ 2 * k + 1 → sqWord M base s' w' = sqWord M base s w') ∧
      KeepRegs (.rax :: .rcx :: .rdx :: xRegs) s s' ∧ Outside base M.tmp 72 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [sDiagK, List.append_assoc, WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movRdx_ok s (readSrc_rc hs (d := a + 8 * k) (by omega))) fun s₁ ⟨d₁, c₁, o₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (mulx_ok s₁ (hi := .rcx) (lo := .rax) (src := .reg .rdx) rfl (fun _ h => nomatch h)
    (by decide)) fun s₂ ⟨e₂, c₂, o₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sDbl_ok hs₂ htmp (w := 2 * k) (by omega) (.inl rfl) (c₂.trans (c₁.trans hc))
    (o₂.trans (o₁.trans ho))) fun s₃ ⟨c₃, o₃, cf₃, of₃, e₃, u₃, k₃, ra₃, rc₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  refine WP.mono (sDbl_ok hs₃ htmp (w := 2 * k + 1) (by omega) (.inr rfl) cf₃ of₃)
    fun s₄ ⟨c₄, o₄, cf₄, of₄, e₄, u₄, k₄, ra₄, rc₄, O₄⟩ => ?_
  have hm₂ : s₂.mem = s.mem := k₂.2.1.trans k₁.2.1
  have hsv₂ : ∀ w, sqWord M base s₂ w = sqWord M base s w := fun w => by
    simp only [sqWord, xg]
    split
    · rw [hm₂]
    · rw [k₂.1 _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨(xAcc_ne w).2.1, (xAcc_ne w).1⟩), k₁.1 _ (by simpa using (xAcc_ne w).2.2.1)]
  refine ⟨c₄, o₄, cf₄, of₄, ?_, fun w' h1 h2 h3 => ?_, ?_, ?_⟩
  · rw [u₄ (2 * k) (by omega) (by omega)] at *
    rw [u₃ (2 * k + 1) (by omega) (by omega), hsv₂] at e₄
    rw [hsv₂] at e₃
    rw [rc₃] at e₄
    rw [d₁] at e₂
    change (s₂.gpr .rax).toNat + 2 ^ 64 * (s₂.gpr .rcx).toNat =
      (word s.mem base (a + 8 * k)).toNat * (word s.mem base (a + 8 * k)).toNat at e₂
    omega
  · rw [u₄ w' h1 h3, u₃ w' h1 h2, hsv₂]
  · refine ⟨fun r hr => ?_, by rw [k₄.rd, k₃.rd, k₂.2.2.1, k₁.2.2.1], by rw [k₄.wr, k₃.wr, k₂.2.2.2, k₁.2.2.2]⟩
    simp only [List.mem_cons, not_or] at hr
    rw [k₄.gpr r (by simp only [List.mem_cons, not_or]; exact ⟨hr.2.2.1, hr.2.2.2⟩),
      k₃.gpr r (by simp only [List.mem_cons, not_or]; exact ⟨hr.2.2.1, hr.2.2.2⟩),
      k₂.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.2.1, hr.1⟩),
      k₁.1 r (by simpa using hr.2.2.1)]
  · rw [← hm₂]; exact O₃.trans O₄

theorem sDiag_arith {X H H0 Q A0 A1 B0 B1 sq dg c o c' o' : Nat}
    (inv : H + Q * (c + o) = 2 * H0 + dg)
    (e : B0 + X * B1 + X * X * (c' + o') = 2 * (A0 + X * A1) + sq + c + o) :
    H + Q * (B0 + X * B1) + Q * (X * X) * (c' + o') = 2 * (H0 + Q * (A0 + X * A1)) + (dg + Q * sq) := by
  have e' : Q * (B0 + X * B1 + X * X * (c' + o')) = Q * (2 * (A0 + X * A1) + sq + c + o) := by rw [e]
  grind

/-- The squares `Σ_{k<n} 2^(128 k) f_k²`. -/
def sDg (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => sDg f k + (2 ^ 64) ^ (2 * k) * (f k * f k)

theorem hval_two (g : Nat → Nat) (n : Nat) :
    hval g 0 (2 * n + 2) = hval g 0 (2 * n) + (2 ^ 64) ^ (2 * n) * (g (2 * n) + 2 ^ 64 * g (2 * n + 1)) := by
  rw [hval_add g 0 (2 * n) 2, Nat.zero_add]
  simp only [hval, Nat.mul_zero, Nat.add_zero]

/-- The first `n ≤ 9` steps of the squares: the words below `2n` doubled
with the squares added, the carries out at word `2n`. -/
theorem sDiags_ok {s₀ : State} {base : Addr} {size c₀ : Nat} (hs : ScrC s₀ base size c₀) {M : Mod} {a : Nat}
    (htmp : M.tmp + 72 ≤ size) (ha : a + 72 ≤ size) (hat : a + 72 ≤ M.tmp ∨ M.tmp + 72 ≤ a)
    (hc₀ : s₀.cf = some false) (ho₀ : s₀.of = some false) :
    ∀ n ≤ 9, WP isa (.block ((List.range n).flatMap (sDiagK M c₀ a))) s₀ fun s => ∃ c o : Bool,
      s.cf = some c ∧ s.of = some o ∧
      hval (sqWord M base s) 0 (2 * n) + (2 ^ 64) ^ (2 * n) * (c.toNat + o.toNat) =
        2 * hval (sqWord M base s₀) 0 (2 * n) + sDg (fun j => (word s₀.mem base (a + 8 * j)).toNat) n ∧
      (∀ w, 2 * n ≤ w → w < 18 → sqWord M base s w = sqWord M base s₀ w) ∧
      KeepRegs (.rax :: .rcx :: .rdx :: xRegs) s₀ s ∧ Outside base M.tmp 72 s₀.mem s.mem
  | 0, _ => WP.block_nil ⟨false, false, hc₀, ho₀, by simp [hval, sDg], fun _ _ _ => rfl,
      ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (sDiags_ok hs htmp ha hat hc₀ ho₀ n (by omega)) fun s ⟨c, o, hc, ho, e, u, k, O⟩ => ?_
    have hnw := hs.nowrap
    have hsS : ScrC s base size c₀ := hs.of_keepRegs k (by decide)
    refine WP.mono (sDiagK_ok hsS htmp ha (k := n) (by omega) hc ho)
      fun s' ⟨c', o', cf', of', e', u', k', O'⟩ => ⟨c', o', cf', of', ?_, fun w h1 h2 => ?_, k.trans k', O.trans O'⟩
    · have hA : word s.mem base (a + 8 * n) = word s₀.mem base (a + 8 * n) := O.word (by omega) (by omega)
      rw [hA, u (2 * n) (by omega) (by omega), u (2 * n + 1) (by omega) (by omega)] at e'
      have hL : hval (sqWord M base s') 0 (2 * n) = hval (sqWord M base s) 0 (2 * n) :=
        hval_congr fun c h1 h2 => u' c (by omega) (by omega) (by omega)
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, hval_two, hval_two, hL, sDg,
        show (2 ^ 64 : Nat) ^ (2 * n + 2) = (2 ^ 64) ^ (2 * n) * (2 ^ 64 * 2 ^ 64) by
          rw [Nat.pow_add (2 ^ 64) (2 * n) 2, Nat.pow_two]]
      exact sDiag_arith e e'
    · rw [u' w h2 (by omega) (by omega), u w (by omega) h2]


/-- The square of nine words: twice the products of two different words, and
the squares. -/
theorem sq_ident (f : Nat → Nat) : hval f 0 9 * hval f 0 9 = 2 * sCross f 8 + sDg f 9 := by
  simp only [hval, sCross, sDg, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
  generalize f 0 = a0
  generalize f 1 = a1
  generalize f 2 = a2
  generalize f 3 = a3
  generalize f 4 = a4
  generalize f 5 = a5
  generalize f 6 = a6
  generalize f 7 = a7
  generalize f 8 = a8
  generalize (2 : Nat) ^ 64 = X
  grind


theorem sDg_congr {f g : Nat → Nat} : ∀ {n}, (∀ j < n, f j = g j) → sDg f n = sDg g n
  | 0, _ => rfl
  | n + 1, h => by rw [sDg, sDg, sDg_congr fun j hj => h j (by omega), h n (by omega)]

/-- `[o] = [a]² R⁻¹ mod p` for P-521's `p`, `R = 2⁵⁷⁶`, with BMI2 and ADX. -/
theorem sqrPX_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) (hred : M.red = .friendly p521Ws) {o a : Nat}
    (ho : o + 8 * M.n ≤ size) (ha : a + 8 * M.n ≤ size)
    (_hoT : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o) (haT : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ a)
    (_hoM : o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ o) (hB : wordsVal s.mem base a M.n < m) :
    WP isa (.block (sqrPX M o a)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base a M.n % m := by
  obtain ⟨hn9, hm⟩ := p521_of_red hred hM.red
  have htmp := hM.tmp
  have hnw := hs.nowrap
  rw [Nat.pow_mul]
  rw [hn9] at ho ha haT htmp ⊢
  rw [hn9] at hB
  rw [sqrPX]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (rdiAdd_ok hs (cOf_lt a)) fun s₁ ⟨hs₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sRows_ok hs₁ (M := M) (a := a) (by omega) (by omega) (by omega) 7 (by omega))
    fun s₂ ⟨k₂, O₂, e₂⟩ => ?_
  rw [k₁.2.1] at e₂ O₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff, sDiag, WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (storeXC_ok hs₂ (xAcc 8) (d := M.tmp + 64) (by omega)) fun s₃ ⟨m₃, g₃, cf₃, of₃, rd₃, wr₃⟩ => ?_
  have hs₃ : ScrC s₃ base size (cOf a) := ⟨by rw [g₃]; exact hs₂.rdi, by rw [wr₃]; exact hs₂.wr, hs₂.nowrap⟩
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movZero_ok s₃ (xAcc 17)) fun s₄ ⟨z₄, _, _, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by simpa using (xAcc_ne 17).2.2.2.1.symm)
  refine WP.mono (xorRax_ok s₄) fun s₅ ⟨c₅, o₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  have hm₅ : s₅.mem = s₃.mem := k₅.2.1.trans k₄.2.1
  have O₃ : Outside base (M.tmp + 64) 8 s₂.mem s₃.mem := by
    rw [m₃]; exact writeW_outside _ _ _ (by omega)
  -- The accumulator before the squares is the products of two different words.
  have hx₅ : ∀ c, 9 ≤ c → c < 17 → xg s₅ c = xg s₂ c := fun c h1 h2 => by
    simp only [xg]
    rw [k₅.1 _ (by simpa using (xAcc_ne c).1), k₄.1 _ (by simpa using (xAcc_ne_of h2 (by omega))), g₃]
  have h17 : xg s₅ 17 = 0 := by
    simp only [xg]; rw [k₅.1 _ (by simpa using (xAcc_ne 17).1), z₄]; rfl
  have hS₅ : hval (sqWord M base s₅) 0 18 = wordsVal s₂.mem base M.tmp 8 + (2 ^ 64) ^ 8 * hval (xg s₂) 8 9 := by
    have hlo : hval (sqWord M base s₅) 0 8 = wordsVal s₂.mem base M.tmp 8 := by
      rw [show M.tmp = M.tmp + 8 * 0 from rfl, wordsVal_hval]
      exact hval_congr fun c _ h2 => by
        simp only [sqWord, show c ≤ 8 by omega, ↓reduceIte, hm₅]
        exact congrArg BitVec.toNat (O₃.word (by omega) (by omega))
    have h8 : sqWord M base s₅ 8 = xg s₂ 8 := by
      simp only [sqWord, show (8 : Nat) ≤ 8 from Nat.le_refl _, ↓reduceIte, hm₅, m₃, xg]
      rw [show M.tmp + 8 * 8 = M.tmp + 64 from rfl, word_writeW_self]
    have hhi : hval (sqWord M base s₅) 9 8 = hval (xg s₂) 9 8 :=
      hval_congr fun c h1 h2 => by
        simp only [sqWord, show ¬ c ≤ 8 by omega, ↓reduceIte]
        exact hx₅ c h1 (by omega)
    have h17' : sqWord M base s₅ 17 = 0 := by simp only [sqWord, show ¬ (17 ≤ 8) by decide, ↓reduceIte]; exact h17
    rw [hval_add (sqWord M base s₅) 0 8 10, Nat.zero_add, hlo, show (10 : Nat) = 9 + 1 from rfl, hval, h8,
      hval_succ_last, hhi, h17', Nat.mul_zero, Nat.add_zero]
    rw [show hval (xg s₂) 8 9 = xg s₂ 8 + 2 ^ 64 * hval (xg s₂) 9 8 from rfl]
  refine WP.mono (sDiags_ok hs₅ (M := M) (a := a) (by omega) (by omega) (by omega) c₅ o₅ 9 (Nat.le_refl _))
    fun s₆ ⟨c₆, o₆, _, _, e₆, _, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  -- The square.
  generalize hf : (fun j => (word s.mem base (a + 8 * j)).toNat) = f at e₂
  have hf₅ : sDg (fun j => (word s₅.mem base (a + 8 * j)).toNat) 9 = sDg f 9 :=
    sDg_congr fun j hj => by
      rw [← hf, hm₅, m₃]
      exact congrArg BitVec.toNat ((writeW_outside _ _ _ (by omega)).word (by omega) (by omega) |>.trans
        (O₂.word (by omega) (by omega)))
  have hA : wordsVal s.mem base a 9 = hval f 0 9 := by
    rw [← hf, ← wordsVal_hval s.mem base a 0 9, Nat.mul_zero, Nat.add_zero]
  have hAl : wordsVal s.mem base a 9 < (2 ^ 64) ^ 9 := by rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ 9
  rw [hS₅, e₂, hf₅, ← sq_ident, ← hA, show 2 * 9 = 18 from rfl] at e₆
  have hAA : wordsVal s.mem base a 9 * wordsVal s.mem base a 9 < (2 ^ 64) ^ 18 := by
    rw [show (18 : Nat) = 9 + 9 from rfl, Nat.pow_add]; exact Nat.mul_lt_mul'' hAl hAl
  have hT : hval (sqWord M base s₆) 0 18 = wordsVal s₆.mem base M.tmp 9 + (2 ^ 64) ^ 9 * hval (xg s₆) 9 9 := by
    have h1 : hval (sqWord M base s₆) 0 9 = wordsVal s₆.mem base M.tmp 9 := by
      rw [show M.tmp = M.tmp + 8 * 0 from rfl, wordsVal_hval]
      exact hval_congr fun c _ h2 => by simp only [sqWord, show c ≤ 8 by omega, ↓reduceIte]
    have h2 : hval (sqWord M base s₆) 9 9 = hval (xg s₆) 9 9 :=
      hval_congr fun c h1 _ => by simp only [sqWord, show ¬ c ≤ 8 by omega, ↓reduceIte]
    rw [show (18 : Nat) = 9 + 9 from rfl, hval_add, Nat.zero_add, h1, h2]
  have e₆' : wordsVal s₆.mem base M.tmp 9 + (2 ^ 64) ^ 9 * hval (xg s₆) 9 9 =
      wordsVal s.mem base a 9 * wordsVal s.mem base a 9 := by
    rw [← hT]
    have : (2 ^ 64) ^ 18 * (c₆.toNat + o₆.toNat) < (2 ^ 64) ^ 18 * 1 := by omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  rw [WP.block_append_iff]
  refine WP.mono (rdiSub_ok hs₆ (cOf_lt a)) fun s₆' ⟨hs₆', k₆'⟩ => ?_
  have hx₆ : hval (xg s₆') 9 9 = hval (xg s₆) 9 9 := hval_congr fun c _ _ => by
    simp only [xg]; rw [k₆'.1 _ (by simpa using (xAcc_ne c).2.2.2.1)]
  rw [← k₆'.2.1, ← hx₆] at e₆'
  rw [WP.block_append_iff]
  refine WP.mono (xRed_ok hs₆' (M := M) (by omega)) fun s₇ ⟨acc, e₇, k₇, O₇⟩ => ?_
  have hs₇ := hs₆'.of_keepRegs k₇ (by decide)
  rw [e₆'] at e₇
  have hU : wordsVal s₇.mem base M.tmp 9 < (2 ^ 64) ^ 9 := by rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ 9
  obtain ⟨hW1, hW2, eW⟩ := mulP_arith1 hm hAl hB hU e₇.symm
  refine WP.mono (xCanon_ok hs₇ (o := o) (by omega) hm hW1 hW2) fun s₈ ⟨e₈, k₈, O₈⟩ => ?_
  have hmo : 0 < m := by omega
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_, ?_⟩
  · have hr' : r ∉ Reg.rax :: Reg.rcx :: Reg.rdx :: xRegs := fun h => hr (by rw [hn9]; exact xRegs_clob r h)
    have hx : ∀ k, xAcc k ≠ r := fun k h => hr' (h ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (xAcc_ne k).2.2.2.2)))
    rw [k₈.gpr r (fun h => hr' (by
        rcases List.mem_cons.mp h with h | h
        · exact h ▸ List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))),
      k₇.gpr r hr']
    by_cases hrd : r = .rdi
    · rw [hrd, hs₆'.rdi, hs.rdi]
    · rw [k₆'.1 r (by simpa using hrd), k₆.gpr r hr',
        k₅.1 r (fun h => hr' (by simp only [List.mem_singleton] at h; exact h ▸ List.mem_cons_self ..)),
        k₄.1 r (by simpa using (hx 17).symm), g₃, k₂.gpr r hr', k₁.1 r (by simpa using hrd)]
  · rw [k₈.rd, k₇.rd, k₆'.2.2.1, k₆.rd, k₅.2.2.1, k₄.2.2.1, rd₃, k₂.rd, k₁.2.2.1]
  · rw [k₈.wr, k₇.wr, k₆'.2.2.2, k₆.wr, k₅.2.2.2, k₄.2.2.2, wr₃, k₂.wr, k₁.2.2.2]
  · rw [hn9] at hx hx'
    rw [O₈ x hx, O₇ x (by omega), k₆'.2.1, O₆ x hx', hm₅, O₃ x (by omega), O₂ x hx']
  · rw [e₈]; exact Nat.mod_lt _ hmo
  · rw [e₈, Nat.mod_mul_mod, Nat.mul_comm, eW, Nat.add_mul_mod_self_right]

end VG.Proof.Mont.X86_64
