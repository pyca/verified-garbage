import VerifiedGarbage.Proof.Mont.X86_64.SparseX
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Steps

/-!
# Montgomery arithmetic on x86-64: a round with BMI2 and ADX

A row `ts += rdx · [d]` (`rowX`) is `xor ebp, ebp`, then for each word the
product's low half added through OF and its high half through CF (`madd`,
X25519's step, `madd_ok`), then the carries left (`carriesX`). `maddSteps_ok`
states what the products give, the two carries out pending, by induction
over the words; `rowX_ok`, what the row gives when it does not overflow.
`roundX_ok` is a round with rows, and `round_ok` a round either way.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono madd_ok carries_ok clear_ok movRdx_ok of_setReg
  of_setFlags adc_carry)

theorem madd_eq (x y : Reg) (src : Src) :
    madd x y src = Impl.X25519.X86_64.madd x y src := rfl

theorem clearX_eq : clearX = Impl.X25519.X86_64.clear := rfl

/-- `adox x, rbp` with `rbp = 0`: the carry OF added into `x`. -/
theorem carryO_ok (s : State) {x : Reg} {o : Bool} (ho : s.of = some o) (hz : s.gpr .rbp = 0) :
    WP isa (.block [.adox x (.reg .rbp)]) s fun s' =>
      ∃ o', s'.of = some o' ∧ s'.cf = s.cf ∧
        (s'.gpr x).toNat + 2 ^ 64 * o'.toNat = (s.gpr x).toNat + o.toNat ∧ Keeps [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAdox, readSrc, hz, ho,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.cf_setReg,
    RegUpd.cf_setFlags, of_setReg, of_setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), ?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · have := adc_carry (s.gpr x) 0 o
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at this ⊢
    exact this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `k` products along `ts`: `rdx · [d … d + 8k)` added at the words
`ts₀ … ts_k`, with the carries OF into `ts₀` and CF into `ts₁` in, and OF
(into `ts_k`) and CF (into `ts_{k+1}`) out. -/
theorem maddSteps_ok {size : Nat} : ∀ (k : Nat) (ts : List Reg) {s : State} {base : Addr} {d : Nat}
    {c o : Bool}, Scr s base size → d + 8 * k ≤ size → k + 1 ≤ ts.length → FreshX ts →
    s.cf = some c → s.of = some o →
    WP isa (.block (maddSteps k ts d)) s fun s' => ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
      regsVal s' (ts.take (k + 1)) + 2 ^ (64 * k) * o'.toNat + 2 ^ (64 * (k + 1)) * c'.toNat =
        regsVal s (ts.take (k + 1)) + o.toNat + 2 ^ 64 * c.toNat +
          (s.gpr .rdx).toNat * wordsVal s.mem base d k ∧
      Keeps (.rcx :: .rax :: ts.take (k + 1)) s s'
  | 0, ts, s, _, _, c, o, _, _, _, _, hc, ho => by
    show WP isa (.block []) s _
    exact WP.block_nil ⟨c, o, hc, ho, by simp [wordsVal], fun _ _ => rfl, rfl, rfl, rfl⟩
  | _ + 1, [], _, _, _, _, _, _, _, hl, _, _, _ => absurd hl (by simp)
  | _ + 1, [_], _, _, _, _, _, _, _, hl, _, _, _ => absurd hl (by simp)
  | k + 1, x :: y :: rest, s, base, d, c, o, hs, hd, hl, hf, hc, ho => by
    obtain ⟨hxn, hxa, hxc, hxd, hxr⟩ := hf.head
    obtain ⟨hyn, hya, hyc, hyd, hyr⟩ := hf.tail.head
    have hxy : x ≠ y := fun h => hxn (h ▸ List.mem_cons_self ..)
    simp only [List.length_cons] at hl
    rw [maddSteps, madd_eq, WP.block_append_iff]
    refine WP.mono (madd_ok s (readSrc_sc hs (d := d) (by omega)) (fun _ h => nomatch h) hc ho hxc hxa
      hyc hya hxy) fun s₁ ⟨c₁, o₁, cf₁, of₁, e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by decide, by decide, Ne.symm hxr, Ne.symm hyr⟩)
    refine WP.mono (maddSteps_ok k (y :: rest) hs₁ (d := d + 8) (by omega)
      (by simp only [List.length_cons]; omega) hf.tail cf₁ of₁) fun s₂ ⟨c', o', cf₂, of₂, e₂, k₂⟩ =>
      ⟨c', o', cf₂, of₂, ?_, ?_⟩
    · have hdx : s₁.gpr .rdx = s.gpr .rdx := k₁.1 .rdx (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨by decide, by decide, Ne.symm hxd, Ne.symm hyd⟩)
      have hx₂ : s₂.gpr x = s₁.gpr x := k₂.1 x (by
        simp only [List.mem_cons, not_or]
        exact ⟨hxc, hxa, fun h => hxn (List.mem_of_mem_take h)⟩)
      have hR : regsVal s₁ (rest.take k) = regsVal s (rest.take k) := regsVal_congr fun q hq => k₁.1 q (by
        have hq' := List.mem_of_mem_take hq
        have := hf.2 q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq'))
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨this.2.1, this.1, fun h => hxn (h ▸ List.mem_cons_of_mem _ hq'),
          fun h => hyn (h ▸ hq')⟩)
      rw [k₁.2.1, hdx] at e₂
      simp only [List.take_succ_cons, regsVal, hR] at e₂ ⊢
      simp only [wordsVal]
      rw [hx₂]
      rw [pow64_succ (k + 1), pow64_succ k] at *
      simp only [Nat.mul_assoc] at e₂ ⊢
      rw [Nat.mul_add (s.gpr .rdx).toNat, Nat.mul_left_comm (s.gpr .rdx).toNat (2 ^ 64)]
      omega
    · simp only [List.take_succ_cons] at k₂ ⊢
      exact (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))

/-- A row: `ts += rdx · [d]` for the words `ts = L ++ [tn, tn1]` (`L` of the
row's length), if it does not overflow. -/
theorem rowX_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {L : List Reg}
    {tn tn1 : Reg} (hf : Fresh (L ++ [tn, tn1])) {d : Nat} (hd : d + 8 * L.length ≤ size)
    (hb : regsVal s (L ++ [tn, tn1]) + (s.gpr .rdx).toNat * wordsVal s.mem base d L.length <
      2 ^ (64 * (L.length + 2))) :
    WP isa (.block (rowX L.length (L ++ [tn, tn1]) d)) s fun s' =>
      regsVal s' (L ++ [tn, tn1]) = regsVal s (L ++ [tn, tn1]) +
        (s.gpr .rdx).toNat * wordsVal s.mem base d L.length ∧
      Keeps (.rbp :: .rcx :: .rax :: (L ++ [tn, tn1])) s s' := by
  have ht : (L ++ [tn, tn1]).take (L.length + 1) = L ++ [tn] := by
    clear hf hb hd
    induction L with
    | nil => rfl
    | cons a L ih => simp only [List.length_cons, List.cons_append, List.take_succ_cons, ih]
  have hg0 : (L ++ [tn, tn1]).getD L.length .r8 = tn := by simp
  have hg1 : (L ++ [tn, tn1]).getD (L.length + 1) .r8 = tn1 := by simp
  have fn := hf.2 tn (by simp)
  have fn1 := hf.2 tn1 (by simp)
  have hnd := hf.1
  simp only [List.nodup_append, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
  have htn : tn ∉ L := fun h => hnd.2.2 tn h tn (Or.inl rfl) rfl
  have htn1 : tn1 ∉ L := fun h => hnd.2.2 tn1 h tn1 (Or.inr rfl) rfl
  have hnn : tn ≠ tn1 := hnd.2.1.1
  rw [rowX, hg0, hg1, ← List.singleton_append, WP.block_append_iff, WP.block_append_iff, clearX_eq]
  refine WP.mono (clear_ok s) fun s₁ ⟨z₁, cf₁, of₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have g₁ : ∀ q, q ≠ .rbp → s₁.gpr q = s.gpr q := fun q h => k₁.1 q (by simpa using h)
  refine WP.mono (maddSteps_ok L.length (L ++ [tn, tn1]) hs₁ hd (by simp) hf.toX cf₁ of₁)
    fun s₂ ⟨c', o', cf₂, of₂, e₂, k₂⟩ => ?_
  rw [ht] at e₂ k₂
  have g₂ : ∀ q, q ≠ .rcx → q ≠ .rax → q ∉ L → q ≠ tn → s₂.gpr q = s₁.gpr q := fun q h1 h2 h3 h4 =>
    k₂.1 q (by simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2, h3, h4⟩)
  have z₂ : s₂.gpr .rbp = 0 := by
    rw [g₂ .rbp (by decide) (by decide) (fun h => (hf.2 _ (List.mem_append_left _ h)).2.2.2.1 rfl)
      (Ne.symm fn.2.2.2.1), z₁]
  rw [carriesX, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (carryO_ok s₂ of₂ z₂) fun s₃ ⟨o₃, of₃, cf₃, e₃, k₃⟩ => ?_
  have z₃ : s₃.gpr .rbp = 0 := by rw [k₃.1 .rbp (by simpa using Ne.symm fn.2.2.2.1), z₂]
  refine WP.mono (carries_ok s₃ (cf₃.trans cf₂) of₃ z₃ fn1.2.2.2.1) fun s₄ ⟨c₄, o₄, cf₄, of₄, e₄, k₄⟩ => ⟨?_, ?_⟩
  · -- The words of `L`, `tn` and `tn1` through the steps.
    have hL : regsVal s₄ L = regsVal s₂ L := regsVal_congr fun q hq => by
      have h1 : q ≠ tn1 := fun h => htn1 (h ▸ hq)
      have h2 : q ≠ tn := fun h => htn (h ▸ hq)
      rw [k₄.1 q (by simpa using h1), k₃.1 q (by simpa using h2)]
    have hL₁ : regsVal s₁ L = regsVal s L := regsVal_congr fun q hq =>
      g₁ q (fun h => (hf.2 _ (List.mem_append_left _ hq)).2.2.2.1 h)
    have t4 : s₄.gpr tn = s₃.gpr tn := k₄.1 tn (by simpa using hnn)
    have t13 : s₃.gpr tn1 = s₂.gpr tn1 := k₃.1 tn1 (by simpa using Ne.symm hnn)
    have t12 : s₂.gpr tn1 = s.gpr tn1 := by
      rw [g₂ tn1 fn1.2.1 fn1.1 htn1 (Ne.symm hnn), g₁ tn1 fn1.2.2.2.1]
    have tn₁ : s₁.gpr tn = s.gpr tn := g₁ tn fn.2.2.2.1
    have rdx₁ : s₁.gpr .rdx = s.gpr .rdx := g₁ .rdx (by decide)
    simp only [regsVal_append, regsVal, Nat.mul_zero, Nat.add_zero, Bool.toNat_false, k₁.2.1, rdx₁, hL₁,
      tn₁] at e₂ hb ⊢
    rw [hL, t4]
    rw [t13, t12] at e₄
    rw [show 64 * (L.length + 2) = 128 + 64 * L.length by omega, Nat.pow_add] at hb
    rw [pow64_succ] at e₂
    generalize 2 ^ (64 * L.length) = P at *
    have m3 := congrArg (P * ·) e₃
    have m4 := congrArg (P * ·) e₄
    simp only [Nat.mul_add, Nat.mul_assoc] at m3 m4 e₂ hb ⊢
    simp only [Nat.mul_left_comm P (2 ^ 64)] at m3 m4 e₂ hb ⊢
    cases c₄ <;> cases o₄ <;>
      simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero, Nat.add_zero] at m4 <;>
      omega
  · exact (((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans (k₃.mono (by sub_regs))).trans
      (k₄.mono (by sub_regs))

/-- `rdx = t₀ m' mod 2⁶⁴`. -/
theorem uRdx_ok (s : State) (t0 : Reg) (minv : BitVec 64) :
    WP isa (.block [.mov .rax (.reg t0), .movImm64 .rcx minv, .mul .rcx, .mov .rdx (.reg .rax)]) s
      fun s' => (s'.gpr .rdx).toNat = (s.gpr t0).toNat * minv.toNat % 2 ^ 64 ∧
        Keeps [.rax, .rcx, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execMul, Option.map_some,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left']
  refine ⟨BitVec.toNat_ofNat _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2, ite_false]

/-- A row over the window of round `i`, as `rowX_ok` takes it. -/
theorem rowX_wins (n i d : Nat) : rowX n (wins n i) d =
    rowX ((List.range n).map (win n i)).length ((List.range n).map (win n i) ++ [win n i n, win n i (n + 1)]) d := by
  rw [← wins_split]; simp

/-- The general reduction of round `i` with BMI2 and ADX: `2⁶⁴ T' = T + u m`, if
`T < 2m + (2⁶⁴ - 1) m`. -/
theorem redGenX_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    (hn : M.n < 7) {i m : Nat} (hmo : M.mo + 8 * M.n ≤ size) (hm : wordsVal s.mem base M.mo M.n = m)
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0)
    (hT : regsVal s (wins M.n i) < 2 * m + (2 ^ 64 - 1) * m) :
    WP isa (.block (([.mov .rax (.reg (win M.n i 0)), .movImm64 .rcx M.minv, .mul .rcx, .mov .rdx (.reg .rax)] :
          List Instr) ++ rowX M.n (wins M.n i) M.mo)) s fun s' =>
      (∃ u, u < 2 ^ 64 ∧ 2 ^ 64 * regsVal s' (wins M.n (i + 1)) = regsVal s (wins M.n i) + u * m) ∧
      Keeps (.rax :: .rcx :: .rdx :: .rbp :: wins M.n i) s s' := by
  have hW := wins_split M.n i
  have hf : Fresh ((List.range M.n).map (win M.n i) ++ [win M.n i M.n, win M.n i (M.n + 1)]) :=
    hW ▸ fresh_wins hn i
  have hl : ((List.range M.n).map (win M.n i)).length = M.n := by simp
  have hm' : m < 2 ^ (64 * M.n) := hm ▸ wordsVal_lt _ _ _ _
  rw [WP.block_append_iff]
  refine WP.mono (uRdx_ok s (win M.n i 0) M.minv) fun s₃ ⟨u₃, k₃⟩ => ?_
  have hs₃ := hs.of_keeps k₃ (by decide)
  have hT₃ : regsVal s₃ (wins M.n i) = regsVal s (wins M.n i) := regsVal_congr fun q hq =>
    k₃.1 q (by
      have := (fresh_wins hn i).2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨this.1, this.2.1, this.2.2.1⟩)
  have hu := (s₃.gpr .rdx).isLt
  have hum : (s₃.gpr .rdx).toNat * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul (by omega) (Nat.le_refl _)
  have hmem₃ : s₃.mem = s.mem := k₃.2.1
  have hP : 2 ^ (64 * (M.n + 2)) = 2 ^ 128 * 2 ^ (64 * M.n) := by
    rw [show 64 * (M.n + 2) = 128 + 64 * M.n by omega, Nat.pow_add]
  rw [rowX_wins]
  refine WP.mono (rowX_ok hs₃ hf (d := M.mo) (by rw [hl]; omega) (by
      rw [← hW, hl, hT₃, hmem₃, hm, hP]
      omega)) fun s₄ ⟨e₄, k₄⟩ => ?_
  rw [← hW, hl, hT₃, hmem₃, hm] at e₄
  -- The window's low word, which is zero.
  have hcons := wins_cons M.n i
  have ht0 : (regsVal s (wins M.n i)) % 2 ^ 64 = (s.gpr (win M.n i 0)).toNat := by
    rw [hcons, regsVal]; omega
  have h₄ : (regsVal s₄ (wins M.n i)) % 2 ^ 64 = (s₄.gpr (win M.n i 0)).toNat := by
    rw [hcons, regsVal]; omega
  have hlow : (s₄.gpr (win M.n i 0)).toNat = 0 := by
    have h := mont_low (s.gpr (win M.n i 0)).toNat M.minv.toNat m hinv
    rw [← u₃] at h
    omega
  have hrot : 2 ^ 64 * regsVal s₄ (wins M.n (i + 1)) = regsVal s₄ (wins M.n i) := by
    rw [wins_succ, regsVal_append, hcons, regsVal]
    simp only [regsVal, hlow, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  refine ⟨⟨(s₃.gpr .rdx).toNat, hu, by rw [hrot, e₄]⟩, ?_⟩
  rw [← hW] at k₄
  exact (k₃.mono (by sub_regs)).trans (k₄.mono (by sub_regs))

/-- Round `i` of the multiplication with BMI2 and ADX: `2⁶⁴ T' = T + a_i B + u m`,
and `T' < 2m` if `T < 2m`. -/
theorem roundX_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    (hn : M.n < 7) {a b i m : Nat} (ha : a + 8 * i + 8 ≤ size) (hb : b + 8 * M.n ≤ size)
    (hmo : M.mo + 8 * M.n ≤ size) (hm : wordsVal s.mem base M.mo M.n = m)
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) (hok : M.ok m = true)
    (hB : wordsVal s.mem base b M.n < m) (hT : regsVal s (wins M.n i) < 2 * m) :
    WP isa (.block (roundX M a b i)) s fun s' =>
      (∃ u, 2 ^ 64 * regsVal s' (wins M.n (i + 1)) = regsVal s (wins M.n i) +
        (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n + u * m) ∧
      regsVal s' (wins M.n (i + 1)) < 2 * m ∧
      Keeps (.rax :: .rcx :: .rdx :: .rbp :: wins M.n i) s s' := by
  have hW := wins_split M.n i
  have hf : Fresh ((List.range M.n).map (win M.n i) ++ [win M.n i M.n, win M.n i (M.n + 1)]) :=
    hW ▸ fresh_wins hn i
  have hl : ((List.range M.n).map (win M.n i)).length = M.n := by simp
  have hm' : m < 2 ^ (64 * M.n) := hm ▸ wordsVal_lt _ _ _ _
  have hA := (word s.mem base (a + 8 * i)).isLt
  have hAB : (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n ≤ (2 ^ 64 - 1) * m :=
    Nat.mul_le_mul (by omega) (by omega)
  have hP : 2 ^ (64 * (M.n + 2)) = 2 ^ 128 * 2 ^ (64 * M.n) := by
    rw [show 64 * (M.n + 2) = 128 + 64 * M.n by omega, Nat.pow_add]
  rw [roundX, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (movRdx_ok s (readSrc_sc hs ha)) fun s₁ ⟨d₁, _, _, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hT₁ : regsVal s₁ (wins M.n i) = regsVal s (wins M.n i) := regsVal_congr fun q hq =>
    k₁.1 q (by simpa using ((fresh_wins hn i).2 q hq).2.2.1)
  rw [rowX_wins]
  refine WP.mono (rowX_ok hs₁ hf (d := b) (by rw [hl]; omega) (by
      rw [← hW, hl, hT₁, d₁, k₁.2.1, hP]
      omega)) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [← hW, hl, hT₁, d₁, k₁.2.1] at e₂
  rw [← hW] at k₂
  have hs₂ := hs₁.of_keeps k₂ (by
    intro h
    simp only [List.mem_cons] at h
    rcases h with h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact (fresh_wins hn i).2 _ h |>.2.2.2.2 rfl)
  have hmem : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  have k₁₂ : Keeps (.rax :: .rcx :: .rdx :: .rbp :: wins M.n i) s s₂ :=
    (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))
  -- From `2⁶⁴ T' = T + a_i B + u m` for a word `u`.
  have fin : ∀ {s' : State} (u : Nat), u < 2 ^ 64 →
      2 ^ 64 * regsVal s' (wins M.n (i + 1)) = regsVal s₂ (wins M.n i) + u * m →
      (∃ u, 2 ^ 64 * regsVal s' (wins M.n (i + 1)) = regsVal s (wins M.n i) +
        (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n + u * m) ∧
      regsVal s' (wins M.n (i + 1)) < 2 * m := fun u hu e => by
    rw [e₂] at e
    have hum : u * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul (by omega) (Nat.le_refl _)
    refine ⟨⟨u, e⟩, Nat.lt_of_mul_lt_mul_left (a := 2 ^ 64) ?_⟩
    rw [e]; omega
  dsimp only
  split
  · rename_i hsp
    obtain ⟨hn6, hm6⟩ := Mod.ok_sparse hok hsp
    refine WP.mono (redSX_ok hn6 hm6 (by rw [e₂]; omega))
      fun s' ⟨⟨u, hu, eu⟩, k⟩ => ⟨(fin u hu eu).1, (fin u hu eu).2, k₁₂.trans k⟩
  have hred := Mod.ok_red hok
  split
  · refine WP.mono (redGenX_ok hs₂ hn hmo (by rw [hmem, hm]) hinv (by rw [e₂]; omega))
      fun s' ⟨⟨u, hu, eu⟩, k⟩ => ⟨(fin u hu eu).1, (fin u hu eu).2, k₁₂.trans k⟩
  · rename_i ws hf
    rw [hf] at hred
    have ht0 := (s₂.gpr (win M.n i 0)).isLt
    have hum : (s₂.gpr (win M.n i 0)).toNat * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul (by omega) (Nat.le_refl _)
    refine WP.mono (redF_ok true hn hred hm' (by rw [e₂]; omega)) fun s' ⟨e, k⟩ =>
      ⟨(fin _ ht0 e).1, (fin _ ht0 e).2, k₁₂.trans (k.mono (by sub_regs))⟩

/-- Round `i` of the multiplication, by `mul` or with BMI2 and ADX:
`2⁶⁴ T' = T + a_i B + u m`, and `T' < 2m` if `T < 2m`. -/
theorem round_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    (hn : M.n < 7) {a b i m : Nat} (ha : a + 8 * i + 8 ≤ size) (hb : b + 8 * M.n ≤ size)
    (hmo : M.mo + 8 * M.n ≤ size) (hm : wordsVal s.mem base M.mo M.n = m)
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) (hok : M.ok m = true)
    (hB : wordsVal s.mem base b M.n < m) (hT : regsVal s (wins M.n i) < 2 * m) :
    WP isa (.block (round M a b i)) s fun s' =>
      (∃ u, 2 ^ 64 * regsVal s' (wins M.n (i + 1)) = regsVal s (wins M.n i) +
        (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n + u * m) ∧
      regsVal s' (wins M.n (i + 1)) < 2 * m ∧
      Keeps (.rax :: .rcx :: .rdx :: .rbp :: wins M.n i) s s' := by
  unfold round; split
  · exact roundX_ok hs hn ha hb hmo hm hinv hok hB hT
  · exact roundM_ok hs hn ha hb hmo hm hinv hok hB hT

end VG.Proof.Mont.X86_64
