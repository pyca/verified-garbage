module

import VerifiedGarbage.Proof.Mont.PPC64LE.Loop
import VerifiedGarbage.Proof.Mont.PPC64LE.AddSub
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
public import VerifiedGarbage.Impl.Mont.PPC64LE
public import VerifiedGarbage.Proof.Mont.PPC64LE.Csub
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words

/-!
# Montgomery arithmetic on PPC64LE: the operations

`mul`, `add` and `sub` (`Impl/Mont/PPC64LE.lean`) on the numbers at `[r5]`
and `[r6]`, into `[r4]`, with the modulus `m` at `[r3 + M.mo]`, for a layout
of the working space (`OpLay`): `mul_ok`, `add_ok`, `sub_ok`.
-/

@[expose] public section

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Mont.PPC64LE VG.Proof.Mont

/-- What the operations need of the layout: the accumulator (`4n + 2`
digits at `acc`), the temporary area and the modulus, and the numbers at
`O`, `A` and `B` (`n` words each, apart from the others but possibly the
same as each other). -/
structure OpLay (M : Mod) (size acc O A B : Nat) : Prop where
  n0 : 0 < M.n
  acc_le : acc + 4 * (4 * M.n + 2) ≤ size
  tmp_le : M.tmp + 8 * M.n ≤ size
  mo_le : M.mo + 8 * M.n ≤ size
  o_le : O + 8 * M.n ≤ size
  a_le : A + 8 * M.n ≤ size
  b_le : B + 8 * M.n ≤ size
  acc4 : acc % 4 = 0
  tmp4 : M.tmp % 4 = 0
  sat : acc + 4 * (4 * M.n + 2) ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ acc
  am : acc + 4 * (4 * M.n + 2) ≤ M.mo ∨ M.mo + 8 * M.n ≤ acc
  ao : acc + 4 * (4 * M.n + 2) ≤ O ∨ O + 8 * M.n ≤ acc
  aa : acc + 4 * (4 * M.n + 2) ≤ A ∨ A + 8 * M.n ≤ acc
  ab : acc + 4 * (4 * M.n + 2) ≤ B ∨ B + 8 * M.n ≤ acc
  tm : M.tmp + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ M.tmp
  to : M.tmp + 8 * M.n ≤ O ∨ O + 8 * M.n ≤ M.tmp

/-- The ranges the operations write. -/
def opOuts (M : Mod) (acc O : Nat) : List (Nat × Nat) :=
  [(acc, 4 * (4 * M.n + 2)), (M.tmp, 8 * M.n), (O, 8 * M.n)]

/-- The registers the operations write. -/
def opClob : List Reg := [.r0, .r5, .r7, .r8, .r9, .r10, .r11, .r12]

/-! ## Clearing -/

theorem zeros_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {acc : Nat}
    (h3 : At s base .r3 0) : ∀ {k : Nat}, acc + 4 * k ≤ size →
    WP isa (.block ((List.range k).map fun j => .store .w .r11 wb (acc + 4 * j))) (s.write .r11 (BitVec.ofNat 64 0))
      fun u => Outside base acc (4 * k) s.mem u.mem ∧ (∀ j < k, w32 u.mem base (acc + 4 * j) = 0) ∧
        Kp [.r11] s u ∧ u.gpr .r11 = BitVec.ofNat 64 0
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      Kp.write s _ (by decide), by simp only [write_gpr, ite_true]⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    refine wp_append (WP.mono (zeros_ok hs h3 (k := k) (by omega)) fun s₁ ⟨O₁, Z₁, K₁, r₁⟩ => ?_)
    refine wp_step (stw0_ok (K₁.ws hs) (K₁.at h3) (by decide) (d := acc + 4 * k) (by omega)) (WP.block_nil ?_)
    have W := writeW32_outside s₁.mem base (d := acc + 4 * k) (BitVec.ofNat 32 (s₁.gpr .r11).toNat) (by omega)
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (W.mono (by omega) (by omega)), fun j hj => ?_,
      K₁.trans (Kp.store _ _ _), r₁⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · show w32 (s₁.mem.writeW _ _) base _ = 0
      rw [w32_write_ne hn (by omega) (by omega) (by omega)]; exact Z₁ j hj
    · show w32 (s₁.mem.writeW _ _) base _ = 0
      rw [w32_write_self, r₁]; rfl

/-! ## The operations -/

theorem OpLay.csub {M : Mod} {size acc O A B : Nat} (h : OpLay M size acc O A B) :
    CsubLay M size acc O := by
  obtain ⟨n0, acc_le, tmp_le, mo_le, o_le, a_le, b_le, acc4, tmp4, sat, am, ao, aa, ab, tm, to⟩ := h
  exact ⟨by omega, tmp_le, mo_le, o_le, acc4, tmp4, by omega, tm.symm, by omega, to⟩

theorem OpLay.csubHi {M : Mod} {size acc O A B : Nat} (h : OpLay M size acc O A B) :
    CsubLay M size (acc + 4 * (2 * M.n)) O := by
  obtain ⟨n0, acc_le, tmp_le, mo_le, o_le, a_le, b_le, acc4, tmp4, sat, am, ao, aa, ab, tm, to⟩ := h
  exact ⟨by omega, tmp_le, mo_le, o_le, by omega, tmp4, by omega, tm.symm, by omega, to⟩

/-- What the operations start from: the working space, the pointers, and the
modulus `m` at `[r3 + M.mo]`. -/
structure OpPre (M : Mod) (base : Addr) (size O A B m : Nat) (s : State) : Prop where
  ws : Ws s base size
  r3 : At s base .r3 0
  r4 : At s base .r4 O
  r5 : At s base .r5 A
  r6 : At s base .r6 B
  mo : val32 s.mem base M.mo (2 * M.n) = m
  m0 : 0 < m

theorem outs_of {base : Addr} {M : Mod} {acc O : Nat} {rs : List (Nat × Nat)} {m m' : Mem}
    (h : Outs base rs m m') (hs : ∀ r ∈ rs, r ∈ opOuts M acc O := by decide) : Outs base (opOuts M acc O) m m' :=
  h.mono hs

theorem outs_tail {base : Addr} {M : Mod} {acc O : Nat} {m m' : Mem}
    (h : Outs base [(M.tmp, 8 * M.n), (O, 8 * M.n)] m m') : Outs base (opOuts M acc O) m m' :=
  h.mono fun r hr => by
    simp only [opOuts, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp

/-- `[r4] = ([r5] + [r6]) mod m`, for a sum below `2m`. -/
theorem add_ok {M : Mod} {base : Addr} {size acc O A B m : Nat} {s : State} (hp : OpPre M base size O A B m s)
    (hL : OpLay M size acc O A B)
    (hab : wordsVal s.mem base A M.n + wordsVal s.mem base B M.n < 2 * m) :
    WP isa (.block (add M acc)) s fun u =>
      wordsVal u.mem base O M.n = (wordsVal s.mem base A M.n + wordsVal s.mem base B M.n) % m ∧
      Outs base (opOuts M acc O) s.mem u.mem ∧ Kp opClob s u := by
  have hn := hp.ws.nowrap
  have hL' := hL
  obtain ⟨n0, acc_le, tmp_le, mo_le, o_le, a_le, b_le, acc4, tmp4, sat, am, ao, aa, ab, tm, to⟩ := hL'
  have ec : add M acc = .li .r10 0 :: (adds acc (2 * M.n) ++
      (.store .w .r10 wb (acc + 4 * (2 * M.n)) :: csub M acc)) := by
    simp only [add, digits, adds, List.append_assoc, List.cons_append, List.nil_append]
  rw [ec]
  refine wp_step (exec_li (by decide)) ?_
  refine wp_append (WP.mono (adds_ok (W := 2 * M.n) (hp.ws.write _ _) (hp.r3.write _) (hp.r5.write _)
    (hp.r6.write _) (by simp only [write_gpr, ite_true]; decide) (by omega) (by omega) (by omega) (by omega)
    (by omega) (k := 2 * M.n) (Nat.le_refl _)) fun s₂ ⟨O₂, V₂, C₂, K₂⟩ => ?_)
  simp only [write_mem, write_gpr, ite_true] at O₂ V₂
  have K₀₂ : Kp [.r10, .r11, .r12] s s₂ := (Kp.write s _ (by decide)).trans K₂
  refine wp_step (stw0_ok (K₀₂.ws hp.ws) (K₀₂.at hp.r3) (by decide) (d := acc + 4 * (2 * M.n)) (by omega)) ?_
  have W := writeW32_outside s₂.mem base (d := acc + 4 * (2 * M.n)) (BitVec.ofNat 32 (s₂.gpr .r10).toNat) (by omega)
  have hsum : val32 (s₂.mem.writeW (off base (acc + 4 * (2 * M.n))) (BitVec.ofNat 32 (s₂.gpr .r10).toNat))
      base acc (2 * M.n + 1) = wordsVal s.mem base A M.n + wordsVal s.mem base B M.n := by
    rw [val32_succ, W.val32 (by omega) (by omega), w32_write_self, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), wordsVal_eq_val32, wordsVal_eq_val32]
    rw [show (BitVec.ofNat 64 0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at V₂
    exact V₂
  have hmo : val32 (s₂.mem.writeW (off base (acc + 4 * (2 * M.n))) (BitVec.ofNat 32 (s₂.gpr .r10).toNat))
      base M.mo (2 * M.n) = m := by
    rw [W.val32 (by omega) (by omega), O₂.val32 (by omega) (by omega), hp.mo]
  refine WP.mono (csub_ok (((K₀₂.ws hp.ws).store _)) ((K₀₂.at hp.r3).store _) ((K₀₂.at hp.r4).store _)
    hL.csub hmo (by rw [hsum]; exact hab)) fun u ⟨V₃, O₃, K₃⟩ => ⟨?_, ?_, ?_⟩
  · rw [V₃, hsum]
  · exact ((Outs.of_outside (O₂.mono (Nat.le_refl _) (by omega)) (List.mem_cons_self ..)).trans
      (Outs.of_outside (W.mono (by omega) (by omega)) (List.mem_cons_self ..))).trans (outs_tail O₃)
  · exact ((K₀₂.mono (by decide)).trans ((Kp.store _ _ _).trans K₃)).mono (by decide)

/-- `[r4] = ([r5] + m - [r6]) mod m`, for numbers below `m`. -/
theorem sub_ok {M : Mod} {base : Addr} {size acc O A B m : Nat} {s : State} (hp : OpPre M base size O A B m s)
    (hL : OpLay M size acc O A B) (ha : wordsVal s.mem base A M.n < m) (hb : wordsVal s.mem base B M.n < m) :
    WP isa (.block (sub M acc)) s fun u =>
      wordsVal u.mem base O M.n = (wordsVal s.mem base A M.n + m - wordsVal s.mem base B M.n) % m ∧
      Outs base (opOuts M acc O) s.mem u.mem ∧ Kp opClob s u := by
  have hn := hp.ws.nowrap
  have hL' := hL
  obtain ⟨n0, acc_le, tmp_le, mo_le, o_le, a_le, b_le, acc4, tmp4, sat, am, ao, aa, ab, tm, to⟩ := hL'
  have ec : sub M acc = mask32 ++ (.li .r10 1 :: (subs M acc (2 * M.n) ++
      (.subi .r10 .r10 1 :: .store .w .r10 wb (acc + 4 * (2 * M.n)) :: csub M acc))) := by
    simp only [sub, digits, subs, List.append_assoc, List.cons_append, List.nil_append]
  rw [ec]
  refine mask32_ok ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_append (WP.mono (subs_ok (W := 2 * M.n) (M := M) ((hp.ws.write _ _).write _ _)
    ((hp.r3.write _).write _) ((hp.r5.write _).write _) ((hp.r6.write _).write _)
    (by simp only [write_gpr, reduceCtorEq, ite_false, ite_true]) (by simp only [write_gpr, ite_true]; rfl)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (k := 2 * M.n) (Nat.le_refl _)) fun s₂ ⟨O₂, V₂, C₂, K₂⟩ => ?_)
  simp only [write_mem] at O₂ V₂
  have K₀₂ : Kp [.r0, .r10, .r11, .r12] s s₂ :=
    ((Kp.write s _ (by decide)).trans (Kp.write _ _ (by decide))).trans (K₂.mono (by decide))
  rw [hp.mo] at V₂
  have eA := wordsVal_eq_val32 s.mem base A M.n
  have eB := wordsVal_eq_val32 s.mem base B M.n
  have hc1 : 1 ≤ (s₂.gpr .r10).toNat := by
    have := val32_lt s₂.mem base acc (2 * M.n)
    have := val32_lt s.mem base A (2 * M.n)
    have := val32_lt s.mem base B (2 * M.n)
    by_contra h
    rw [show (s₂.gpr .r10).toNat = 0 by omega, Nat.mul_zero, Nat.add_zero] at V₂
    omega
  refine wp_step (exec_subi (by decide) (by decide)) ?_
  have hsub : ((s₂.gpr .r10 - BitVec.ofNat 64 1)).toNat = (s₂.gpr .r10).toNat - 1 := by
    rw [BitVec.toNat_sub, toNat_ofNat_lt (by decide)]; omega
  refine wp_step (stw0_ok ((K₀₂.ws hp.ws).write _ _) ((K₀₂.at hp.r3).write _) (by decide)
    (d := acc + 4 * (2 * M.n)) (by omega)) ?_
  simp only [write_gpr, ite_true]
  rw [hsub]
  have W := writeW32_outside s₂.mem base (d := acc + 4 * (2 * M.n)) (BitVec.ofNat 32 ((s₂.gpr .r10).toNat - 1))
    (by omega)
  have hdiff : val32 (s₂.mem.writeW (off base (acc + 4 * (2 * M.n))) (BitVec.ofNat 32 ((s₂.gpr .r10).toNat - 1)))
      base acc (2 * M.n + 1) = wordsVal s.mem base A M.n + m - wordsVal s.mem base B M.n := by
    rw [val32_succ, W.val32 (by omega) (by omega), w32_write_self, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    have : 2 ^ (32 * (2 * M.n)) * ((s₂.gpr .r10).toNat - 1) + 2 ^ (32 * (2 * M.n)) =
        2 ^ (32 * (2 * M.n)) * (s₂.gpr .r10).toNat := by
      rw [Nat.mul_sub_one]
      have : 2 ^ (32 * (2 * M.n)) ≤ 2 ^ (32 * (2 * M.n)) * (s₂.gpr .r10).toNat := Nat.le_mul_of_pos_right _ hc1
      omega
    omega
  have hmo : val32 (s₂.mem.writeW (off base (acc + 4 * (2 * M.n))) (BitVec.ofNat 32 ((s₂.gpr .r10).toNat - 1)))
      base M.mo (2 * M.n) = m := by
    rw [W.val32 (by omega) (by omega), O₂.val32 (by omega) (by omega), hp.mo]
  refine WP.mono (csub_ok ((((K₀₂.ws hp.ws).write _ _).store _)) (((K₀₂.at hp.r3).write _).store _)
    (((K₀₂.at hp.r4).write _).store _) hL.csub hmo (by dsimp only [write_mem]; rw [hdiff]; omega)) fun u ⟨V₃, O₃, K₃⟩ => ⟨?_, ?_, ?_⟩
  · rw [V₃]; dsimp only [write_mem]; rw [hdiff]
  · exact ((Outs.of_outside (O₂.mono (Nat.le_refl _) (by omega)) (List.mem_cons_self ..)).trans
      (Outs.of_outside (W.mono (by omega) (by omega)) (List.mem_cons_self ..))).trans (outs_tail O₃)
  · exact (K₀₂.trans (((Kp.write _ _ (by decide)).trans (Kp.store _ _ _)).trans K₃)).mono (by decide)

theorem val32_zeros {m : Mem} {base : Addr} {d : Nat} :
    ∀ {k : Nat}, (∀ j < k, w32 m base (d + 4 * j) = 0) → val32 m base d k = 0
  | 0, _ => rfl
  | k + 1, h => by
    rw [val32_succ, val32_zeros fun j hj => h j (by omega), h k (by omega), Nat.mul_zero]

/-- `[r4] = [r5] [r6] R⁻¹ mod m`, for `[r6]` below `m`. -/
theorem mul_ok {M : Mod} {base : Addr} {size acc O A B m : Nat} {s : State} (hp : OpPre M base size O A B m s)
    (hL : OpLay M size acc O A B) (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0)
    (hb : wordsVal s.mem base B M.n < m) :
    WP isa (mul M acc) s fun u =>
      wordsVal u.mem base O M.n < m ∧
      wordsVal u.mem base O M.n * 2 ^ (64 * M.n) % m = wordsVal s.mem base A M.n * wordsVal s.mem base B M.n % m ∧
      Outs base (opOuts M acc O) s.mem u.mem ∧ Kp opClob s u := by
  have hn := hp.ws.nowrap
  have hs15 := hp.ws.small
  have hL' := hL
  obtain ⟨n0, acc_le, tmp_le, mo_le, o_le, a_le, b_le, acc4, tmp4, sat, am, ao, aa, ab, tm, to⟩ := hL'
  have hD : digits M = 2 * M.n := rfl
  have hML : MulLay (2 * M.n) size acc A B M.mo :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have eB := wordsVal_eq_val32 s.mem base B M.n
  have eA := wordsVal_eq_val32 s.mem base A M.n
  refine WP.seq ?_
  simp only [zeros, hD, List.cons_append]
  refine wp_step (exec_li (by decide)) ?_
  refine wp_append (WP.mono (zeros_ok hp.ws hp.r3 (acc := acc) (k := 2 * (2 * M.n) + 2) (by omega))
    fun s₁ ⟨O₁, Z₁, K₁, _⟩ => ?_)
  refine wp_step (exec_addi (by decide) (by omega)) ?_
  refine wp_step (exec_li (by omega)) (WP.block_nil ?_)
  -- The invariant at digit 0.
  have h0 : LoopInv base (2 * M.n) acc A B m 0 s
      ((s₁.write .r7 (s₁.gpr .r3 + BitVec.ofNat 64 acc)).write .r8 (BitVec.ofNat 64 (2 * M.n))) := by
    refine ⟨((K₁.at hp.r3).write _).write _, ?_, ((K₁.at hp.r6).write _).write _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [At, write_gpr, reduceCtorEq, ite_false, Nat.mul_zero, Nat.add_zero]; rw [K₁.g]; exact hp.r5
    · simp only [At, write_gpr, reduceCtorEq, ite_false, ite_true, Nat.mul_zero, Nat.add_zero]
      rw [K₁.g, hp.r3, off_add, Nat.zero_add]
    · simp only [write_gpr, ite_true, Nat.sub_zero]
    · simp only [write_mem]; exact O₁.mono (Nat.le_refl _) (by omega)
    · exact ((K₁.mono (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))
    · intro l _ hl; simp only [write_mem]; exact Z₁ l (by omega)
    · simp only [write_mem, Nat.mul_zero, Nat.add_zero]
      rw [val32_zeros fun j hj => Z₁ j (by omega)]; have := hp.m0; omega
    · refine ⟨0, ?_⟩
      simp only [write_mem, Nat.mul_zero, Nat.add_zero]
      rw [val32_zeros fun j hj => Z₁ j (by omega)]; simp [val32]
  have hmo₀ : val32 s.mem base M.mo (2 * M.n) = m := hp.mo
  refine WP.seq (WP.mono (loop_ok hp.ws hD hML (by omega) hmo₀ (minv32_inv hinv) (by omega) h0) fun t I => ?_)
  -- The reduction.
  obtain ⟨U, hU⟩ := I.cong
  have hT := I.lt
  generalize hTv : val32 t.mem base (acc + 4 * (2 * M.n)) (2 * M.n + 2) = T at hT hU
  have hlo : val32 t.mem base (acc + 4 * (2 * M.n)) (2 * M.n + 1) = T := by
    have e := val32_succ t.mem base (acc + 4 * (2 * M.n)) (2 * M.n + 1)
    rw [hTv] at e
    have hm0 : m < 2 ^ (32 * (2 * M.n)) := by rw [← hp.mo]; exact val32_lt _ _ _ _
    have hP : 2 ^ (32 * (2 * M.n)) * 2 ≤ 2 ^ (32 * (2 * M.n + 1)) := by
      rw [show 32 * (2 * M.n + 1) = 32 * (2 * M.n) + 32 by omega, Nat.pow_add]
      exact Nat.mul_le_mul_left _ (by decide)
    by_contra hne
    have : 1 ≤ w32 t.mem base (acc + 4 * (2 * M.n) + 4 * (2 * M.n + 1)) := by
      rcases Nat.eq_zero_or_pos (w32 t.mem base (acc + 4 * (2 * M.n) + 4 * (2 * M.n + 1))) with h | h
      · rw [h, Nat.mul_zero, Nat.add_zero] at e; exact absurd e.symm hne
      · exact h
    have : 2 ^ (32 * (2 * M.n + 1)) ≤ 2 ^ (32 * (2 * M.n + 1)) * w32 t.mem base (acc + 4 * (2 * M.n) +
      4 * (2 * M.n + 1)) := Nat.le_mul_of_pos_right _ this
    omega
  have hmo : val32 t.mem base M.mo (2 * M.n) = m := by rw [I.out.val32 (by omega) (by omega), hp.mo]
  refine WP.mono (csub_ok (I.kp.ws hp.ws) I.r3 (by rw [At, kp_clob I.kp]; exact hp.r4) hL.csubHi hmo
    (by rw [hlo]; exact hT)) fun u ⟨V₃, O₃, K₃⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [V₃]; exact Nat.mod_lt _ hp.m0
  · rw [V₃, hlo, Nat.mod_mul_mod, show 64 * M.n = 32 * (2 * M.n) by omega, Nat.mul_comm, hU, ← eA, ← eB,
      Nat.add_mul_mod_self_right]
  · exact (Outs.of_outside (I.out.mono (Nat.le_refl _) (by omega)) (List.mem_cons_self ..)).trans (outs_tail O₃)
  · exact (I.kp.trans (K₃.mono (by decide))).mono (by decide)

end VG.Proof.Mont.PPC64LE
