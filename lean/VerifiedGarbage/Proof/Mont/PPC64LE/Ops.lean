module

import VerifiedGarbage.Proof.Mont.PPC64LE.Loop
import VerifiedGarbage.Proof.Mont.PPC64LE.AddSub
import VerifiedGarbage.Proof.Mont.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Mont.PPC64LE.Const
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

/-! ## Clearing, and the modulus's pointer -/

theorem zeros_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {acc : Nat}
    (h3 : At s base .r3 0) (hacc4 : acc % 4 = 0) : ∀ {k : Nat}, acc + 8 * k ≤ size →
    WP isa (.block ((List.range k).map fun j => .store .d .r11 wb (acc + 8 * j))) (s.write .r11 (BitVec.ofNat 64 0))
      fun u => Outside base acc (8 * k) s.mem u.mem ∧ (∀ j < k, word u.mem base (acc + 8 * j) = 0) ∧
        Kp [.r11] s u ∧ u.gpr .r11 = BitVec.ofNat 64 0
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      Kp.write s _ (by decide), by simp only [write_gpr, ite_true]⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    have hs15 := hs.small
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    refine wp_append (WP.mono (zeros_ok hs h3 hacc4 (k := k) (by omega_arith)) fun s₁ ⟨O₁, Z₁, K₁, r₁⟩ => ?_)
    refine wp_step (std_ok (K₁.ws hs) (K₁.at h3) (by decide) (by omega) (d := acc + 8 * k) (by omega_arith))
      (WP.block_nil ?_)
    rw [Nat.zero_add]
    have W := writeW_outside s₁.mem base (d := acc + 8 * k) (s₁.gpr .r11) (by omega_arith)
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega_arith)).trans (W.mono (by omega_arith) (by omega_arith)), fun j hj => ?_,
      K₁.trans (Kp.store _ _ _), r₁⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · show word (s₁.mem.writeW _ _) base _ = 0
      rw [word_writeW_ne _ (by omega_arith) (by omega_arith) (by omega_arith)]; exact Z₁ j hj
    · show word (s₁.mem.writeW _ _) base _ = 0
      rw [word_writeW_self, r₁]; rfl

theorem wordsVal_zeros {m : Mem} {base : Addr} {d : Nat} :
    ∀ {k : Nat}, (∀ j < k, word m base (d + 8 * j) = 0) → wordsVal m base d k = 0
  | 0, _ => rfl
  | k + 1, h => by
    rw [wordsVal_succ_top, wordsVal_zeros fun j hj => h j (by omega_arith), h k (by omega_arith)]; rfl

theorem setMo_ok {s : State} {base : Addr} {M : Mod} (h3 : At s base .r3 0) (hmo : M.mo < 2 ^ 15) :
    exec (setMo M) s = some (s.write .r7 (off base M.mo)) := by
  rw [setMo, exec_addi (by decide) hmo, h3, off_add, Nat.zero_add]

/-! ## The operations -/

theorem OpLay.csub {M : Mod} {size acc O A B : Nat} (h : OpLay M size acc O A B) :
    CsubLay M size acc O := by
  obtain ⟨n0, acc_le, tmp_le, mo_le, o_le, a_le, b_le, acc4, tmp4, sat, am, ao, aa, ab, tm, to⟩ := h
  exact ⟨by omega_arith, tmp_le, mo_le, o_le, acc4, tmp4, by omega_arith, tm.symm, by omega_arith, to⟩

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
  have hs15 := hp.ws.small
  have hL' := hL
  obtain ⟨n0, acc_le, tmp_le, mo_le, o_le, a_le, b_le, acc4, tmp4, sat, am, ao, aa, ab, tm, to⟩ := hL'
  have ec : add M acc = setMo M :: (chain false .r5 0 .r6 0 acc M.n ++
      ([.li .r10 0, .addze .r10 .r10, .store .d .r10 wb (acc + 8 * M.n)] ++ csub M acc)) := by
    simp only [add, List.append_assoc, List.cons_append]
  rw [ec]
  refine wp_step (setMo_ok hp.r3 (by omega_arith)) ?_
  have hs₁ := hp.ws.write .r7 (off base M.mo)
  refine wp_append (WP.mono (chain_ok (sub := false) (W := M.n) hs₁ (hp.r5.write _) (hp.r6.write _) (hp.r3.write _)
    (by decide) (by decide) (by decide) (by decide) acc4 (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (k := M.n) (Nat.le_refl _)) fun s₂ ⟨O₂, V₂, K₂⟩ => ?_)
  simp only [write_mem, ite_false, Bool.false_eq_true, Nat.add_zero, Bool.toNat_false] at O₂ V₂
  rw [show cOf false M.n s₂.ca = s₂.ca.toNat by simp only [cOf]; split <;> omega_arith] at V₂
  have K₀₂ : Kp [.r7, .r11, .r12] s s₂ := (Kp.write s _ (by decide)).trans (K₂.mono (by decide))
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_addze ?_
  refine wp_step (std_ok (((K₀₂.ws hp.ws).write _ _).writeCarry _ _) (((K₀₂.at hp.r3).write _).writeCarry _)
    (by decide) (by omega_arith) (d := acc + 8 * M.n) (by omega_arith)) ?_
  simp only [write_gpr, writeCarry_gpr, ite_true, RegUpd.mem_writeCarry, write_mem, RegUpd.ca_write]
  rw [show (BitVec.ofNat 64 0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add, Nat.zero_add]
  have W := writeW_outside s₂.mem base (d := acc + 8 * M.n) (BitVec.ofNat 64 s₂.ca.toNat) (by omega_arith)
  have hsum : wordsVal (s₂.mem.writeW (off base (acc + 8 * M.n)) (BitVec.ofNat 64 s₂.ca.toNat)) base acc (M.n + 1) =
      wordsVal s.mem base A M.n + wordsVal s.mem base B M.n := by
    rw [wordsVal_succ_top, W.wordsVal (by omega_arith) (by omega_arith), word_writeW_self,
      toNat_ofNat_lt (by have := Bool.toNat_le s₂.ca; omega_arith)]
    exact V₂
  have hmo : wordsVal (s₂.mem.writeW (off base (acc + 8 * M.n)) (BitVec.ofNat 64 s₂.ca.toNat)) base M.mo M.n = m := by
    rw [W.wordsVal (by omega_arith) (by omega_arith), O₂.wordsVal (by omega_arith) (by omega_arith),
      wordsVal_eq_val32, hp.mo]
  refine WP.mono (csub_ok ((((K₀₂.ws hp.ws).write _ _).writeCarry _ _).store _)
    ((((K₀₂.at hp.r3).write _).writeCarry _).store _) ((((K₀₂.at hp.r4).write _).writeCarry _).store _)
    ((((by rw [At, K₂.g]; rfl : At s₂ base .r7 M.mo).write _).writeCarry _).store _) hL.csub n0 hmo
    (by rw [hsum]; exact hab)) fun u ⟨V₃, O₃, K₃⟩ => ⟨?_, ?_, ?_⟩
  · rw [V₃, hsum]
  · exact ((Outs.of_outside (O₂.mono (Nat.le_refl _) (by omega_arith)) (List.mem_cons_self ..)).trans
      (Outs.of_outside (W.mono (by omega_arith) (by omega_arith)) (List.mem_cons_self ..))).trans (outs_tail O₃)
  · refine (K₀₂.mono (rs' := opClob) (by decide)).trans (Kp.trans ?_ (K₃.mono (by decide)))
    exact ((Kp.write _ _ (by decide)).trans (Kp.writeCarry _ _ (by decide))).trans (Kp.store _ _ _)

/-- What `sub` computes: `D = A - B + R (1 - c)`, then `E = D + m` (mod `R`),
and the borrow selects. -/
theorem sub_math {A B m D E R c c' : Nat} (hA : A < m) (hB : B < m) (hD : D < R) (hE : E < R)
    (h1 : D + R * c + B = A + R) (h2 : E + R * c' = D + m) (hc : c ≤ 1) (hc' : c' ≤ 1) :
    (if c = 1 then D else E) = (A + m - B) % m := by
  obtain rfl | rfl : c = 0 ∨ c = 1 := by omega_arith
  · obtain rfl | rfl : c' = 0 ∨ c' = 1 := by omega_arith
    · simp only [Nat.mul_zero, Nat.add_zero] at h1 h2; omega_arith
    · simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at h1 h2
      simp only [Nat.zero_ne_one, ite_false]
      rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · simp only [Nat.mul_one, ite_true] at h1 ⊢
    rw [show A + m - B = (A - B) + m by omega_arith, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith

theorem mask_ca (c : Bool) :
    BitVec.ofNat 64 (2 ^ 64 - 1 + c.toNat) = (if c.toNat = 1 then 0 else BitVec.allOnes 64) := by
  cases c <;> decide

/-- `[r4] = ([r5] + m - [r6]) mod m`, for numbers below `m`. -/
theorem sub_ok {M : Mod} {base : Addr} {size acc O A B m : Nat} {s : State} (hp : OpPre M base size O A B m s)
    (hL : OpLay M size acc O A B) (ha : wordsVal s.mem base A M.n < m) (hb : wordsVal s.mem base B M.n < m) :
    WP isa (.block (sub M acc)) s fun u =>
      wordsVal u.mem base O M.n = (wordsVal s.mem base A M.n + m - wordsVal s.mem base B M.n) % m ∧
      Outs base (opOuts M acc O) s.mem u.mem ∧ Kp opClob s u := by
  have hn := hp.ws.nowrap
  have hs15 := hp.ws.small
  have hL' := hL
  obtain ⟨n0, acc_le, tmp_le, mo_le, o_le, a_le, b_le, acc4, tmp4, sat, am, ao, aa, ab, tm, to⟩ := hL'
  have ec : sub M acc = setMo M :: (chain true .r5 0 .r6 0 acc M.n ++ (.sube .r10 .r10 .r10 ::
      (chain false wb acc .r7 0 M.tmp M.n ++ sels M acc M.n))) := by
    simp only [sub, List.append_assoc, List.cons_append, List.nil_append]
  rw [ec]
  refine wp_step (setMo_ok hp.r3 (by omega_arith)) ?_
  have hs₁ := hp.ws.write .r7 (off base M.mo)
  refine wp_append (WP.mono (chain_ok (sub := true) (W := M.n) hs₁ (hp.r5.write _) (hp.r6.write _) (hp.r3.write _)
    (by decide) (by decide) (by decide) (by decide) acc4 (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (k := M.n) (Nat.le_refl _)) fun s₂ ⟨O₂, V₂, K₂⟩ => ?_)
  simp only [write_mem, ite_true, Bool.toNat_true, Nat.add_zero] at O₂ V₂
  rw [show cOf true M.n s₂.ca = s₂.ca.toNat by simp only [cOf]; split <;> omega_arith] at V₂
  replace V₂ : wordsVal s₂.mem base acc M.n + 2 ^ (64 * M.n) * s₂.ca.toNat + wordsVal s.mem base B M.n =
      wordsVal s.mem base A M.n + 2 ^ (64 * M.n) := by
    have := Nat.one_le_two_pow (n := 64 * M.n)
    generalize 2 ^ (64 * M.n) = P at *
    omega_arith
  have K₀₂ : Kp [.r7, .r11, .r12] s s₂ := (Kp.write s _ (by decide)).trans (K₂.mono (by decide))
  have h7₂ : At s₂ base .r7 M.mo := by rw [At, K₂.g]; rfl
  refine wp_step exec_sube ?_
  have hmk : (s₂.writeCarry .r10 ((s₂.gpr .r10).toNat + (2 ^ 64 - 1 - (s₂.gpr .r10).toNat) + s₂.ca.toNat)).gpr .r10 =
      if s₂.ca.toNat = 1 then 0 else BitVec.allOnes 64 := by
    rw [RegUpd.gpr_writeCarry_self, ← mask_ca]
    congr 2
    have := (s₂.gpr .r10).isLt
    omega_arith
  generalize hc : s₂.ca.toNat = c at V₂ hmk
  have hc1 : c ≤ 1 := hc ▸ Bool.toNat_le _
  refine wp_append (WP.mono (chain_ok (sub := false) (W := M.n) ((K₀₂.ws hp.ws).writeCarry _ _)
    ((K₀₂.at hp.r3).writeCarry _) (h7₂.writeCarry _) ((K₀₂.at hp.r3).writeCarry _)
    (by decide) (by decide) acc4 (by decide) tmp4 (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (k := M.n) (Nat.le_refl _)) fun s₃ ⟨O₃, V₃, K₃⟩ => ?_)
  simp only [RegUpd.mem_writeCarry, ite_false, Bool.false_eq_true, Nat.add_zero, Bool.toNat_false,
    Nat.zero_add] at O₃ V₃
  rw [show cOf false M.n s₃.ca = s₃.ca.toNat by simp only [cOf]; split <;> omega_arith] at V₃
  have hmo : wordsVal s₂.mem base M.mo M.n = m := by
    rw [O₂.wordsVal (by omega_arith) (by omega_arith), wordsVal_eq_val32, hp.mo]
  rw [hmo] at V₃
  have hmk₃ : s₃.gpr .r10 = if c = 1 then 0 else BitVec.allOnes 64 := by rw [K₃.g]; exact hmk
  refine WP.mono (sels_ok (W := M.n) (K₃.ws ((K₀₂.ws hp.ws).writeCarry _ _)) (K₃.at ((K₀₂.at hp.r3).writeCarry _))
    (K₃.at ((K₀₂.at hp.r4).writeCarry _)) acc4 tmp4 (by rw [hmk₃]; split <;> simp)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (k := M.n) (Nat.le_refl _))
    fun u ⟨O₄, V₄, K₄⟩ => ⟨?_, ?_, ?_⟩
  · have hD₃ : wordsVal s₃.mem base acc M.n = wordsVal s₂.mem base acc M.n :=
      O₃.wordsVal (by omega_arith) (by omega_arith)
    rw [V₄, hmk₃, hD₃, ← sub_math ha hb (wordsVal_lt _ _ _ _)
      (wordsVal_lt s₃.mem base M.tmp M.n) V₂ V₃ hc1 (Bool.toNat_le _)]
    by_cases h : c = 1
    · simp [h]
    · have : BitVec.allOnes 64 ≠ 0 := by decide
      simp only [h, ite_false, this]
  · have o₂ : Outs base (opOuts M acc O) s.mem s₂.mem :=
      Outs.of_outside (O₂.mono (Nat.le_refl _) (by omega_arith)) (List.mem_cons_self ..)
    have o₃ : Outs base (opOuts M acc O) s₂.mem s₃.mem := Outs.of_outside O₃ (by simp [opOuts])
    have o₄ : Outs base (opOuts M acc O) s₃.mem u.mem := Outs.of_outside O₄ (by simp [opOuts])
    exact (o₂.trans o₃).trans o₄
  · have k₂ : Kp opClob s s₂ := K₀₂.mono (by decide)
    have k₃ : Kp opClob s₂ s₃ := (Kp.writeCarry _ _ (by decide)).trans (K₃.mono (by decide))
    exact (k₂.trans k₃).trans (K₄.mono (by decide))

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
  have hML : MulLay M size acc A B :=
    ⟨n0, by omega_arith, a_le, b_le, mo_le, acc4, by omega_arith, by omega_arith, by omega_arith⟩
  have hmi4 : (acc + 8 * (M.n + 1)) % 4 = 0 := by omega_arith
  refine WP.seq ?_
  simp only [zeros, List.append_assoc, List.cons_append]
  -- `m'` above the accumulator.
  refine wp_append (WP.mono (setConst_ok hp.ws hp.r3 (n := 1) (o := acc + 8 * (M.n + 1)) (x := M.minv.toNat)
    (by omega_arith) M.minv.isLt) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  refine wp_step (exec_li (by decide)) ?_
  refine wp_append (WP.mono (zeros_ok (K₁.ws hp.ws) (K₁.at hp.r3) acc4 (acc := acc) (k := M.n + 1) (by omega_arith))
    fun s₂ ⟨O₂, Z₂, K₂, _⟩ => ?_)
  refine wp_step (setMo_ok ((K₁.trans K₂).at hp.r3) (by omega_arith)) ?_
  refine wp_step (exec_li (by omega_arith)) (WP.block_nil ?_)
  generalize hu : (s₂.write .r7 (off base M.mo)).write .r8 (BitVec.ofNat 64 M.n) = u
  have hum : u.mem = s₂.mem := by rw [← hu]; rfl
  have K₀u : Kp [.r7, .r8, .r11] s u := by
    rw [← hu]
    exact ((K₁.trans K₂).mono (by decide)).trans ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide)))
  have Ous : Outs base (opOuts M acc O) s.mem u.mem := by
    rw [hum]
    have o₁ : Outs base (opOuts M acc O) s.mem s₁.mem :=
      Outs.of_outside (O₁.mono (o' := acc) (n' := 4 * (4 * M.n + 2)) (by omega_arith) (by omega_arith))
        (List.mem_cons_self ..)
    have o₂ : Outs base (opOuts M acc O) s₁.mem s₂.mem :=
      Outs.of_outside (O₂.mono (o' := acc) (n' := 4 * (4 * M.n + 2)) (Nat.le_refl _) (by omega_arith))
        (List.mem_cons_self ..)
    exact o₁.trans o₂
  have hmi : (word u.mem base (acc + 8 * (M.n + 1))).toNat = M.minv.toNat := by
    rw [hum, O₂.word (by omega_arith) (by omega_arith), ← V₁, ← wordsVal_eq_val32]
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero]
  have hmu : wordsVal u.mem base M.mo M.n = m := by
    rw [hum, O₂.wordsVal (by omega_arith) (by omega_arith), O₁.wordsVal (by omega_arith) (by omega_arith),
      wordsVal_eq_val32, hp.mo]
  have hAu : wordsVal u.mem base A M.n = wordsVal s.mem base A M.n := by
    rw [hum, O₂.wordsVal (by omega_arith) (by omega_arith), O₁.wordsVal (by omega_arith) (by omega_arith)]
  have hBu : wordsVal u.mem base B M.n = wordsVal s.mem base B M.n := by
    rw [hum, O₂.wordsVal (by omega_arith) (by omega_arith), O₁.wordsVal (by omega_arith) (by omega_arith)]
  have hws : Ws u base size := K₀u.ws hp.ws
  -- The invariant at word 0.
  have h0 : LoopInv base M acc A B m 0 u u := by
    refine ⟨K₀u.at hp.r3, ?_, K₀u.at hp.r6, ?_, ?_, Outside.refl _ _ _ _, Kp.refl _ _, ?_, ?_⟩
    · rw [Nat.mul_zero, Nat.add_zero]; exact K₀u.at hp.r5
    · rw [At, ← hu]; simp only [write_gpr, reduceCtorEq, ite_false, ite_true]
    · rw [← hu]; simp only [write_gpr, ite_true, Nat.sub_zero]
    · rw [hum, wordsVal_zeros fun j hj => Z₂ j hj]; have := hp.m0; omega_arith
    · exact ⟨0, by rw [hum, wordsVal_zeros fun j hj => Z₂ j hj]; simp [wordsVal]⟩
  refine WP.seq (WP.mono (loop_ok hws hML hmu (by rw [hmi]; exact hinv) (by rw [hBu]; exact hb) h0) fun t I => ?_)
  -- The reduction.
  obtain ⟨U, hU⟩ := I.cong
  have hmt : wordsVal t.mem base M.mo M.n = m := by rw [I.out.wordsVal (by omega_arith) (by omega_arith), hmu]
  refine WP.mono (csub_ok (I.kp.ws hws) I.r3 (by rw [At, kp_clob I.kp]; exact K₀u.at hp.r4) I.r7 hL.csub n0 hmt
    I.lt) fun v ⟨V₃, O₃, K₃⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [V₃]; exact Nat.mod_lt _ hp.m0
  · rw [V₃, Nat.mod_mul_mod, Nat.mul_comm, hU, hAu, hBu, Nat.add_mul_mod_self_right]
  · exact (Ous.trans (Outs.of_outside (I.out.mono (Nat.le_refl _) (by omega_arith)) (List.mem_cons_self ..))).trans
      (outs_tail O₃)
  · exact ((K₀u.mono (by decide)).trans (I.kp.trans (K₃.mono (by decide)))).mono (by decide)

end VG.Proof.Mont.PPC64LE
