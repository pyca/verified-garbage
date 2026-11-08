module

import VerifiedGarbage.Proof.Mont.PPC64LE.Loop
import VerifiedGarbage.Proof.Mont.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Mont.PPC64LE.Const
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.RangeCover
public import VerifiedGarbage.Impl.Mont.PPC64LE
public import VerifiedGarbage.Proof.Mont.PPC64LE.Csub
public import VerifiedGarbage.Proof.Mont.PPC64LE.AddSub
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words

/-!
# Montgomery arithmetic on PPC64LE: the operations

`rmul`, `add` and `sub` (`Impl/Mont/PPC64LE.lean`) on the numbers at `[r5]`
and `[r6]`, into `[r4]`, with the modulus `m` at `[r3 + M.mo]`, for a layout
of the working space (`OpLay`): `rmul_ok`, `add_ok`, `sub_ok`.

The accumulator of `rmul` is in the registers `treg j`, `r15` up, which are
none of the registers the rest of the code names (`treg_ne`) and distinct
for `j < 10` (`treg_inj`); `regsVal t d k` is the number in `treg d`, …,
`treg (d + k - 1)`. A row of steps (`rmacs_ok`), the iteration of the loop
(`rrow_ok`, invariant `RLoopInv`) and the loop (`rloop_ok`), the reduction
(`rcsub_ok`), and the registers saved, cleared and restored around them.
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

/-! ## The modulus's pointer -/

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


/-! ## The registers of the accumulator -/

/-- The registers `treg` takes. -/
def hiRegs : List Reg := [.r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25]

theorem treg_hi (j : Nat) : treg j ∈ hiRegs := by
  unfold treg
  rw [List.getD_eq_getElem?_getD]
  cases h : ([Reg.r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24] : List Reg)[j]? with
  | none => simp [hiRegs]
  | some r =>
    simp only [Option.getD_some]
    exact (by decide : ∀ x ∈ ([Reg.r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24] : List Reg),
      x ∈ hiRegs) r (List.mem_of_getElem? h)

/-- No register of the accumulator is one the rest of the code names. -/
theorem treg_ne {r : Reg} (hr : r ∉ hiRegs := by decide) (j : Nat) : treg j ≠ r := fun e => hr (e ▸ treg_hi j)

@[simp] theorem treg_eq_r0 (j : Nat) : (treg j = .r0) ↔ False := iff_false_intro (treg_ne (r := .r0) (by decide) j)
@[simp] theorem treg_eq_r3 (j : Nat) : (treg j = .r3) ↔ False := iff_false_intro (treg_ne (r := .r3) (by decide) j)
@[simp] theorem treg_eq_r4 (j : Nat) : (treg j = .r4) ↔ False := iff_false_intro (treg_ne (r := .r4) (by decide) j)
@[simp] theorem treg_eq_r5 (j : Nat) : (treg j = .r5) ↔ False := iff_false_intro (treg_ne (r := .r5) (by decide) j)
@[simp] theorem treg_eq_r6 (j : Nat) : (treg j = .r6) ↔ False := iff_false_intro (treg_ne (r := .r6) (by decide) j)
@[simp] theorem treg_eq_r7 (j : Nat) : (treg j = .r7) ↔ False := iff_false_intro (treg_ne (r := .r7) (by decide) j)
@[simp] theorem treg_eq_r8 (j : Nat) : (treg j = .r8) ↔ False := iff_false_intro (treg_ne (r := .r8) (by decide) j)
@[simp] theorem treg_eq_r9 (j : Nat) : (treg j = .r9) ↔ False := iff_false_intro (treg_ne (r := .r9) (by decide) j)
@[simp] theorem treg_eq_r10 (j : Nat) : (treg j = .r10) ↔ False :=
  iff_false_intro (treg_ne (r := .r10) (by decide) j)
@[simp] theorem treg_eq_r11 (j : Nat) : (treg j = .r11) ↔ False :=
  iff_false_intro (treg_ne (r := .r11) (by decide) j)
@[simp] theorem treg_eq_r12 (j : Nat) : (treg j = .r12) ↔ False :=
  iff_false_intro (treg_ne (r := .r12) (by decide) j)

@[simp] theorem r0_eq_treg (j : Nat) : (Reg.r0 = treg j) ↔ False :=
  iff_false_intro fun e => treg_ne (r := .r0) (by decide) j e.symm
@[simp] theorem r3_eq_treg (j : Nat) : (Reg.r3 = treg j) ↔ False :=
  iff_false_intro fun e => treg_ne (r := .r3) (by decide) j e.symm
@[simp] theorem r4_eq_treg (j : Nat) : (Reg.r4 = treg j) ↔ False :=
  iff_false_intro fun e => treg_ne (r := .r4) (by decide) j e.symm
@[simp] theorem r5_eq_treg (j : Nat) : (Reg.r5 = treg j) ↔ False :=
  iff_false_intro fun e => treg_ne (r := .r5) (by decide) j e.symm
@[simp] theorem r6_eq_treg (j : Nat) : (Reg.r6 = treg j) ↔ False :=
  iff_false_intro fun e => treg_ne (r := .r6) (by decide) j e.symm
@[simp] theorem r7_eq_treg (j : Nat) : (Reg.r7 = treg j) ↔ False :=
  iff_false_intro fun e => treg_ne (r := .r7) (by decide) j e.symm
@[simp] theorem r8_eq_treg (j : Nat) : (Reg.r8 = treg j) ↔ False :=
  iff_false_intro fun e => treg_ne (r := .r8) (by decide) j e.symm
@[simp] theorem r9_eq_treg (j : Nat) : (Reg.r9 = treg j) ↔ False :=
  iff_false_intro fun e => treg_ne (r := .r9) (by decide) j e.symm
@[simp] theorem r10_eq_treg (j : Nat) : (Reg.r10 = treg j) ↔ False :=
  iff_false_intro fun e => treg_ne (r := .r10) (by decide) j e.symm
@[simp] theorem r11_eq_treg (j : Nat) : (Reg.r11 = treg j) ↔ False :=
  iff_false_intro fun e => treg_ne (r := .r11) (by decide) j e.symm
@[simp] theorem r12_eq_treg (j : Nat) : (Reg.r12 = treg j) ↔ False :=
  iff_false_intro fun e => treg_ne (r := .r12) (by decide) j e.symm

/-- The registers of the accumulator are distinct. -/
theorem treg_inj {i j : Nat} (hi : i < 10) (hj : j < 10) (h : treg i = treg j) : i = j :=
  (by decide : ∀ i < 10, ∀ j < 10, treg i = treg j → i = j) i hi j hj h

theorem treg_ne_of {i j : Nat} (hi : i < 10) (hj : j < 10) (h : i ≠ j) : treg i ≠ treg j :=
  fun e => h (treg_inj hi hj e)

/-- The registers `treg d`, …, `treg (d + k - 1)`. -/
def tregs (d k : Nat) : List Reg := (List.range k).map fun j => treg (d + j)

theorem treg_mem_tregs {d k j : Nat} (hj : j < k) : treg (d + j) ∈ tregs d k :=
  List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

theorem tregs_succ (d k : Nat) : tregs d (k + 1) = tregs d k ++ [treg (d + k)] := by
  simp only [tregs, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- A register outside the accumulator's from `d`: `treg i` for `i < d`, or `i ≥ d + k`. -/
theorem treg_not_mem_tregs {d k i : Nat} (hi : i < 10) (hk : d + k ≤ 10) (h : i < d ∨ d + k ≤ i) :
    treg i ∉ tregs d k := by
  intro hm
  obtain ⟨j, hj, e⟩ := List.mem_map.mp hm
  rw [List.mem_range] at hj
  have := treg_inj (by omega) hi e
  omega

theorem nm_tregs {r : Reg} {l : List Reg} (h1 : r ∉ l) (h2 : r ∉ hiRegs) (d k : Nat) : r ∉ l ++ tregs d k := by
  intro h
  rcases List.mem_append.mp h with h' | h'
  · exact h1 h'
  · obtain ⟨j, -, e⟩ := List.mem_map.mp h'; exact h2 (e ▸ treg_hi _)

theorem nm_treg {r : Reg} (h2 : r ∉ hiRegs) (i : Nat) {l : List Reg} (h : r ∉ l) : r ∉ treg i :: l := by
  intro h'
  rcases List.mem_cons.mp h' with e | e
  · exact h2 (e ▸ treg_hi i)
  · exact h e

/-- The number in `treg d`, …, `treg (d + k - 1)`. -/
def regsVal (s : State) (d : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (s.gpr (treg d)).toNat + 2 ^ 64 * regsVal s (d + 1) k

theorem regsVal_lt (s : State) (d k : Nat) : regsVal s d k < 2 ^ (64 * k) := by
  induction k generalizing d with
  | zero => exact Nat.one_pos
  | succ k ih =>
    rw [regsVal, pow64_succ]
    exact word_add_lt (s.gpr (treg d)).isLt (ih (d + 1))

theorem regsVal_succ_top (s : State) (d k : Nat) :
    regsVal s d (k + 1) = regsVal s d k + 2 ^ (64 * k) * (s.gpr (treg (d + k))).toNat := by
  induction k generalizing d with
  | zero => simp [regsVal]
  | succ k ih =>
    rw [regsVal, ih (d + 1), regsVal, pow64_succ, Nat.mul_add, show d + 1 + k = d + (k + 1) by omega]
    grind

theorem regsVal_congr {s t : State} {d k : Nat} (h : ∀ j < k, t.gpr (treg (d + j)) = s.gpr (treg (d + j))) :
    regsVal t d k = regsVal s d k := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    rw [regsVal, regsVal, ih (d := d + 1) (fun j hj => by
      rw [show d + 1 + j = d + (j + 1) by omega]; exact h (j + 1) (by omega)), show d = d + 0 from rfl,
      h 0 (by omega)]

/-- The accumulator's registers that `Kp` keeps. -/
theorem regsVal_kp {rs : List Reg} {s t : State} (K : Kp rs s t) {d k : Nat}
    (h : ∀ j < k, treg (d + j) ∉ rs) : regsVal t d k = regsVal s d k :=
  regsVal_congr fun j hj => K.gpr _ (h j hj)

/-! ## A step, and a row -/

/-- `treg (dst + j) = r9 · [rs + src + 8j] + r0 + treg (rd + j)`, the high
word to `r0`. -/
theorem rmac_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {rs : Reg} {K src rd dst j : Nat}
    (hb : At s base rs K) (hrs : rs ∉ [.r0, .r10, .r11] := by decide) (hsrc4 : src % 4 = 0)
    (hbd : K + (src + 8 * j) + 8 ≤ size) :
    WP isa (.block (rmac rs src rd dst j)) s fun u =>
      (u.gpr (treg (dst + j))).toNat + 2 ^ 64 * (u.gpr .r0).toNat =
        (s.gpr .r9).toNat * (word s.mem base (K + (src + 8 * j))).toNat + (s.gpr (treg (rd + j))).toNat +
          (s.gpr .r0).toNat ∧
      u.mem = s.mem ∧ Kp [.r0, .r10, .r11, treg (dst + j)] s u := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hrs
  obtain ⟨h0, h10, h11⟩ := hrs
  have hs15 := hs.small
  simp only [rmac]
  refine wp_step (ld_ok hs hb h0 (by omega) hbd) ?_
  refine wp_step exec_mulhu ?_
  refine wp_step exec_mul ?_
  refine wp_step exec_addc ?_
  refine wp_step exec_addze ?_
  refine wp_step exec_addc ?_
  refine wp_step exec_addze (WP.block_nil ?_)
  simp only [write_gpr, writeCarry_gpr, write_mem, RegUpd.mem_writeCarry, RegUpd.ca_writeCarry, reduceCtorEq,
    ite_false, ite_true, treg_eq_r0, treg_eq_r10, treg_eq_r11, r0_eq_treg, r10_eq_treg]
  refine ⟨?_, trivial, ?_⟩
  · generalize hx : s.gpr .r9 = x
    generalize hy : word s.mem base (K + (src + 8 * j)) = y
    generalize ht : s.gpr (treg (rd + j)) = t
    generalize hc : s.gpr .r0 = c
    have hP : x.toNat * y.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by have := x.isLt; omega) (by have := y.isLt; omega)
    have := mac_arith hP c.isLt t.isLt
    simp only [BitVec.toNat_ofNat, BitVec.toNat_mul] at this ⊢
    omega
  · refine ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [writeCarry_gpr, write_gpr, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem rmacs_succ (rs : Reg) (src rd dst k : Nat) :
    rmacs rs src rd dst (k + 1) = rmacs rs src rd dst k ++ rmac rs src rd dst k := by
  simp only [rmacs, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The low `k` words of `regs rd + r9 · [rs + src] + r0` to the registers
from `treg dst` (`dst ≤ rd`), the carry word to `r0`. -/
theorem rmacs_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {rs : Reg} {K src rd dst W : Nat}
    (hb : At s base rs K) (hrs : rs ∉ [.r0, .r10, .r11]) (hrsh : rs ∉ hiRegs) (hsrc4 : src % 4 = 0)
    (hbW : K + src + 8 * W ≤ size) (hle : dst ≤ rd) (hW : rd + W ≤ 10) :
    ∀ {k : Nat}, k ≤ W →
    WP isa (.block (rmacs rs src rd dst k)) s fun u =>
      regsVal u dst k + 2 ^ (64 * k) * (u.gpr .r0).toNat =
        regsVal s rd k + (s.gpr .r9).toNat * wordsVal s.mem base (K + src) k + (s.gpr .r0).toNat ∧
      u.mem = s.mem ∧ Kp (([.r0, .r10, .r11] : List Reg) ++ tregs dst k) s u
  | 0, _ => WP.block_nil ⟨by simp [regsVal, wordsVal], rfl, Kp.refl _ _⟩
  | k + 1, hk => by
    rw [rmacs_succ]
    refine WP.block_append (WP.mono (rmacs_ok hs hb hrs hrsh hsrc4 hbW hle hW (k := k) (by omega)) fun s₁ ⟨V₁, M₁, K₁⟩ => ?_)
    have hrs₁ : rs ∉ [.r0, .r10, .r11] ++ tregs dst k := by
      simp only [List.mem_append, not_or]
      refine ⟨hrs, fun h => ?_⟩
      obtain ⟨j, -, e⟩ := List.mem_map.mp h
      exact hrsh (e ▸ treg_hi (dst + j))
    refine WP.mono (rmac_ok (K₁.ws hs) (K₁.at hb hrs₁) (by simpa using hrs) hsrc4 (j := k) (rd := rd) (dst := dst)
      (by omega)) fun u ⟨V₂, M₂, K₂⟩ => ?_
    have h9 : s₁.gpr .r9 = s.gpr .r9 := K₁.gpr _ (by
      simp only [List.mem_append, not_or]
      exact ⟨by decide, fun h => by obtain ⟨j, -, e⟩ := List.mem_map.mp h; exact treg_ne (r := .r9) (by decide) _ e⟩)
    have ht : s₁.gpr (treg (rd + k)) = s.gpr (treg (rd + k)) := K₁.gpr _ (by
      simp only [List.mem_append, not_or]
      refine ⟨by simp, treg_not_mem_tregs (by omega) (by omega) (by omega)⟩)
    rw [h9, ht, M₁] at V₂
    have hr : regsVal u dst k = regsVal s₁ dst k := regsVal_kp K₂ fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by simp, by simp, by simp, treg_ne_of (by omega) (by omega) (by omega)⟩
    refine ⟨?_, M₂.trans M₁, (K₁.mono ?_).trans (K₂.mono ?_)⟩
    · rw [regsVal_succ_top, regsVal_succ_top, wordsVal_succ_top, hr, pow64_succ]
      generalize 2 ^ (64 * k) = P at *
      have e := congrArg (P * ·) V₂
      simp only [Nat.mul_add] at e
      grind
    · intro r hr
      simp only [List.mem_append, tregs_succ] at hr ⊢
      rcases hr with h | h
      · exact .inl h
      · exact .inr (.inl h)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [List.mem_append, tregs_succ, List.mem_cons, List.not_mem_nil, or_false]
      rcases hr with h | h | h | h <;> simp [h]

/-! ## Around the steps -/

theorem regsVal_append (s : State) (d j k : Nat) :
    regsVal s d (j + k) = regsVal s d j + 2 ^ (64 * j) * regsVal s (d + j) k := by
  induction j generalizing d with
  | zero => simp [regsVal]
  | succ j ih =>
    rw [Nat.add_right_comm, regsVal, ih, regsVal, pow64_succ, show d + 1 + j = d + (j + 1) by omega, Nat.mul_add,
      Nat.mul_assoc]
    omega

theorem regsVal_two (s : State) (d : Nat) :
    regsVal s d 2 = (s.gpr (treg d)).toNat + 2 ^ 64 * (s.gpr (treg (d + 1))).toNat := by
  simp only [regsVal, Nat.mul_zero, Nat.add_zero]

theorem regsVal_low (s : State) (d k : Nat) : regsVal s d (k + 1) % 2 ^ 64 = (s.gpr (treg d)).toNat := by
  rw [regsVal, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (BitVec.isLt _)

/-- The carry word `r0` added to `treg n`, the carry out to `r12`. -/
theorem rtopB_ok {s : State} (n : Nat) :
    WP isa (.block [.addc (treg n) (treg n) .r0, .li .r12 0, .addze .r12 .r12]) s fun u =>
      (u.gpr (treg n)).toNat + 2 ^ 64 * (u.gpr .r12).toNat = (s.gpr (treg n)).toNat + (s.gpr .r0).toNat ∧
      u.mem = s.mem ∧ Kp [treg n, .r12] s u := by
  refine wp_step exec_addc ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_addze (WP.block_nil ?_)
  simp only [write_gpr, writeCarry_gpr, write_mem, RegUpd.mem_writeCarry, RegUpd.ca_writeCarry, RegUpd.ca_write,
    ite_false, ite_true, treg_eq_r12, r12_eq_treg]
  refine ⟨?_, trivial, ?_⟩
  · simp only [BitVec.toNat_ofNat]
    have := ca_split (v := (s.gpr (treg n)).toNat + (s.gpr .r0).toNat)
      (by have := (s.gpr (treg n)).isLt; have := (s.gpr .r0).isLt; omega)
    generalize (decide (2 ^ 64 ≤ (s.gpr (treg n)).toNat + (s.gpr .r0).toNat)).toNat = c at *
    omega
  · refine ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, writeCarry_gpr, hr.1, hr.2, ite_false]

/-- `q = treg 0 · [r3 + mi] mod 2⁶⁴` to `r9`, and the first step of its
row: `treg 0 + q m₀` (`m₀` at `[r7]`), whose low word is dropped and high
word goes to `r0`. -/
theorem rqStart_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {K mi : Nat} (h7 : At s base .r7 K) (hmi4 : mi % 4 = 0) (hmi : mi + 8 ≤ size) (hK : K + 8 ≤ size) :
    WP isa (.block [.load .d .r10 wb mi, .mul .r9 (treg 0) .r10, .load .d .r10 .r7 0,
        .mulhu .r0 .r9 .r10, .mul .r10 .r9 .r10, .addc .r10 .r10 (treg 0), .addze .r0 .r0]) s fun u =>
      (u.gpr .r9).toNat = (s.gpr (treg 0)).toNat * (word s.mem base mi).toNat % 2 ^ 64 ∧
      (∃ lo, lo < 2 ^ 64 ∧ lo + 2 ^ 64 * (u.gpr .r0).toNat =
        (u.gpr .r9).toNat * (word s.mem base K).toNat + (s.gpr (treg 0)).toNat) ∧
      u.mem = s.mem ∧ Kp [.r0, .r9, .r10] s u := by
  have hs15 := hs.small
  refine wp_step (ld0_ok hs h3 (by decide) hmi4 hmi) ?_
  refine wp_step exec_mul ?_
  refine wp_step (ld_ok ((hs.write _ _).write _ _) ((h7.write _).write _) (by decide)
    (by decide) (d := 0) (by omega)) ?_
  refine wp_step exec_mulhu ?_
  refine wp_step exec_mul ?_
  refine wp_step exec_addc ?_
  refine wp_step exec_addze (WP.block_nil ?_)
  simp only [write_gpr, writeCarry_gpr, write_mem, RegUpd.mem_writeCarry, RegUpd.ca_writeCarry,
    reduceCtorEq, ite_false, ite_true, Nat.add_zero, BitVec.toNat_mul, treg_eq_r0, treg_eq_r9, treg_eq_r10]
  refine ⟨trivial, ?_, trivial, ?_⟩
  · generalize hq : (s.gpr (treg 0)).toNat * (word s.mem base mi).toNat % 2 ^ 64 = q
    generalize hm : word s.mem base K = m0
    generalize ht : s.gpr (treg 0) = t
    have hq64 : q < 2 ^ 64 := hq ▸ Nat.mod_lt _ (by decide)
    have hP : q * m0.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by have := m0.isLt; omega)
    simp only [BitVec.toNat_ofNat]
    have := t.isLt
    have := ca_split (v := q * m0.toNat % 2 ^ 64 + t.toNat) (by omega)
    generalize (decide (2 ^ 64 ≤ q * m0.toNat % 2 ^ 64 + t.toNat)).toNat = c at *
    refine ⟨(q * m0.toNat % 2 ^ 64 + t.toNat) % 2 ^ 64, Nat.mod_lt _ (by decide), ?_⟩
    omega
  · refine ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, writeCarry_gpr, hr.1, hr.2.1, hr.2.2, ite_false]

/-- The carry word `r0` added to `treg (e + 1)` and the top word `r12`,
moved one word down (to `treg e`, `treg (e + 1)`), the carry out in CA. -/
theorem rtopQ_ok {s : State} {e : Nat} (he : e + 1 < 10) :
    WP isa (.block [.addc (treg e) (treg (e + 1)) .r0, .addze (treg (e + 1)) .r12]) s fun u =>
      (u.gpr (treg e)).toNat + 2 ^ 64 * (u.gpr (treg (e + 1))).toNat + 2 ^ 128 * u.ca.toNat =
        (s.gpr (treg (e + 1))).toNat + 2 ^ 64 * (s.gpr .r12).toNat + (s.gpr .r0).toNat ∧
      u.mem = s.mem ∧ Kp [treg e, treg (e + 1)] s u := by
  refine wp_step exec_addc ?_
  refine wp_step exec_addze (WP.block_nil ?_)
  have hne : treg e ≠ treg (e + 1) := treg_ne_of (by omega) he (by omega)
  simp only [writeCarry_gpr, RegUpd.mem_writeCarry, RegUpd.ca_writeCarry,
    ite_true, hne, hne.symm, ite_false, r12_eq_treg]
  refine ⟨?_, trivial, ?_⟩
  · simp only [BitVec.toNat_ofNat]
    generalize hv : (s.gpr (treg (e + 1))).toNat + (s.gpr .r0).toNat = v
    have h1 := ca_split (v := v) (by have := (s.gpr (treg (e + 1))).isLt; have := (s.gpr .r0).isLt; omega)
    generalize (decide (2 ^ 64 ≤ v)).toNat = c at *
    have := (s.gpr .r12).isLt
    have h2 := ca_split (v := (s.gpr .r12).toNat + c) (by omega)
    generalize (decide (2 ^ 64 ≤ (s.gpr .r12).toNat + c)).toNat = c' at *
    omega
  · refine ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [writeCarry_gpr, hr.1, hr.2, ite_false]

/-! ## An iteration -/

/-- The registers the loop writes. -/
def rclob (n : Nat) : List Reg := [.r0, .r5, .r7, .r8, .r9, .r10, .r11, .r12] ++ tregs 0 (n + 1)

theorem lo_sub_rclob {l : List Reg} (h : ∀ r ∈ l, r ∈ [Reg.r0, .r5, .r7, .r8, .r9, .r10, .r11, .r12] := by decide)
    (n : Nat) : ∀ r ∈ l, r ∈ rclob n := fun r hr => List.mem_append_left _ (h r hr)

theorem treg_mem_rclob {n j : Nat} (hj : j ≤ n) : treg j ∈ rclob n :=
  List.mem_append_right _ (by simpa using treg_mem_tregs (d := 0) (k := n + 1) (j := j) (by omega))

theorem tregs_sub_rclob {n d k : Nat} (h : d + k ≤ n + 1) : ∀ r ∈ tregs d k, r ∈ rclob n := by
  intro r hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  exact treg_mem_rclob (by rw [List.mem_range] at hj; omega)

theorem sub_rclob {l : List Reg} {n d k : Nat}
    (h : ∀ r ∈ l, r ∈ [Reg.r0, .r5, .r7, .r8, .r9, .r10, .r11, .r12] := by decide) (hk : d + k ≤ n + 1) :
    ∀ r ∈ l ++ tregs d k, r ∈ rclob n := by
  intro r hr
  rcases List.mem_append.mp hr with h' | h'
  · exact lo_sub_rclob h n r h'
  · exact tregs_sub_rclob hk r h'

theorem rclob_not_hi {r : Reg} (hr : r ∉ [Reg.r0, .r5, .r7, .r8, .r9, .r10, .r11, .r12]) (hh : r ∉ hiRegs)
    (n : Nat) : r ∉ rclob n := by
  intro h
  rcases List.mem_append.mp h with h' | h'
  · exact hr h'
  · obtain ⟨j, -, e⟩ := List.mem_map.mp h'; exact hh (e ▸ treg_hi _)

/-- What the multiplication needs of the layout: `[a]`, `[b]`, the
modulus and `m'` in the working space. -/
structure RMulLay (M : Mod) (size mi a b : Nat) : Prop where
  n0 : 0 < M.n
  n9 : M.n ≤ 9
  mi_le : mi + 8 ≤ size
  mi4 : mi % 4 = 0
  a_le : a + 8 * M.n ≤ size
  b_le : b + 8 * M.n ≤ size
  mo_le : M.mo + 8 * M.n ≤ size

/-- The invariant of the loop, before the iteration for word `k` of `[a]`:
the registers `treg 0`, …, `treg n` hold `T < 2m` with `2^(64 k) T ≡ A B`,
for the low `k` words `A` of `[a]`; `r5` points to word `k`, `r7` to the
modulus, and `r8` counts the words left. The memory is unchanged. -/
structure RLoopInv (base : Addr) (M : Mod) (a b m k : Nat) (s t : State) : Prop where
  r3 : At t base .r3 0
  r5 : At t base .r5 (a + 8 * k)
  r6 : At t base .r6 b
  r7 : At t base .r7 M.mo
  r8 : t.gpr .r8 = BitVec.ofNat 64 (M.n - k)
  mem : t.mem = s.mem
  kp : Kp (rclob M.n) s t
  lt : regsVal t 0 (M.n + 1) < 2 * m
  cong : ∃ U, 2 ^ (64 * k) * regsVal t 0 (M.n + 1) = wordsVal s.mem base a k * wordsVal s.mem base b M.n + U * m

theorem rrow_eq (M : Mod) (acc : Nat) : rrow M acc =
    ([.load .d .r9 .r5 0, .li .r0 0] : List Instr) ++ (rmacs .r6 0 0 0 M.n ++
    (([.addc (treg M.n) (treg M.n) .r0, .li .r12 0, .addze .r12 .r12] : List Instr) ++
    (([.load .d .r10 wb (acc + 8 * (M.n + 1)), .mul .r9 (treg 0) .r10, .load .d .r10 .r7 0,
      .mulhu .r0 .r9 .r10, .mul .r10 .r9 .r10, .addc .r10 .r10 (treg 0), .addze .r0 .r0] : List Instr) ++
    (rmacs .r7 8 1 0 (M.n - 1) ++
    (([.addc (treg (M.n - 1)) (treg M.n) .r0, .addze (treg M.n) .r12] : List Instr) ++
    ([.addi .r5 .r5 8, .subi .r8 .r8 1] : List Instr)))))) := by
  simp only [rrow, rrowB, rrowM, List.append_assoc]

/-- An iteration of the loop. -/
theorem rrow_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {acc a b m k : Nat}
    (hL : RMulLay M size (acc + 8 * (M.n + 1)) a b) (hk : k < M.n) (hm : wordsVal s.mem base M.mo M.n = m)
    (hinv : (m * (word s.mem base (acc + 8 * (M.n + 1))).toNat + 1) % 2 ^ 64 = 0)
    (hB : wordsVal s.mem base b M.n < m) {t : State} (I : RLoopInv base M a b m k s t) :
    WP isa (.block (rrow M acc)) t fun u => RLoopInv base M a b m (k + 1) s u := by
  have hn := hs.nowrap
  have hs15 := hs.small
  obtain ⟨n0, n9, mi_le, mi4, a_le, b_le, mo_le⟩ := hL
  obtain ⟨N, hN⟩ : ∃ N, M.n = N + 1 := ⟨M.n - 1, by omega⟩
  have ht := I.kp.ws hs
  rw [rrow_eq]
  -- u
  have hat : word t.mem base (a + 8 * k + 0) = word s.mem base (a + 8 * k) := by rw [I.mem, Nat.add_zero]
  refine WP.block_append (wp_step (ld_ok ht I.r5 (by decide) (by decide) (d := 0) (by omega))
    (wp_step (exec_li (by decide)) (WP.block_nil ?_)))
  rw [hat]
  generalize hu : word s.mem base (a + 8 * k) = u
  -- T += u [b]
  refine WP.block_append (WP.mono (rmacs_ok ((ht.write _ _).write _ _) ((I.r6.write _).write _)
    (rs := .r6) (src := 0) (rd := 0) (dst := 0) (W := M.n) (by decide) (by decide) (by decide) (by omega)
    (Nat.le_refl _) (by omega) (Nat.le_refl _)) fun t₂ ⟨V₂, M₂, K₂⟩ => ?_)
  simp only [write_gpr, write_mem, reduceCtorEq, ite_false, ite_true, Nat.add_zero] at V₂ M₂
  rw [show (BitVec.ofNat 64 0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at V₂
  have hrt : regsVal ((t.write .r9 u).write .r0 (BitVec.ofNat 64 0)) 0 M.n = regsVal t 0 M.n :=
    regsVal_congr fun j _ => by simp only [write_gpr, treg_eq_r0, treg_eq_r9, ite_false]
  rw [hrt] at V₂
  refine WP.block_append (WP.mono (rtopB_ok (s := t₂) M.n) fun t₃ ⟨V₃, M₃, K₃⟩ => ?_)
  have K₁₃ : Kp (rclob M.n) t t₃ :=
    (((Kp.write t _ (lo_sub_rclob (l := [.r9]) (by decide) M.n _ (by simp))).trans
      (Kp.write _ _ (lo_sub_rclob (l := [.r0]) (by decide) M.n _ (by simp)))).trans
      (K₂.mono (sub_rclob (by decide) (by omega)))).trans
      (K₃.mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact treg_mem_rclob (Nat.le_refl _)
        · exact lo_sub_rclob (l := [.r12]) (by decide) M.n _ (by simp))
  -- The accumulator after the first row, with its top word in `r12`: `T₁ = T + u B`.
  generalize hT : regsVal t 0 (M.n + 1) = T at I
  generalize hTB : wordsVal s.mem base b M.n = B at hB
  have hbt : wordsVal t.mem base b M.n = B := by rw [← hTB, I.mem]
  rw [hbt] at V₂
  generalize hc₃ : (t₃.gpr .r12).toNat = c₃ at V₃
  have hn2 : (t₂.gpr (treg M.n)) = t.gpr (treg M.n) := by
    rw [K₂.gpr _ (by
      simp only [List.mem_append, not_or]
      exact ⟨by simp, treg_not_mem_tregs (by omega) (by omega) (by omega)⟩)]
    simp only [write_gpr, treg_eq_r0, treg_eq_r9, ite_false]
  rw [hn2] at V₃
  have h3r : regsVal t₃ 0 M.n = regsVal t₂ 0 M.n := regsVal_kp K₃ fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, Nat.zero_add]
    exact ⟨treg_ne_of (by omega) (by omega) (by omega), by simp⟩
  have hT1 : regsVal t₃ 0 (M.n + 1) + 2 ^ (64 * (M.n + 1)) * c₃ = T + u.toNat * B := by
    have e1 := regsVal_succ_top t₃ 0 M.n
    have e2 := regsVal_succ_top t 0 M.n
    rw [Nat.zero_add] at e1 e2
    rw [h3r] at e1
    rw [e1, ← hT, e2, show 64 * (M.n + 1) = 64 + 64 * M.n by omega, Nat.pow_add]
    generalize 2 ^ (64 * M.n) = P at *
    have e := congrArg (P * ·) V₃
    simp only [Nat.mul_add] at e
    grind
  generalize hT1v : regsVal t₃ 0 (M.n + 1) + 2 ^ (64 * (M.n + 1)) * c₃ = T1 at hT1
  -- q, and the first step of its row.
  have ht₃ := K₁₃.ws ht
  have h3₃ : At t₃ base .r3 0 := K₁₃.at I.r3 (rclob_not_hi (by decide) (by decide) _)
  have h7₃ : At t₃ base .r7 M.mo := by
    rw [At, K₃.gpr _ (by simp), K₂.gpr _ (by simp [tregs]), write_gpr, write_gpr]; simp only [reduceCtorEq, ite_false]
    exact I.r7
  refine WP.block_append (WP.mono (rqStart_ok ht₃ h3₃ h7₃ (mi := acc + 8 * (M.n + 1)) mi4 mi_le (by omega))
    fun t₄ ⟨q₄, ⟨lo, hlo, V₄⟩, M₄, K₄⟩ => ?_)
  have hmem₃ : t₃.mem = s.mem := by rw [M₃, M₂, I.mem]
  have ht0 : (t₃.gpr (treg 0)).toNat = T1 % 2 ^ 64 := by
    rw [← hT1v, show 64 * (M.n + 1) = 64 + 64 * M.n by omega, Nat.pow_add, Nat.mul_assoc, Nat.add_mul_mod_self_left,
      regsVal_low]
  rw [hmem₃, ht0] at q₄
  rw [hmem₃, ht0] at V₄
  generalize hq : (t₄.gpr .r9).toNat = q at q₄ V₄
  have hq64 : q < 2 ^ 64 := hq ▸ BitVec.isLt _
  generalize hM' : wordsVal s.mem base (M.mo + 8) N = M'
  have hmM : m = (word s.mem base M.mo).toNat + 2 ^ 64 * M' := by
    rw [← hm, ← hM', hN]; rfl
  have hlo0 : lo = 0 := by
    have hl := mont_low (T1 % 2 ^ 64) (word s.mem base (acc + 8 * (M.n + 1))).toNat m hinv
    rw [← q₄, hmM] at hl
    have : (lo + 2 ^ 64 * (t₄.gpr .r0).toNat) % 2 ^ 64 = lo := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
    rw [V₄] at this
    rw [← this]
    have e : T1 % 2 ^ 64 + q * ((word s.mem base M.mo).toNat + 2 ^ 64 * M') =
      (q * (word s.mem base M.mo).toNat + T1 % 2 ^ 64) + 2 ^ 64 * (q * M') := by grind
    rw [e, Nat.add_mul_mod_self_left] at hl
    exact hl
  rw [hlo0, Nat.zero_add] at V₄
  -- The rest of the modulus's row.
  have h7₄ : At t₄ base .r7 M.mo := K₄.at h7₃
  refine WP.block_append (WP.mono (rmacs_ok (K₄.ws ht₃) h7₄ (rs := .r7) (K := M.mo) (src := 8)
    (rd := 1) (dst := 0) (W := M.n - 1) (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
    (Nat.le_refl _)) fun t₅ ⟨V₅, M₅, K₅⟩ => ?_)
  rw [M₄, hq, hmem₃] at V₅
  have hn1 : M.n - 1 + 1 = M.n := by omega
  have := rtopQ_ok (s := t₅) (e := M.n - 1) (by omega)
  rw [hn1] at this
  refine WP.block_append (WP.mono this fun t₆ ⟨V₆, M₆, K₆⟩ => ?_)
  -- The pointers and the count.
  refine wp_step (exec_addi (by decide) (by decide)) ?_
  refine wp_step (exec_subi (by decide) (by decide)) (WP.block_nil ?_)
  -- What the second row keeps.
  have hf₅ : t₅.gpr (treg M.n) = t₃.gpr (treg M.n) := by
    rw [K₅.gpr _ (by
      simp only [List.mem_append, not_or]
      exact ⟨by simp, treg_not_mem_tregs (by omega) (by omega) (by omega)⟩), K₄.gpr _ (by simp)]
  have h12₅ : (t₅.gpr .r12).toNat = c₃ := by
    rw [K₅.gpr _ (by simp only [List.mem_append, not_or]; exact ⟨by decide, fun h => by
      obtain ⟨j, -, e⟩ := List.mem_map.mp h; exact treg_ne (r := .r12) (by decide) _ e⟩), K₄.g (r := .r12) (by decide), hc₃]
  have h0₅ : (t₅.gpr .r0) = t₅.gpr .r0 := rfl
  rw [hf₅, h12₅] at V₆
  have h4r : regsVal t₄ 1 (M.n - 1) = regsVal t₃ 1 (M.n - 1) := regsVal_kp K₄ fun j _ => by simp
  rw [h4r, show M.n - 1 = N by omega, hM'] at V₅
  rw [show N = M.n - 1 by omega] at V₅
  have hT1s : T1 = T1 % 2 ^ 64 + 2 ^ 64 * (regsVal t₃ 1 (M.n - 1) + 2 ^ (64 * (M.n - 1)) *
      ((t₃.gpr (treg M.n)).toNat + 2 ^ 64 * c₃)) := by
    rw [← ht0, ← hT1v]
    have e1 : regsVal t₃ 0 (M.n + 1) = (t₃.gpr (treg 0)).toNat + 2 ^ 64 * regsVal t₃ 1 M.n := rfl
    have e2 := regsVal_succ_top t₃ 1 (M.n - 1)
    rw [hn1, show 1 + (M.n - 1) = M.n by omega] at e2
    have e3 : 2 ^ (64 * (M.n + 1)) = 2 ^ 64 * 2 ^ (64 * (M.n - 1)) * 2 ^ 64 := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    rw [e1, e2, e3]
    generalize 2 ^ (64 * (M.n - 1)) = R
    grind
  have h6r : regsVal t₆ 0 (M.n - 1) = regsVal t₅ 0 (M.n - 1) := regsVal_kp K₆ fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, Nat.zero_add]
    exact ⟨treg_ne_of (by omega) (by omega) (by omega), treg_ne_of (by omega) (by omega) (by omega)⟩
  have hT' : regsVal t₆ 0 (M.n + 1) = regsVal t₅ 0 (M.n - 1) + 2 ^ (64 * (M.n - 1)) *
      ((t₆.gpr (treg (M.n - 1))).toNat + 2 ^ 64 * (t₆.gpr (treg M.n)).toNat) := by
    rw [show M.n + 1 = M.n - 1 + 2 by omega, regsVal_append, regsVal_two, h6r, Nat.zero_add, hn1]
  have hmath := rowM_math hT1s hmM V₄ V₅ V₆
  rw [← hT'] at hmath
  have hrow := row_lt I.lt u.isLt hB hq64
  have hX : 2 * m ≤ 2 ^ (64 * (M.n - 1)) * 2 ^ 128 := by
    have : m < 2 ^ (64 * M.n) := by rw [← hm]; exact wordsVal_lt _ _ _ _
    rw [← Nat.pow_add, show 64 * (M.n - 1) + 128 = 64 * M.n + 64 by omega, Nat.pow_add]
    have : 2 ≤ 2 ^ 64 := by decide
    have := Nat.mul_le_mul_left (2 ^ (64 * M.n)) this
    omega
  have hca : t₆.ca.toNat = 0 := by
    rcases Nat.eq_zero_or_pos t₆.ca.toNat with h | h
    · exact h
    · exfalso
      have : 2 ^ 64 * (2 ^ (64 * (M.n - 1)) * 2 ^ 128) ≤ 2 ^ 64 * 2 ^ (64 * (M.n - 1)) * 2 ^ 128 * t₆.ca.toNat := by
        rw [Nat.mul_assoc (2 ^ 64)]; exact Nat.le_mul_of_pos_right _ h
      have := Nat.mul_le_mul_left (2 ^ 64) hX
      rw [hT1] at hmath
      omega
  rw [hca, Nat.mul_zero, Nat.add_zero, hT1] at hmath
  have K₃₆ : Kp (rclob M.n) t₃ t₆ :=
    ((K₄.mono (lo_sub_rclob (by decide) M.n)).trans (K₅.mono (sub_rclob (by decide) (by omega)))).trans
      (K₆.mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact treg_mem_rclob (by omega)
        · exact treg_mem_rclob (Nat.le_refl _))
  have K₁₆ := K₁₃.trans K₃₆
  have keep : ∀ r : Reg, r ∉ [Reg.r0, .r9, .r10, .r11, .r12] → r ∉ hiRegs → t₆.gpr r = t.gpr r := by
    intro r h1 h2
    have hh : ∀ j, treg j ≠ r := fun j e => h2 (e ▸ treg_hi j)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1
    obtain ⟨a0, a9, a10, a11, a12⟩ := h1
    rw [K₆.gpr r (nm_treg h2 _ (nm_treg h2 _ List.not_mem_nil)),
      K₅.gpr r (nm_tregs (by simp [a0, a10, a11]) h2 _ _), K₄.gpr r (by simp [a0, a9, a10]),
      K₃.gpr r (nm_treg h2 _ (by simp [a12])), K₂.gpr r (nm_tregs (by simp [a0, a10, a11]) h2 _ _)]
    simp only [write_gpr, a0, a9, ite_false]
  have hwr : ∀ (x y : BitVec 64) (j : Nat), ((t₆.write .r5 x).write .r8 y).gpr (treg j) = t₆.gpr (treg j) :=
    fun _ _ _ => by simp only [write_gpr, treg_eq_r5, treg_eq_r8, ite_false]
  have hrv : ∀ (x y : BitVec 64), regsVal ((t₆.write .r5 x).write .r8 y) 0 (M.n + 1) = regsVal t₆ 0 (M.n + 1) :=
    fun _ _ => regsVal_congr fun j _ => hwr _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [At, write_gpr, reduceCtorEq, ite_false]; rw [keep _ (by decide) (by decide)]; exact I.r3
  · simp only [At, write_gpr, reduceCtorEq, ite_false, ite_true]
    rw [keep _ (by decide) (by decide), I.r5, off_add, show a + 8 * k + 8 = a + 8 * (k + 1) by omega]
  · simp only [At, write_gpr, reduceCtorEq, ite_false]; rw [keep _ (by decide) (by decide)]; exact I.r6
  · simp only [At, write_gpr, reduceCtorEq, ite_false]; rw [keep _ (by decide) (by decide)]; exact I.r7
  · simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
    rw [keep _ (by decide) (by decide), I.r8]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have : M.n < 2 ^ 15 := by omega
    omega
  · simp only [write_mem]; rw [M₆, M₅, M₄, hmem₃]
  · exact I.kp.trans (K₁₆.trans ((Kp.write _ _ (lo_sub_rclob (l := [.r5]) (by decide) M.n _ (by simp))).trans
      (Kp.write _ _ (lo_sub_rclob (l := [.r8]) (by decide) M.n _ (by simp)))))
  · rw [hrv]
    generalize regsVal t₆ 0 (M.n + 1) = T' at hmath ⊢
    have : 2 ^ 64 * T' < 2 ^ 64 * (2 * m) := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  · obtain ⟨U, hU⟩ := I.cong
    rw [hT, hTB] at hU
    refine ⟨U + q * 2 ^ (64 * k), ?_⟩
    rw [hrv]
    generalize regsVal t₆ 0 (M.n + 1) = T' at hmath ⊢
    have hA : wordsVal s.mem base a (k + 1) = wordsVal s.mem base a k + 2 ^ (64 * k) * u.toNat := by
      rw [wordsVal_succ_top, hu]
    rw [hA, show 64 * (k + 1) = 64 * k + 64 by omega, Nat.pow_add, Nat.mul_assoc, hmath, Nat.mul_add, Nat.mul_add, hU]
    grind

/-! ## The loop -/

/-- The loop of `rmul`: from the invariant at word 0 to the invariant at `n`. -/
theorem rloop_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {acc a b m : Nat}
    (hL : RMulLay M size (acc + 8 * (M.n + 1)) a b) (hm : wordsVal s.mem base M.mo M.n = m)
    (hinv : (m * (word s.mem base (acc + 8 * (M.n + 1))).toNat + 1) % 2 ^ 64 = 0)
    (hB : wordsVal s.mem base b M.n < m) {t : State} (h0 : RLoopInv base M a b m 0 s t) :
    WP isa (.loop (.block (rrow M acc)) (.nonzero .d .r8)) t fun u => RLoopInv base M a b m M.n s u := by
  have hD15 : M.n < 2 ^ 15 := by have := hL.n9; omega
  refine WP.loop (M := isa)
    (fun n t' => ∃ k, n = M.n - k ∧ k < M.n ∧ RLoopInv base M a b m k s t') ?_ M.n t ⟨0, rfl, hL.n0, h0⟩
  rintro n t' ⟨k, rfl, hk, I⟩
  refine WP.mono (rrow_ok hs hL hk hm hinv hB I) fun u I' => ?_
  have he := eval_nonzero_ofNat I'.r8 (x := M.n - (k + 1)) (by omega)
  by_cases hk1 : k + 1 = M.n
  · exact .inl ⟨by rw [he]; simp [hk1], hk1 ▸ I'⟩
  · exact .inr ⟨by rw [he]; simp; omega, M.n - (k + 1), by omega, k + 1, rfl, by omega, I'⟩

/-! ## The reduction -/

theorem rsubs_succ (M : Mod) (k : Nat) :
    (List.range (k + 1)).flatMap (rsubStep M) = (List.range k).flatMap (rsubStep M) ++ rsubStep M k := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The low `k` words of `T + 2^(64 k) - m` (`T` in registers, `m` at `r7`)
to `[M.tmp]`, no borrow to CA. -/
theorem rsubs_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {W : Nat}
    (h3 : At s base .r3 0) (h7 : At s base .r7 M.mo) (htmp4 : M.tmp % 4 = 0) (hmo : M.mo + 8 * W ≤ size)
    (htmp : M.tmp + 8 * W ≤ size) (sm : M.mo + 8 * W ≤ M.tmp ∨ M.tmp + 8 * W ≤ M.mo) :
    ∀ {k : Nat}, k ≤ W →
    WP isa (.block ((List.range k).flatMap (rsubStep M))) s fun u =>
      Outside base M.tmp (8 * k) s.mem u.mem ∧
      wordsVal u.mem base M.tmp k + 2 ^ (64 * k) * cOf true k u.ca + wordsVal s.mem base M.mo k =
        regsVal s 0 k + (2 ^ (64 * k) - 1) + 1 ∧
      Kp [.r11, .r12] s u
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, by simp [wordsVal, regsVal, cOf], Kp.refl _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    have hs15 := hs.small
    rw [rsubs_succ]
    refine WP.block_append (WP.mono (rsubs_ok hs h3 h7 htmp4 hmo htmp sm (k := k) (by omega))
      fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have h3₁ := K₁.at h3
    have h7₁ := K₁.at h7
    have hs₁ := K₁.ws hs
    simp only [rsubStep]
    refine wp_step (ld_ok hs₁ h7₁ (by decide) (by omega) (d := 8 * k) (by omega)) ?_
    refine wp_step (exec_carryOp _ _ _ _ _ _) ?_
    refine wp_step (std_ok ((hs₁.write _ _).writeCarry _ _) ((h3₁.write _).writeCarry _)
      (by decide) (by omega) (d := M.tmp + 8 * k) (by omega)) (WP.block_nil ?_)
    simp only [write_gpr, writeCarry_gpr, write_mem, RegUpd.mem_writeCarry, RegUpd.ca_write,
      reduceCtorEq, ite_false, ite_true, Nat.zero_add, treg_eq_r12, ite_true]
    generalize hlo : BitVec.ofNat 64 ((s₁.gpr (treg k)).toNat + (2 ^ 64 - 1 - (word s₁.mem base (M.mo + 8 * k)).toNat) +
      cOf true k s₁.ca) = lo
    have W := writeW_outside s₁.mem base (d := M.tmp + 8 * k) lo (by omega)
    have ht : s₁.gpr (treg k) = s.gpr (treg k) := K₁.gpr _ (by simp)
    have hy : word s₁.mem base (M.mo + 8 * k) = word s.mem base (M.mo + 8 * k) := O₁.word (by omega) (by omega)
    have hr₁ : regsVal s₁ 0 k = regsVal s 0 k := regsVal_kp K₁ fun j _ => by simp
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (W.mono (by omega) (by omega)), ?_, ?_⟩
    · have hc : cOf true k s₁.ca ≤ 1 := by unfold cOf; split <;> exact Bool.toNat_le _
      have hx := (s.gpr (treg k)).isLt
      have hyl := (word s.mem base (M.mo + 8 * k)).isLt
      have e := RegUpd.toNat_add_ca ((s₁.write .r12 (word s₁.mem base (M.mo + 8 * k)))) (r := .r11)
        (v := (s₁.gpr (treg k)).toNat + (2 ^ 64 - 1 - (word s₁.mem base (M.mo + 8 * k)).toNat) + cOf true k s₁.ca)
        (by omega)
      rw [RegUpd.gpr_writeCarry_self] at e
      rw [show ({ (s₁.write .r12 (word s₁.mem base (M.mo + 8 * k))).writeCarry .r11 _ with mem := _ } : State).ca =
        ((s₁.write .r12 (word s₁.mem base (M.mo + 8 * k))).writeCarry .r11 _).ca from rfl]
      rw [regsVal_succ_top, wordsVal_succ_top, wordsVal_succ_top, W.wordsVal (by omega) (by omega), word_writeW_self,
        pow64_succ, Nat.zero_add]
      generalize hcb : ((State.write s₁ Reg.r12 (word s₁.mem base (M.mo + 8 * k))).writeCarry Reg.r11
        ((s₁.gpr (treg k)).toNat + (2 ^ 64 - 1 - (word s₁.mem base (M.mo + 8 * k)).toNat) + cOf true k s₁.ca)).ca = cb at *
      rw [hlo] at e
      rw [hy, ht] at e
      generalize hcc : cOf true k s₁.ca = c at *
      simp only [cOf, Nat.succ_ne_zero, ite_false]
      have hP : 1 ≤ 2 ^ (64 * k) := Nat.one_le_two_pow
      generalize 2 ^ (64 * k) = P at *
      have e2 := congrArg (P * ·) e
      simp only [Nat.mul_add] at e2
      generalize (word s.mem base (M.mo + 8 * k)).toNat = y at *
      have hA : P * (2 ^ 64 - 1 - y) + P * y = 2 ^ 64 * P - P := by
        rw [← Nat.mul_add, show 2 ^ 64 - 1 - y + y = 2 ^ 64 - 1 by omega, Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
      have hB : P * (2 ^ 64 * cb.toNat) = 2 ^ 64 * P * cb.toNat := by
        rw [Nat.mul_left_comm, Nat.mul_assoc]
      have hC : P ≤ 2 ^ 64 * P := Nat.le_mul_of_pos_left _ (by decide)
      rw [hB] at e2
      generalize P * (2 ^ 64 - 1 - y) = A at *
      generalize P * y = B at *
      generalize 2 ^ 64 * P * cb.toNat = D at *
      generalize 2 ^ 64 * P = E at *
      omega
    · exact K₁.trans (((Kp.write _ _ (by decide)).trans (Kp.writeCarry _ _ (by decide))).trans (Kp.store _ _ _))

theorem rsels_succ (M : Mod) (k : Nat) :
    (List.range (k + 1)).flatMap (rselWord M) = (List.range k).flatMap (rselWord M) ++ rselWord M k := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The low `k` words of `T` (in registers), or of `[M.tmp]` where the mask
`r10` is all ones, to `[r4]`. -/
theorem rsels_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {O W : Nat}
    (h3 : At s base .r3 0) (h4 : At s base .r4 O) (htmp4 : M.tmp % 4 = 0)
    (hmk : s.gpr .r10 = 0 ∨ s.gpr .r10 = BitVec.allOnes 64)
    (htmp : M.tmp + 8 * W ≤ size) (hO : O + 8 * W ≤ size) (hs2 : M.tmp + 8 * W ≤ O ∨ O + 8 * W ≤ M.tmp) :
    ∀ {k : Nat}, k ≤ W →
    WP isa (.block ((List.range k).flatMap (rselWord M))) s fun u =>
      Outside base O (8 * k) s.mem u.mem ∧
      wordsVal u.mem base O k = (if s.gpr .r10 = 0 then regsVal s 0 k else wordsVal s.mem base M.tmp k) ∧
      Kp [.r11, .r12] s u
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, by simp [wordsVal, regsVal], Kp.refl _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    have hs15 := hs.small
    rw [rsels_succ]
    refine WP.block_append (WP.mono (rsels_ok hs h3 h4 htmp4 hmk htmp hO hs2 (k := k) (by omega))
      fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hs₁ := K₁.ws hs
    simp only [rselWord]
    refine wp_step (ld0_ok hs₁ (K₁.at h3) (by decide) (by omega) (d := M.tmp + 8 * k) (by omega)) ?_
    refine wp_step exec_logic ?_
    refine wp_step exec_logic ?_
    refine wp_step exec_logic ?_
    refine wp_step (std_ok (((((hs₁.write _ _).write _ _).write _ _).write _ _))
      ((((K₁.at h4).write _).write _).write _ |>.write _) (by decide) (by omega) (d := 8 * k) (by omega))
      (WP.block_nil ?_)
    simp only [write_gpr, write_mem, reduceCtorEq, ite_false, ite_true, treg_eq_r12]
    have ht : s₁.gpr (treg k) = s.gpr (treg k) := K₁.gpr _ (by simp)
    have h10 : s₁.gpr .r10 = s.gpr .r10 := K₁.g
    rw [ht, h10, O₁.word (by omega) (by omega), sel_mask _ _ hmk]
    generalize hv : (if s.gpr .r10 = 0 then s.gpr (treg k) else word s.mem base (M.tmp + 8 * k)) = v
    have W := writeW_outside s₁.mem base (d := O + 8 * k) v (by omega)
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (W.mono (by omega) (by omega)), ?_, ?_⟩
    · rw [wordsVal_succ_top, regsVal_succ_top, wordsVal_succ_top, W.wordsVal (by omega) (by omega), V₁,
        word_writeW_self, ← hv, Nat.zero_add]
      split <;> rfl
    · exact K₁.trans ((((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans
        ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide)))).trans (Kp.store _ _ _))

/-- What `rcsub` needs of the layout: the difference (`n` words at
`M.tmp`), the modulus (`n` at `M.mo`) and the result (`n` at `O`). -/
structure RCsubLay (M : Mod) (size O : Nat) : Prop where
  tmp_le : M.tmp + 8 * M.n ≤ size
  mo_le : M.mo + 8 * M.n ≤ size
  o_le : O + 8 * M.n ≤ size
  tmp4 : M.tmp % 4 = 0
  s2 : M.mo + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ M.mo
  s4 : M.tmp + 8 * M.n ≤ O ∨ O + 8 * M.n ≤ M.tmp

/-- `[r4] = T mod m`, for `T` below `2m` in `treg 0`, …, `treg n` and the
modulus at `r7`. -/
theorem rcsub_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {O m : Nat}
    (h3 : At s base .r3 0) (h4 : At s base .r4 O) (h7 : At s base .r7 M.mo) (hL : RCsubLay M size O)
    (hn0 : 0 < M.n) (hm : wordsVal s.mem base M.mo M.n = m) (hN : regsVal s 0 (M.n + 1) < 2 * m) :
    WP isa (.block (rcsub M)) s fun u =>
      wordsVal u.mem base O M.n = regsVal s 0 (M.n + 1) % m ∧
      Outs base [(M.tmp, 8 * M.n), (O, 8 * M.n)] s.mem u.mem ∧
      Kp [.r10, .r11, .r12] s u := by
  obtain ⟨tmp_le, mo_le, o_le, tmp4, s2, s4⟩ := hL
  have hn := hs.nowrap
  have hs15 := hs.small
  simp only [rcsub, List.append_assoc]
  refine WP.block_append (WP.mono (rsubs_ok (W := M.n) hs h3 h7 tmp4 mo_le tmp_le s2 (k := M.n) (Nat.le_refl _))
    fun s₂ ⟨O₂, V₂, K₂⟩ => ?_)
  rw [hm, show cOf true M.n s₂.ca = s₂.ca.toNat by simp only [cOf]; split <;> omega] at V₂
  have hs₂ := K₂.ws hs
  refine wp_step exec_addze ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub ?_
  simp only [write_gpr, writeCarry_gpr, ite_true, reduceCtorEq, ite_false]
  have htop : s₂.gpr (treg M.n) = s.gpr (treg M.n) := K₂.gpr _ (by simp)
  rw [htop]
  generalize hc : s₂.ca.toNat = c at V₂
  generalize hT : (s.gpr (treg M.n)).toNat = top
  have hL' : regsVal s₂ 0 M.n = regsVal s 0 M.n := regsVal_kp K₂ fun j _ => by simp
  have hN' : regsVal s 0 M.n + 2 ^ (64 * M.n) * top < 2 * m := by
    rw [← hT, show treg M.n = treg (0 + M.n) by rw [Nat.zero_add], ← regsVal_succ_top]; exact hN
  have hm0 : m < 2 ^ (64 * M.n) := by rw [← hm]; exact wordsVal_lt _ _ _ _
  have hc1 : c ≤ 1 := hc ▸ Bool.toNat_le _
  obtain ⟨hct, hsel⟩ := csub_math hm0 hN' (wordsVal_lt s₂.mem base M.tmp M.n)
    (by have := V₂; omega) hc1
  have hadd : BitVec.ofNat 64 (top + c) = BitVec.ofNat 64 (c + top) := by rw [Nat.add_comm]
  rw [hadd]
  have h3₂ := K₂.at h3
  have h4₂ := K₂.at h4
  refine WP.mono (rsels_ok (W := M.n) ((((hs₂.writeCarry _ _).write _ _).write _ _))
    (((h3₂.writeCarry _).write _).write _) (((h4₂.writeCarry _).write _).write _) tmp4
    (by simp only [write_gpr, ite_true]; exact neg_mask hct) tmp_le o_le s4 (k := M.n) (Nat.le_refl _))
    fun u ⟨O₃, V₃, K₃⟩ => ⟨?_, ?_, ?_⟩
  · simp only [write_gpr, ite_true, write_mem, RegUpd.mem_writeCarry] at V₃
    have hr : regsVal (((s₂.writeCarry .r10 (top + c)).write .r11 (BitVec.ofNat 64 0)).write .r10
        (BitVec.ofNat 64 0 - BitVec.ofNat 64 (c + top))) 0 M.n = regsVal s 0 M.n := by
      rw [← hL']; exact regsVal_congr fun j _ => by
        simp only [write_gpr, writeCarry_gpr, treg_eq_r10, treg_eq_r11, ite_false]
    rw [V₃, hr, regsVal_succ_top, Nat.zero_add, hT, ← hsel]
    simp only [neg_mask_zero hct]
  · simp only [write_mem, RegUpd.mem_writeCarry] at O₃
    intro x hx
    rw [O₃ x (hx (O, 8 * M.n) (by simp)), O₂ x (by
      have := hx (M.tmp, 8 * M.n) (by simp)
      simp only at this; omega)]
  · exact (K₂.mono (by decide)).trans ((((Kp.writeCarry _ _ (by decide)).trans
      ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide)))).trans (K₃.mono (by decide))))

/-! ## Saving, clearing and restoring the accumulator's registers -/

theorem rsave_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {acc : Nat}
    (h3 : At s base .r3 0) (hacc4 : acc % 4 = 0) : ∀ {k : Nat}, acc + 8 * k ≤ size →
    WP isa (.block ((List.range k).map fun j => .store .d (treg j) wb (acc + 8 * j))) s
      fun u => Outside base acc (8 * k) s.mem u.mem ∧ (∀ j < k, word u.mem base (acc + 8 * j) = s.gpr (treg j)) ∧
        Kp [] s u ∧ u.gpr = s.gpr
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _), Kp.refl _ _, rfl⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    have hs15 := hs.small
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    refine WP.block_append (WP.mono (rsave_ok hs h3 hacc4 (k := k) (by omega)) fun s₁ ⟨O₁, Z₁, K₁, r₁⟩ => ?_)
    refine wp_step (std_ok (K₁.ws hs) (K₁.at h3) (by decide) (by omega) (d := acc + 8 * k) (by omega))
      (WP.block_nil ?_)
    rw [Nat.zero_add]
    have W := writeW_outside s₁.mem base (d := acc + 8 * k) (s₁.gpr (treg k)) (by omega)
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (W.mono (by omega) (by omega)), fun j hj => ?_,
      K₁.trans (Kp.store _ _ _), r₁⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · show word (s₁.mem.writeW _ _) base _ = _
      rw [word_writeW_ne _ (by omega) (by omega) (by omega)]; exact Z₁ j hj
    · show word (s₁.mem.writeW _ _) base _ = _
      rw [word_writeW_self, r₁]

theorem rzero_ok {s : State} : ∀ {k : Nat}, k ≤ 10 →
    WP isa (.block ((List.range k).map fun j => .li (treg j) 0)) s
      fun u => u.mem = s.mem ∧ (∀ j < k, u.gpr (treg j) = 0) ∧ Kp (tregs 0 k) s u
  | 0, _ => WP.block_nil ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _), Kp.refl _ _⟩
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    refine WP.block_append (WP.mono (rzero_ok (k := k) (by omega)) fun s₁ ⟨M₁, Z₁, K₁⟩ => ?_)
    refine wp_step (exec_li (by decide)) (WP.block_nil ?_)
    refine ⟨M₁, fun j hj => ?_, (K₁.mono fun r hr => by rw [tregs_succ]; exact List.mem_append_left _ hr).trans
      (Kp.write _ _ (by rw [tregs_succ, Nat.zero_add]; exact List.mem_append_right _ (List.mem_singleton_self _)))⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [write_gpr]; simp only [treg_ne_of (by omega) (by omega) (Nat.ne_of_lt hj), ite_false]; exact Z₁ j hj
    · rw [write_gpr]; simp only [ite_true]; rfl

theorem rrestore_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {acc : Nat}
    (h3 : At s base .r3 0) (hacc4 : acc % 4 = 0) : ∀ {k : Nat}, k ≤ 10 → acc + 8 * k ≤ size →
    WP isa (.block ((List.range k).map fun j => .load .d (treg j) wb (acc + 8 * j))) s
      fun u => u.mem = s.mem ∧ (∀ j < k, u.gpr (treg j) = word s.mem base (acc + 8 * j)) ∧ Kp (tregs 0 k) s u
  | 0, _, _ => WP.block_nil ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _), Kp.refl _ _⟩
  | k + 1, hk, hka => by
    have hs15 := hs.small
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    refine WP.block_append (WP.mono (rrestore_ok hs h3 hacc4 (k := k) (by omega) (by omega)) fun s₁ ⟨M₁, Z₁, K₁⟩ => ?_)
    refine wp_step (ld0_ok (K₁.ws hs) (K₁.at h3 (by simp [tregs])) (by decide) (by omega) (d := acc + 8 * k) (by omega))
      (WP.block_nil ?_)
    refine ⟨M₁, fun j hj => ?_, (K₁.mono fun r hr => by rw [tregs_succ]; exact List.mem_append_left _ hr).trans
      (Kp.write _ _ (by rw [tregs_succ, Nat.zero_add]; exact List.mem_append_right _ (List.mem_singleton_self _)))⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [write_gpr]; simp only [treg_ne_of (by omega) (by omega) (Nat.ne_of_lt hj), ite_false]; exact Z₁ j hj
    · rw [write_gpr]; simp only [ite_true]; rw [M₁]

/-! ## The multiplication -/

theorem regsVal_zero_of {s : State} {d : Nat} : ∀ {k : Nat}, (∀ j < k, s.gpr (treg (d + j)) = 0) → regsVal s d k = 0
  | 0, _ => rfl
  | k + 1, h => by
    rw [regsVal_succ_top, regsVal_zero_of fun j hj => h j (by omega), h k (by omega)]; rfl

theorem rclob_eq (n : Nat) : rclob n = opClob ++ tregs 0 (n + 1) := rfl

/-- `[r4] = [r5] [r6] R⁻¹ mod m`, for `[r6]` below `m`, with the
accumulator in registers. -/
theorem rmul_ok {M : Mod} {base : Addr} {size acc O A B m : Nat} {s : State} (hp : OpPre M base size O A B m s)
    (hL : OpLay M size acc O A B) (hn9 : M.n ≤ 9) (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0)
    (hb : wordsVal s.mem base B M.n < m) :
    WP isa (rmul M acc) s fun u =>
      wordsVal u.mem base O M.n < m ∧
      wordsVal u.mem base O M.n * 2 ^ (64 * M.n) % m = wordsVal s.mem base A M.n * wordsVal s.mem base B M.n % m ∧
      Outs base (opOuts M acc O) s.mem u.mem ∧ Kp opClob s u := by
  have hn := hp.ws.nowrap
  have hs15 := hp.ws.small
  have hL' := hL
  obtain ⟨n0, acc_le, tmp_le, mo_le, o_le, a_le, b_le, acc4, tmp4, sat, am, ao, aa, ab, tm, to⟩ := hL'
  have hmi4 : (acc + 8 * (M.n + 1)) % 4 = 0 := by omega
  have hRL : RMulLay M size (acc + 8 * (M.n + 1)) A B := ⟨n0, hn9, by omega, hmi4, a_le, b_le, mo_le⟩
  refine WP.seq ?_
  simp only [rsave, rzero, List.append_assoc]
  -- `m'` above the saved registers.
  refine WP.block_append (WP.mono (setConst_ok hp.ws hp.r3 (n := 1) (o := acc + 8 * (M.n + 1)) (x := M.minv.toNat)
    (by omega) M.minv.isLt) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  refine WP.block_append (WP.mono (rsave_ok (K₁.ws hp.ws) (K₁.at hp.r3) acc4 (acc := acc) (k := M.n + 1) (by omega))
    fun s₂ ⟨O₂, Z₂, K₂, G₂⟩ => ?_)
  refine WP.block_append (WP.mono (rzero_ok (s := s₂) (k := M.n + 1) (by omega)) fun s₃ ⟨M₃, Z₃, K₃⟩ => ?_)
  have h3₃ : At s₃ base .r3 0 := by rw [At, K₃.gpr _ (by simp [tregs]), G₂, K₁.g]; exact hp.r3
  refine wp_step (setMo_ok h3₃ (by omega)) ?_
  refine wp_step (exec_li (by omega)) (WP.block_nil ?_)
  generalize hu : (s₃.write .r7 (off base M.mo)).write .r8 (BitVec.ofNat 64 M.n) = u
  have hum : u.mem = s₂.mem := by rw [← hu]; exact M₃
  have keep : ∀ r : Reg, r ∉ [Reg.r7, .r8, .r11] → r ∉ hiRegs → u.gpr r = s.gpr r := by
    intro r h1 h2
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1
    rw [← hu]
    simp only [write_gpr, h1.1, h1.2.1, ite_false]
    rw [K₃.gpr _ (fun h => by obtain ⟨j, -, e⟩ := List.mem_map.mp h; exact h2 (e ▸ treg_hi _)), G₂, K₁.gpr _ (by simp [h1.2.2])]
  have K₀u : Kp ([.r7, .r8, .r11] ++ tregs 0 (M.n + 1)) s u := by
    rw [← hu]
    exact (((K₁.mono (by intro r hr; simp at hr; simp [hr])).trans (K₂.mono (by simp))).trans
      (K₃.mono fun r hr => List.mem_append_right _ hr)).trans
      ((Kp.write _ _ (by simp)).trans (Kp.write _ _ (by simp)))
  have Ous : Outs base (opOuts M acc O) s.mem u.mem := by
    rw [hum]
    have o₁ : Outs base (opOuts M acc O) s.mem s₁.mem :=
      Outs.of_outside (O₁.mono (o' := acc) (n' := 4 * (4 * M.n + 2)) (by omega) (by omega))
        (List.mem_cons_self ..)
    have o₂ : Outs base (opOuts M acc O) s₁.mem s₂.mem :=
      Outs.of_outside (O₂.mono (o' := acc) (n' := 4 * (4 * M.n + 2)) (Nat.le_refl _) (by omega))
        (List.mem_cons_self ..)
    exact o₁.trans o₂
  have hmi : (word u.mem base (acc + 8 * (M.n + 1))).toNat = M.minv.toNat := by
    rw [hum, O₂.word (by omega) (by omega), ← V₁, ← wordsVal_eq_val32]
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero]
  have hmu : wordsVal u.mem base M.mo M.n = m := by
    rw [hum, O₂.wordsVal (by omega) (by omega), O₁.wordsVal (by omega) (by omega), wordsVal_eq_val32, hp.mo]
  have hAu : wordsVal u.mem base A M.n = wordsVal s.mem base A M.n := by
    rw [hum, O₂.wordsVal (by omega) (by omega), O₁.wordsVal (by omega) (by omega)]
  have hBu : wordsVal u.mem base B M.n = wordsVal s.mem base B M.n := by
    rw [hum, O₂.wordsVal (by omega) (by omega), O₁.wordsVal (by omega) (by omega)]
  have hsv : ∀ j < M.n + 1, word u.mem base (acc + 8 * j) = s.gpr (treg j) := fun j hj => by
    rw [hum, Z₂ j hj, K₁.gpr _ (by simp)]
  have hws : Ws u base size := K₀u.ws hp.ws
  have hz : regsVal u 0 (M.n + 1) = 0 := by
    have : ∀ j < M.n + 1, u.gpr (treg (0 + j)) = 0 := fun j hj => by
      rw [← hu, Nat.zero_add]; simp only [write_gpr, treg_eq_r7, treg_eq_r8, ite_false]; exact Z₃ j hj
    exact regsVal_zero_of this
  -- The invariant at word 0.
  have h0 : RLoopInv base M A B m 0 u u := by
    refine ⟨?_, ?_, ?_, ?_, ?_, rfl, Kp.refl _ _, ?_, ?_⟩
    · rw [At, keep _ (by decide) (by decide)]; exact hp.r3
    · rw [Nat.mul_zero, Nat.add_zero, At, keep _ (by decide) (by decide)]; exact hp.r5
    · rw [At, keep _ (by decide) (by decide)]; exact hp.r6
    · rw [At, ← hu]; simp only [write_gpr, reduceCtorEq, ite_false, ite_true]
    · rw [← hu]; simp only [write_gpr, ite_true, Nat.sub_zero]
    · rw [hz]; have := hp.m0; omega
    · exact ⟨0, by rw [hz]; simp [wordsVal]⟩
  refine WP.seq (WP.mono (rloop_ok hws hRL hmu (by rw [hmi]; exact hinv) (by rw [hBu]; exact hb) h0) fun t I => ?_)
  -- The reduction, and the registers restored.
  obtain ⟨U, hU⟩ := I.cong
  have hmt : wordsVal t.mem base M.mo M.n = m := by rw [I.mem, hmu]
  have h4t : At t base .r4 O := by
    rw [At, I.kp.gpr _ (rclob_not_hi (by decide) (by decide) _), keep _ (by decide) (by decide)]; exact hp.r4
  refine WP.block_append (WP.mono (rcsub_ok (I.kp.ws hws) I.r3 h4t I.r7
    ⟨tmp_le, mo_le, o_le, tmp4, tm.symm, to⟩ n0 hmt I.lt) fun v ⟨V₃, O₃, K₃⟩ => ?_)
  refine WP.mono (rrestore_ok (K₃.ws (I.kp.ws hws)) (K₃.at I.r3) acc4 (k := M.n + 1) (by omega) (by omega))
    fun w ⟨M₄, R₄, K₄⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [M₄, V₃]; exact Nat.mod_lt _ hp.m0
  · rw [M₄, V₃, Nat.mod_mul_mod, Nat.mul_comm, hU, hAu, hBu, Nat.add_mul_mod_self_right]
  · rw [M₄]
    refine (Ous.trans ?_).trans (outs_tail O₃)
    rw [I.mem]; exact Outs.refl _ _ _
  · -- Every register but `opClob` is the caller's: the accumulator's are restored.
    have hrest : ∀ j < M.n + 1, w.gpr (treg j) = s.gpr (treg j) := fun j hj => by
      rw [R₄ j hj, ← hsv j hj]
      have : word v.mem base (acc + 8 * j) = word t.mem base (acc + 8 * j) := by
        exact Outs.word O₃ (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> dsimp only <;> omega) (by omega)
      rw [this, I.mem]
    have Kall : Kp (opClob ++ tregs 0 (M.n + 1)) s w :=
      ((K₀u.mono fun r hr => by
          rcases List.mem_append.mp hr with h | h
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl | rfl <;> simp [opClob]
          · exact List.mem_append_right _ h).trans
        (I.kp.mono fun r hr => by rw [← rclob_eq]; exact hr)).trans
        ((K₃.mono fun r hr => List.mem_append_left _ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl <;> decide)).trans (K₄.mono fun r hr => List.mem_append_right _ hr))
    refine ⟨fun r hr => ?_, Kall.rd, Kall.wr, Kall.sp, Kall.lr⟩
    by_cases ht : r ∈ tregs 0 (M.n + 1)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
      rw [List.mem_range] at hj
      rw [Nat.zero_add]; exact hrest j hj
    · exact Kall.gpr r (fun h => (List.mem_append.mp h).elim hr ht)

end VG.Proof.Mont.PPC64LE
