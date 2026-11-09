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
theorem regsVal_congr' {s t : State} {d d' k : Nat}
    (h : ∀ j < k, t.gpr (treg (d + j)) = s.gpr (treg (d' + j))) : regsVal t d k = regsVal s d' k := by
  induction k generalizing d d' with
  | zero => rfl
  | succ k ih =>
    simp only [regsVal]
    have h0 := h 0 (by omega)
    rw [Nat.add_zero, Nat.add_zero] at h0
    rw [h0, ih fun j hj => by
      have := h (j + 1) (by omega)
      rwa [show d + (j + 1) = d + 1 + j by omega, show d' + (j + 1) = d' + 1 + j by omega] at this]

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

/-! ## The reduction row of a Mersenne modulus -/

theorem mersK_spec {n m : Nat} (h : 0 < mersK n m) :
    2 ≤ n ∧ mersK n m < 64 ∧ m + 1 = 2 ^ (64 * (n - 1) + mersK n m) := by
  unfold mersK at h ⊢
  split
  · rename_i k hk
    have hp := List.find?_some hk
    have hr := List.mem_of_find?_eq_some hk
    rw [List.mem_range] at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    exact ⟨hp.1.2, hr, hp.2⟩
  · rename_i hk
    rw [hk] at h
    exact absurd h (Nat.lt_irrefl 0)

/-- The accumulator moved down: `treg i = treg (i + 1)` for `i < j`. -/
theorem rmoves_ok {t : State} : ∀ {j : Nat}, j + 1 < 10 →
    WP isa (.block ((List.range j).map fun i => .ori (treg i) (treg (i + 1)) 0)) t fun u =>
      (∀ i < j, u.gpr (treg i) = t.gpr (treg (i + 1))) ∧ u.mem = t.mem ∧ Kp (tregs 0 j) t u
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, Kp.refl _ _⟩
  | j + 1, hj => by
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    refine WP.block_append (WP.mono (rmoves_ok (t := t) (j := j) (by omega)) fun t₁ ⟨V₁, M₁, K₁⟩ => ?_)
    refine wp_step exec_ori (WP.block_nil ?_)
    have hj1 : t₁.gpr (treg (j + 1)) = t.gpr (treg (j + 1)) :=
      K₁.gpr _ (treg_not_mem_tregs (by omega) (by omega) (by omega))
    refine ⟨fun i hi => ?_, by rw [write_mem, M₁], (K₁.mono fun r hr => by
        rw [tregs_succ]; exact List.mem_append_left _ hr).trans
      (Kp.write _ _ (by rw [tregs_succ]; exact List.mem_append_right _ (by simp)))⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [write_gpr]
      simp only [treg_ne_of (show i < 10 by omega) (show j < 10 by omega) (by omega), ite_false]
      exact V₁ i hi
    · rw [write_gpr]
      simp only [ite_true, hj1]
      simp

/-- The three top words: `treg e = treg (e + 1) + r10`, then
`treg (e + 1) = treg (e + 2) + r0`, `treg (e + 2) = r12`, with the carries. -/
theorem rtopF_ok {s : State} {e : Nat} (he : e + 2 < 10) :
    WP isa (.block [.addc (treg e) (treg (e + 1)) .r10, .adde (treg (e + 1)) (treg (e + 2)) .r0,
        .addze (treg (e + 2)) .r12]) s fun u =>
      (u.gpr (treg e)).toNat + 2 ^ 64 * (u.gpr (treg (e + 1))).toNat + 2 ^ 128 * (u.gpr (treg (e + 2))).toNat +
          2 ^ 192 * u.ca.toNat =
        (s.gpr (treg (e + 1))).toNat + (s.gpr .r10).toNat + 2 ^ 64 * ((s.gpr (treg (e + 2))).toNat + (s.gpr .r0).toNat) +
          2 ^ 128 * (s.gpr .r12).toNat ∧
      u.mem = s.mem ∧ Kp [treg e, treg (e + 1), treg (e + 2)] s u := by
  refine wp_step exec_addc ?_
  refine wp_step exec_adde ?_
  refine wp_step exec_addze (WP.block_nil ?_)
  have h01 : treg e ≠ treg (e + 1) := treg_ne_of (by omega) (by omega) (by omega)
  have h02 : treg e ≠ treg (e + 2) := treg_ne_of (by omega) (by omega) (by omega)
  have h12 : treg (e + 1) ≠ treg (e + 2) := treg_ne_of (by omega) (by omega) (by omega)
  simp only [writeCarry_gpr, RegUpd.mem_writeCarry, RegUpd.ca_writeCarry, ite_true, h01, h02, h12, h01.symm,
    h02.symm, h12.symm, ite_false, r0_eq_treg, r12_eq_treg]
  refine ⟨?_, trivial, ?_⟩
  · simp only [BitVec.toNat_ofNat]
    have ha := (s.gpr (treg (e + 1))).isLt
    have hb := (s.gpr .r10).isLt
    have hc := (s.gpr (treg (e + 2))).isLt
    have hd := (s.gpr .r0).isLt
    have hf := (s.gpr .r12).isLt
    generalize (s.gpr (treg (e + 1))).toNat = a at *
    generalize (s.gpr .r10).toNat = b at *
    generalize (s.gpr (treg (e + 2))).toNat = c at *
    generalize (s.gpr .r0).toNat = d at *
    generalize (s.gpr .r12).toNat = f at *
    have h1 := ca_split (v := a + b) (by omega)
    generalize (decide (2 ^ 64 ≤ a + b)).toNat = c1 at *
    have h2 := ca_split (v := c + d + c1) (by omega)
    generalize (decide (2 ^ 64 ≤ c + d + c1)).toNat = c2 at *
    have h3 := ca_split (v := f + c2) (by omega)
    generalize (decide (2 ^ 64 ≤ f + c2)).toNat = c3 at *
    omega
  · refine ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [writeCarry_gpr, hr.1, hr.2.1, hr.2.2, ite_false]

/-- The arithmetic of `rredF_ok`, over the word base `B = 2⁶⁴`: the words
`a`, `b`, `d` (and the carry out `c`) of the top three are the sum, so
`B T' = T₁ + t₀ m`. -/
theorem redF_math {T1 t0 W x y z l h m R a b d c B : Nat}
    (hT1 : T1 = t0 + B * (W + R * (x + B * y)) + B * R * (B * B) * z)
    (hm : t0 * m + t0 = B * R * (l + B * h))
    (hV : a + B * b + B * B * d + B * B * B * c = x + l + B * (y + h) + B * B * z)
    (hb : T1 + t0 * m < B * (B * R * (B * B))) :
    B * (W + R * (a + B * b + B * B * d)) = T1 + t0 * m := by
  have key : T1 + t0 * m = B * (W + R * (a + B * b + B * B * d + B * B * B * c)) :=
    calc T1 + t0 * m = (t0 * m + t0) + B * (W + R * (x + B * y)) + B * R * (B * B) * z := by rw [hT1]; grind
      _ = B * R * (l + B * h) + B * (W + R * (x + B * y)) + B * R * (B * B) * z := by rw [hm]
      _ = B * (W + R * (x + l + B * (y + h) + B * B * z)) := by grind
      _ = B * (W + R * (a + B * b + B * B * d + B * B * B * c)) := by rw [hV]
  have hc : c = 0 := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exact h0
    · exfalso
      have e : B * R * (B * B) = R * (B * B * B) := by grind
      have : B * (B * R * (B * B)) ≤ B * (W + R * (a + B * b + B * B * d + B * B * B * c)) := by
        apply Nat.mul_le_mul_left
        rw [e]
        calc R * (B * B * B) ≤ R * (B * B * B * c) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ h0)
          _ ≤ R * (a + B * b + B * B * d + B * B * B * c) := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
          _ ≤ W + R * (a + B * b + B * B * d + B * B * B * c) := Nat.le_add_left _ _
      omega
  rw [key, hc, Nat.mul_zero, Nat.add_zero]

/-- The reduction row of a Mersenne modulus `m = 2^(64 (n - 1) + k) - 1`:
`2⁶⁴ T' = T₁ + t₀ m` for the accumulator `T₁` (its top word in `r12`) and
`t₀ = T₁ mod 2⁶⁴`. -/
theorem rredF_ok {t : State} {n k m T1 : Nat} (hn : 2 ≤ n) (hn9 : n ≤ 9) (hk0 : 0 < k) (hk : k < 64)
    (hm : m + 1 = 2 ^ (64 * (n - 1) + k))
    (hT1 : T1 = regsVal t 0 (n + 1) + 2 ^ (64 * (n + 1)) * (t.gpr .r12).toNat)
    (hb : T1 + T1 % 2 ^ 64 * m < 2 ^ 64 * 2 ^ (64 * (n + 1))) :
    WP isa (.block (rredF n k)) t fun u =>
      2 ^ 64 * regsVal u 0 (n + 1) = T1 + T1 % 2 ^ 64 * m ∧ u.mem = t.mem ∧
        Kp (.r0 :: .r10 :: tregs 0 (n + 1)) t u := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
  simp only [rredF, show N + 2 - 2 = N by omega, show N + 2 - 1 = N + 1 by omega,
    List.cons_append, List.nil_append]
  refine wp_step (exec_lsl hk) ?_
  refine wp_step (exec_lsr_d (by omega)) ?_
  simp only [write_gpr, treg_eq_r10, ite_false]
  generalize hL : t.gpr (treg 0) <<< k = L
  generalize hH : t.gpr (treg 0) >>> (64 - k) = H
  refine WP.block_append (WP.mono (rmoves_ok (t := (t.write .r10 L).write .r0 H) (j := N) (by omega))
    fun t₁ ⟨V₁, M₁, K₁⟩ => ?_)
  refine WP.mono (rtopF_ok (s := t₁) (e := N) (by omega)) fun u ⟨V, Mu, K⟩ => ?_
  -- What the moves kept.
  have kt : ∀ r, r ∉ tregs 0 N → t₁.gpr r = ((t.write .r10 L).write .r0 H).gpr r := fun r h => K₁.gpr r h
  have e1 : t₁.gpr (treg (N + 1)) = t.gpr (treg (N + 1)) := by
    rw [kt _ (treg_not_mem_tregs (by omega) (by omega) (by omega))]; simp only [write_gpr, treg_eq_r0, treg_eq_r10, ite_false]
  have e2 : t₁.gpr (treg (N + 2)) = t.gpr (treg (N + 2)) := by
    rw [kt _ (treg_not_mem_tregs (by omega) (by omega) (by omega))]; simp only [write_gpr, treg_eq_r0, treg_eq_r10, ite_false]
  have e10 : t₁.gpr .r10 = L := by
    rw [kt _ (fun h => by obtain ⟨j, -, e⟩ := List.mem_map.mp h; exact treg_ne (r := .r10) (by decide) _ e)]
    simp only [write_gpr, reduceCtorEq, ite_false, ite_true]
  have e0 : t₁.gpr .r0 = H := by
    rw [kt _ (fun h => by obtain ⟨j, -, e⟩ := List.mem_map.mp h; exact treg_ne (r := .r0) (by decide) _ e)]
    simp only [write_gpr, ite_true]
  have e12 : t₁.gpr .r12 = t.gpr .r12 := by
    rw [kt _ (fun h => by obtain ⟨j, -, e⟩ := List.mem_map.mp h; exact treg_ne (r := .r12) (by decide) _ e)]
    simp only [write_gpr, reduceCtorEq, ite_false]
  rw [e1, e2, e10, e0, e12] at V
  -- The low words.
  have hlow : regsVal u 0 N = regsVal t 1 N := by
    refine regsVal_congr' fun j hj => ?_
    rw [K.gpr _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, Nat.zero_add]
      exact ⟨treg_ne_of (by omega) (by omega) (by omega), treg_ne_of (by omega) (by omega) (by omega),
        treg_ne_of (by omega) (by omega) (by omega)⟩), Nat.zero_add, V₁ j hj]
    simp only [write_gpr, treg_eq_r0, treg_eq_r10, ite_false, Nat.add_comm 1 j]
  have hu : regsVal u 0 (N + 3) = regsVal u 0 N + 2 ^ (64 * N) * ((u.gpr (treg N)).toNat +
      2 ^ 64 * (u.gpr (treg (N + 1))).toNat + 2 ^ 128 * (u.gpr (treg (N + 2))).toNat) := by
    rw [regsVal_append u 0 N 3]
    simp only [regsVal, Nat.zero_add, Nat.mul_zero, Nat.add_zero]
    rw [show N + 1 + 1 = N + 2 by omega]
    grind
  have ht : regsVal t 0 (N + 3) = (t.gpr (treg 0)).toNat + 2 ^ 64 * (regsVal t 1 N + 2 ^ (64 * N) *
      ((t.gpr (treg (N + 1))).toNat + 2 ^ 64 * (t.gpr (treg (N + 2))).toNat)) := by
    rw [show regsVal t 0 (N + 3) = (t.gpr (treg 0)).toNat + 2 ^ 64 * regsVal t 1 (N + 2) from rfl,
      regsVal_append t 1 N 2, regsVal_two, show 1 + N = N + 1 by omega, show N + 1 + 1 = N + 2 by omega]
  -- The shift: `t₀ 2^k = L + 2⁶⁴ H`.
  have hLH : (t.gpr (treg 0)).toNat * 2 ^ k = L.toNat + 2 ^ 64 * H.toNat := by
    rw [← hL, ← hH, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    have e : (t.gpr (treg 0)).toNat * 2 ^ k / 2 ^ 64 = (t.gpr (treg 0)).toNat / 2 ^ (64 - k) := by
      rw [show (2 : Nat) ^ 64 = 2 ^ (64 - k) * 2 ^ k by rw [← Nat.pow_add]; congr 1; omega,
        Nat.mul_div_mul_right _ _ (Nat.two_pow_pos k)]
    rw [← e, Nat.mod_add_div]
  have ht0 : T1 % 2 ^ 64 = (t.gpr (treg 0)).toNat := by
    rw [hT1, show 64 * (N + 2 + 1) = 64 + 64 * (N + 2) by omega, Nat.pow_add, Nat.mul_assoc,
      Nat.add_mul_mod_self_left, regsVal_low]
  rw [ht0]
  rw [ht0] at hb
  refine ⟨?_, by rw [Mu, M₁]; rfl, ?_⟩
  · have hm' : (t.gpr (treg 0)).toNat * m + (t.gpr (treg 0)).toNat =
        2 ^ 64 * 2 ^ (64 * N) * (L.toNat + 2 ^ 64 * H.toNat) := by
      rw [← hLH, ← Nat.mul_add_one, hm, show N + 2 - 1 = N + 1 by omega, Nat.pow_add,
        show 64 * (N + 1) = 64 + 64 * N by omega, Nat.pow_add]
      grind
    rw [show N + 2 + 1 = N + 3 by omega, ht,
      show 64 * (N + 3) = 64 + 64 * N + 128 by omega, Nat.pow_add, Nat.pow_add] at hT1
    rw [show N + 2 + 1 = N + 3 by omega, show 64 * (N + 3) = 64 + 64 * N + 128 by omega, Nat.pow_add,
      Nat.pow_add] at hb
    rw [show N + 2 + 1 = N + 3 by omega, hu, hlow]
    rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by rw [← Nat.pow_add]] at hT1 hb V ⊢
    rw [show (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 by rw [← Nat.pow_add, ← Nat.pow_add]] at V
    generalize (2 : Nat) ^ 64 = B at *
    generalize 2 ^ (64 * N) = R at *
    exact redF_math hT1 hm' V hb
  · refine ((Kp.write t _ (by simp)).trans (Kp.write _ _ (by simp))).trans ((K₁.mono fun r hr => ?_).trans
      (K.mono fun r hr => ?_))
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      rw [List.mem_range] at hj
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (treg_mem_tregs (d := 0) (by omega)))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (by
          simpa using treg_mem_tregs (d := 0) (k := N + 2 + 1) (by omega)))

/-- The general reduction row (`rrowG`): `2⁶⁴ T' = T₁ + q m` for some `q`,
the accumulator `T₁` with its top word in `r12`. -/
theorem rredG_ok {t₃ : State} {base : Addr} {size : Nat} {M : Mod} {acc a b m T1 : Nat} {sm : Mem}
    (ht₃ : Ws t₃ base size) (h3₃ : At t₃ base .r3 0) (h7₃ : At t₃ base .r7 M.mo)
    (hL : RMulLay M size (acc + 8 * (M.n + 1)) a b) (hmem₃ : t₃.mem = sm) (hm : wordsVal sm base M.mo M.n = m)
    (hinv : (m * (word sm base (acc + 8 * (M.n + 1))).toNat + 1) % 2 ^ 64 = 0)
    (hT1v : regsVal t₃ 0 (M.n + 1) + 2 ^ (64 * (M.n + 1)) * (t₃.gpr .r12).toNat = T1)
    (hrowb : ∀ q < 2 ^ 64, T1 + q * m < 2 ^ 64 * (2 * m)) :
    WP isa (.block (rrowG M acc)) t₃ fun t₆ => ∃ q, q < 2 ^ 64 ∧ 2 ^ 64 * regsVal t₆ 0 (M.n + 1) = T1 + q * m ∧
      t₆.mem = t₃.mem ∧ Kp (([.r0, .r9, .r10, .r11, .r12] : List Reg) ++ tregs 0 (M.n + 1)) t₃ t₆ := by
  have hs15 := ht₃.small
  obtain ⟨n0, n9, mi_le, mi4, a_le, b_le, mo_le⟩ := hL
  obtain ⟨N, hN⟩ : ∃ N, M.n = N + 1 := ⟨M.n - 1, by omega⟩
  generalize hc₃ : (t₃.gpr .r12).toNat = c₃ at hT1v
  simp only [rrowG, List.append_assoc]
  refine WP.block_append (WP.mono (rqStart_ok ht₃ h3₃ h7₃ (mi := acc + 8 * (M.n + 1)) mi4 mi_le (by omega))
    fun t₄ ⟨q₄, ⟨lo, hlo, V₄⟩, M₄, K₄⟩ => ?_)
  have ht0 : (t₃.gpr (treg 0)).toNat = T1 % 2 ^ 64 := by
    rw [← hT1v, show 64 * (M.n + 1) = 64 + 64 * M.n by omega, Nat.pow_add, Nat.mul_assoc, Nat.add_mul_mod_self_left,
      regsVal_low]
  rw [hmem₃, ht0] at q₄
  rw [hmem₃, ht0] at V₄
  generalize hq : (t₄.gpr .r9).toNat = q at q₄ V₄
  have hq64 : q < 2 ^ 64 := hq ▸ BitVec.isLt _
  generalize hM' : wordsVal sm base (M.mo + 8) N = M'
  have hmM : m = (word sm base M.mo).toNat + 2 ^ 64 * M' := by
    rw [← hm, ← hM', hN]; rfl
  have hlo0 : lo = 0 := by
    have hl := mont_low (T1 % 2 ^ 64) (word sm base (acc + 8 * (M.n + 1))).toNat m hinv
    rw [← q₄, hmM] at hl
    have : (lo + 2 ^ 64 * (t₄.gpr .r0).toNat) % 2 ^ 64 = lo := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
    rw [V₄] at this
    rw [← this]
    have e : T1 % 2 ^ 64 + q * ((word sm base M.mo).toNat + 2 ^ 64 * M') =
      (q * (word sm base M.mo).toNat + T1 % 2 ^ 64) + 2 ^ 64 * (q * M') := by grind
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
  refine WP.mono this fun t₆ ⟨V₆, M₆, K₆⟩ => ?_
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
  have hrow := hrowb q hq64
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
      omega
  rw [hca, Nat.mul_zero, Nat.add_zero] at hmath
  refine ⟨q, hq64, hmath, by rw [M₆, M₅, M₄], ?_⟩
  refine ((K₄.mono fun r hr => ?_).trans (K₅.mono fun r hr => ?_)).trans (K₆.mono fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp
  · rcases List.mem_append.mp hr with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> simp
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
      rw [List.mem_range] at hj
      exact List.mem_append_right _ (by simpa using treg_mem_tregs (d := 0) (k := M.n + 1) (j := 0 + j) (by omega))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      exact List.mem_append_right _ (by simpa using treg_mem_tregs (d := 0) (k := M.n + 1) (by omega))

/-- The reduction row (`rrowM`): `rredF` for a Mersenne modulus, else `rrowG`. -/
theorem rred_ok {t₃ : State} {base : Addr} {size : Nat} {M : Mod} {acc a b m T1 : Nat} {sm : Mem}
    (ht₃ : Ws t₃ base size) (h3₃ : At t₃ base .r3 0) (h7₃ : At t₃ base .r7 M.mo)
    (hL : RMulLay M size (acc + 8 * (M.n + 1)) a b) (hmem₃ : t₃.mem = sm) (hm : wordsVal sm base M.mo M.n = m)
    (hinv : (m * (word sm base (acc + 8 * (M.n + 1))).toNat + 1) % 2 ^ 64 = 0)
    (hT1v : regsVal t₃ 0 (M.n + 1) + 2 ^ (64 * (M.n + 1)) * (t₃.gpr .r12).toNat = T1)
    (hrowb : ∀ q < 2 ^ 64, T1 + q * m < 2 ^ 64 * (2 * m)) :
    WP isa (.block (rrowM M m acc)) t₃ fun t₆ => ∃ q, q < 2 ^ 64 ∧ 2 ^ 64 * regsVal t₆ 0 (M.n + 1) = T1 + q * m ∧
      t₆.mem = t₃.mem ∧ Kp (([.r0, .r9, .r10, .r11, .r12] : List Reg) ++ tregs 0 (M.n + 1)) t₃ t₆ := by
  unfold rrowM
  split
  · rename_i hF
    obtain ⟨hn2, hk64, hmk⟩ := mersK_spec hF
    have hmlt : m < 2 ^ (64 * M.n) := by rw [← hm]; exact wordsVal_lt _ _ _ _
    have hb : T1 + T1 % 2 ^ 64 * m < 2 ^ 64 * 2 ^ (64 * (M.n + 1)) := by
      have := hrowb (T1 % 2 ^ 64) (Nat.mod_lt _ (by decide))
      have : 2 ^ 64 * (2 * m) ≤ 2 ^ 64 * 2 ^ (64 * (M.n + 1)) := Nat.mul_le_mul_left _ (by
        rw [show 64 * (M.n + 1) = 64 * M.n + 64 by omega, Nat.pow_add]
        have : 2 ≤ 2 ^ 64 := by decide
        have := Nat.mul_le_mul_left (2 ^ (64 * M.n)) this
        omega)
      omega
    refine WP.mono (rredF_ok hn2 hL.n9 hF hk64 hmk hT1v.symm hb) fun u ⟨V, Mu, K⟩ =>
      ⟨T1 % 2 ^ 64, Nat.mod_lt _ (by decide), V, Mu, K.mono fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · simp
    rcases List.mem_cons.mp hr with rfl | hr
    · simp
    exact List.mem_append_right _ hr
  · exact rredG_ok ht₃ h3₃ h7₃ hL hmem₃ hm hinv hT1v hrowb

theorem rrow_eq (M : Mod) (m acc : Nat) : rrow M m acc =
    ([.load .d .r9 .r5 0, .li .r0 0] : List Instr) ++ (rmacs .r6 0 0 0 M.n ++
    (([.addc (treg M.n) (treg M.n) .r0, .li .r12 0, .addze .r12 .r12] : List Instr) ++
    (rrowM M m acc ++ ([.addi .r5 .r5 8, .subi .r8 .r8 1] : List Instr)))) := by
  simp only [rrow, rrowB, List.append_assoc]

/-- An iteration of the loop. -/
theorem rrow_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {acc a b m k : Nat}
    (hL : RMulLay M size (acc + 8 * (M.n + 1)) a b) (hk : k < M.n) (hm : wordsVal s.mem base M.mo M.n = m)
    (hinv : (m * (word s.mem base (acc + 8 * (M.n + 1))).toNat + 1) % 2 ^ 64 = 0)
    (hB : wordsVal s.mem base b M.n < m) {t : State} (I : RLoopInv base M a b m k s t) :
    WP isa (.block (rrow M m acc)) t fun u => RLoopInv base M a b m (k + 1) s u := by
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
  -- The reduction row.
  have ht₃ := K₁₃.ws ht
  have h3₃ : At t₃ base .r3 0 := K₁₃.at I.r3 (rclob_not_hi (by decide) (by decide) _)
  have h7₃ : At t₃ base .r7 M.mo := by
    rw [At, K₃.gpr _ (by simp), K₂.gpr _ (by simp [tregs]), write_gpr, write_gpr]; simp only [reduceCtorEq, ite_false]
    exact I.r7
  have hmem₃ : t₃.mem = s.mem := by rw [M₃, M₂, I.mem]
  have hrowb : ∀ q < 2 ^ 64, T1 + q * m < 2 ^ 64 * (2 * m) := fun q hq => by
    rw [hT1]; exact row_lt (by rw [← hT]; exact I.lt) u.isLt hB hq
  rw [← hc₃] at hT1v
  refine WP.block_append (WP.mono (rred_ok ht₃ h3₃ h7₃ ⟨n0, n9, mi_le, mi4, a_le, b_le, mo_le⟩ hmem₃ hm hinv hT1v
    hrowb) fun t₆ ⟨q, hq64, hmath, M₆, K₃₆'⟩ => ?_)
  refine wp_step (exec_addi (by decide) (by decide)) ?_
  refine wp_step (exec_subi (by decide) (by decide)) (WP.block_nil ?_)
  have hrow := hrowb q hq64
  rw [hT1] at hmath hrow
  have K₃₆ : Kp (rclob M.n) t₃ t₆ := K₃₆'.mono (sub_rclob (by decide) (by omega))
  have K₁₆ := K₁₃.trans K₃₆
  have keep : ∀ r : Reg, r ∉ [Reg.r0, .r9, .r10, .r11, .r12] → r ∉ hiRegs → t₆.gpr r = t.gpr r := by
    intro r h1 h2
    rw [K₃₆'.gpr r (nm_tregs h1 h2 _ _)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1
    obtain ⟨a0, a9, a10, a11, a12⟩ := h1
    rw [K₃.gpr r (nm_treg h2 _ (by simp [a12])), K₂.gpr r (nm_tregs (by simp [a0, a10, a11]) h2 _ _)]
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
  · simp only [write_mem]; rw [M₆, hmem₃]
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
    WP isa (.loop (.block (rrow M m acc)) (.nonzero .d .r8)) t fun u => RLoopInv base M a b m M.n s u := by
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
    WP isa (rmul M m acc) s fun u =>
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

/-! ## The multiplication of at most four words: the carry chains -/

/-- The number in the registers `f 0`, …, `f (k - 1)`. -/
def gval (s : State) (f : Nat → Reg) : Nat → Nat
  | 0 => 0
  | k + 1 => gval s f k + 2 ^ (64 * k) * (s.gpr (f k)).toNat

/-- The low (or high) words of `x · y_j`, as a number. -/
def pv (hi : Bool) (x : Nat) (s : State) (f : Nat → Reg) : Nat → Nat
  | 0 => 0
  | k + 1 => pv hi x s f k + 2 ^ (64 * k) *
      (if hi then x * (s.gpr (f k)).toNat / 2 ^ 64 else x * (s.gpr (f k)).toNat % 2 ^ 64)

theorem pv_split (x : Nat) (s : State) (f : Nat → Reg) :
    ∀ k, pv false x s f k + 2 ^ 64 * pv true x s f k = x * gval s f k
  | 0 => rfl
  | k + 1 => by
    simp only [pv, gval, ite_true, Bool.false_eq_true, ite_false]
    have ih := pv_split x s f k
    have e := Nat.mod_add_div (x * (s.gpr (f k)).toNat) (2 ^ 64)
    generalize 2 ^ (64 * k) = P at *
    generalize x * (s.gpr (f k)).toNat % 2 ^ 64 = l at *
    generalize x * (s.gpr (f k)).toNat / 2 ^ 64 = h at *
    rw [Nat.mul_add x, ← ih, Nat.mul_left_comm x, ← e]
    grind

theorem gval_lt' (s : State) (f : Nat → Reg) : ∀ k, gval s f k < 2 ^ (64 * k)
  | 0 => Nat.one_pos
  | k + 1 => by
    rw [gval, pow64_succ]
    have := gval_lt' s f k
    have := (s.gpr (f k)).isLt
    have : 2 ^ (64 * k) * (s.gpr (f k)).toNat ≤ 2 ^ (64 * k) * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
    have : 2 ^ (64 * k) * (2 ^ 64 - 1) + 2 ^ (64 * k) = 2 ^ 64 * 2 ^ (64 * k) := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
      have : 2 ^ (64 * k) ≤ 2 ^ (64 * k) * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
      omega
    omega

theorem gval_congr {s t : State} {f : Nat → Reg} {k : Nat} (h : ∀ j < k, t.gpr (f j) = s.gpr (f j)) :
    gval t f k = gval s f k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [gval, gval, ih fun j hj => h j (by omega), h k (by omega)]

theorem pv_congr {s t : State} {hi : Bool} {x : Nat} {f : Nat → Reg} {k : Nat}
    (h : ∀ j < k, t.gpr (f j) = s.gpr (f j)) : pv hi x t f k = pv hi x s f k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pv, pv, ih fun j hj => h j (by omega), h k (by omega)]

theorem pv_lt (hi : Bool) {x : Nat} (hx : x < 2 ^ 64) (s : State) (f : Nat → Reg) :
    ∀ k, pv hi x s f k < 2 ^ (64 * k)
  | 0 => Nat.one_pos
  | k + 1 => by
    rw [pv, pow64_succ]
    have hw : (if hi then x * (s.gpr (f k)).toNat / 2 ^ 64 else x * (s.gpr (f k)).toNat % 2 ^ 64) < 2 ^ 64 := by
      split
      · have := (s.gpr (f k)).isLt
        have : x * (s.gpr (f k)).toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hx this
        exact Nat.div_lt_of_lt_mul this
      · exact Nat.mod_lt _ (by decide)
    have := pv_lt hi hx s f k
    have : 2 ^ (64 * k) * (if hi then x * (s.gpr (f k)).toNat / 2 ^ 64 else x * (s.gpr (f k)).toNat % 2 ^ 64) ≤
        2 ^ (64 * k) * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
    have : 2 ^ (64 * k) * (2 ^ 64 - 1) + 2 ^ (64 * k) = 2 ^ 64 * 2 ^ (64 * k) := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm]; have := Nat.one_le_two_pow (n := 64 * k)
      have : 2 ^ (64 * k) ≤ 2 ^ (64 * k) * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
      omega
    omega

theorem pass_succ (hi : Bool) (y : Nat → Reg) (dd ds k : Nat) :
    pass hi y dd ds (k + 1) = pass hi y dd ds k ++ passStep hi y dd ds k := by
  simp only [pass, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- A chain: the low (or high) words of `r9 · y_j` added with the carry into
`treg (ds + j)`, to `treg (dd + j)` (`dd ≤ ds`), the carry out to CA. -/
theorem pass_ok {s : State} {hi : Bool} {y : Nat → Reg} {dd ds W : Nat} (hle : dd ≤ ds) (hW : ds + W ≤ 10)
    (hy : ∀ j < W, y j ≠ .r11 ∧ y j ≠ .r9 ∧ ∀ i < W, y j ≠ treg (dd + i)) :
    ∀ {k : Nat}, k ≤ W →
    WP isa (.block (pass hi y dd ds k)) s fun u =>
      regsVal u dd k + 2 ^ (64 * k) * cOf false k u.ca = regsVal s ds k + pv hi (s.gpr .r9).toNat s y k ∧
      u.mem = s.mem ∧ Kp (.r11 :: tregs dd k) s u
  | 0, _ => WP.block_nil ⟨by simp [regsVal, pv, cOf], rfl, Kp.refl _ _⟩
  | k + 1, hk => by
    rw [pass_succ]
    refine WP.block_append (WP.mono (pass_ok hle hW hy (k := k) (by omega)) fun s₁ ⟨V₁, M₁, K₁⟩ => ?_)
    obtain ⟨y11, y9, yh⟩ := hy k (by omega)
    have nt : ∀ r : Reg, r ∉ hiRegs → r ≠ .r11 → r ∉ (.r11 :: tregs dd k) := fun r h1 h2 =>
      fun h => by
        rcases List.mem_cons.mp h with e | e
        · exact h2 e
        · obtain ⟨j, -, e'⟩ := List.mem_map.mp e; exact h1 (e' ▸ treg_hi _)
    have h9 : s₁.gpr .r9 = s.gpr .r9 := K₁.gpr _ (nt _ (by decide) (by decide))
    have hyk : s₁.gpr (y k) = s.gpr (y k) := K₁.gpr _ (by
      intro h
      rcases List.mem_cons.mp h with e | e
      · exact y11 e
      · obtain ⟨j, hj, e'⟩ := List.mem_map.mp e
        rw [List.mem_range] at hj
        exact yh j (by omega) e'.symm)
    have htk : s₁.gpr (treg (ds + k)) = s.gpr (treg (ds + k)) := K₁.gpr _ (by
      intro h
      rcases List.mem_cons.mp h with e | e
      · exact treg_ne (r := .r11) (by decide) _ e
      · exact treg_not_mem_tregs (by omega) (by omega) (by omega) e)
    simp only [passStep]
    have hmul : ∃ v : BitVec 64, exec (if hi then Instr.mulhu .r11 .r9 (y k) else Instr.mul .r11 .r9 (y k)) s₁ =
        some (s₁.write .r11 v) ∧ v.toNat = (if hi then (s.gpr .r9).toNat * (s.gpr (y k)).toNat / 2 ^ 64 else
          (s.gpr .r9).toNat * (s.gpr (y k)).toNat % 2 ^ 64) := by
      cases hi
      · refine ⟨_, exec_mul, ?_⟩
        simp only [Bool.false_eq_true, ite_false, BitVec.toNat_mul, h9, hyk]
      · refine ⟨_, exec_mulhu, ?_⟩
        simp only [ite_true, BitVec.toNat_ofNat, h9, hyk]
        have := (s.gpr (y k)).isLt
        have : (s.gpr .r9).toNat * (s.gpr (y k)).toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' (s.gpr .r9).isLt this
        exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul this)
    obtain ⟨v, hv, hvv⟩ := hmul
    refine wp_step hv ?_
    refine wp_step (exec_carryOp _ _ _ _ _ _) (WP.block_nil ?_)
    simp only [Bool.false_eq_true, ite_false, RegUpd.ca_write]
    simp only [write_gpr, treg_eq_r11, ite_false, ite_true]
    have hrk : regsVal (((s₁.write .r11 v).writeCarry (treg (dd + k)) ((s₁.gpr (treg (ds + k))).toNat + v.toNat +
        cOf false k s₁.ca))) dd k = regsVal s₁ dd k := regsVal_congr fun j hj => by
      simp only [writeCarry_gpr, write_gpr, treg_eq_r11, ite_false,
        treg_ne_of (by omega) (by omega) (show dd + j ≠ dd + k by omega)]
    have hc : cOf false k s₁.ca ≤ 1 := by unfold cOf; split <;> simp [Bool.toNat_le]
    have e := RegUpd.toNat_add_ca (s₁.write .r11 v) (r := treg (dd + k))
      (v := (s₁.gpr (treg (ds + k))).toNat + v.toNat + cOf false k s₁.ca)
      (by have := (s₁.gpr (treg (ds + k))).isLt; have := v.isLt; omega)
    refine ⟨?_, M₁, ?_⟩
    · rw [regsVal_succ_top, regsVal_succ_top, hrk, pv, pow64_succ, show cOf false (k + 1) _ =
        ((s₁.write .r11 v).writeCarry (treg (dd + k)) ((s₁.gpr (treg (ds + k))).toNat + v.toNat +
          cOf false k s₁.ca)).ca.toNat from rfl, ← hvv]
      rw [htk] at e ⊢
      generalize 2 ^ (64 * k) = P at *
      generalize cOf false k s₁.ca = c at *
      generalize ((s₁.write .r11 v).writeCarry _ _).ca.toNat = c' at *
      generalize ((s₁.write .r11 v).writeCarry _ _).gpr (treg (dd + k)) = w at *
      have e2 := congrArg (P * ·) e
      simp only [Nat.mul_add] at e2
      grind
    · refine (K₁.mono ?_).trans ((Kp.write _ _ ?_).trans (Kp.writeCarry _ _ ?_))
      · intro r hr
        rcases List.mem_cons.mp hr with h | h
        · exact List.mem_cons.mpr (.inl h)
        · exact List.mem_cons.mpr (.inr (by rw [tregs_succ]; exact List.mem_append_left _ h))
      · exact List.mem_cons_self ..
      · exact List.mem_cons.mpr (.inr (by rw [tregs_succ]; exact List.mem_append_right _ (List.mem_singleton_self _)))

/-! ## The multiplication of at most four words: the rows -/

/-- The registers a row writes. -/
def lrow (n : Nat) : List Reg := [.r9, .r11, .r12] ++ tregs 0 (n + 1)

theorem lrow_of {n : Nat} {l : List Reg} (h : ∀ r ∈ l, r ∈ [Reg.r9, .r11, .r12] ∨ ∃ j ≤ n, r = treg j) :
    ∀ r ∈ l, r ∈ lrow n := by
  intro r hr
  rcases h r hr with h | ⟨j, hj, rfl⟩
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (by simpa using treg_mem_tregs (d := 0) (k := n + 1) (j := j) (by omega))

theorem tregs_sub_lrow {n d k : Nat} (h : d + k ≤ n + 1) : ∀ r ∈ tregs d k, r ∈ [Reg.r9, .r11, .r12] ∨ ∃ j ≤ n, r = treg j := by
  intro r hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  rw [List.mem_range] at hj
  exact .inr ⟨d + j, by omega, rfl⟩

theorem not_mem_lrow {n : Nat} {r : Reg} (h1 : r ∉ [Reg.r9, .r11, .r12]) (h2 : ∀ j ≤ n, r ≠ treg j) : r ∉ lrow n := by
  intro h
  rcases List.mem_append.mp h with h' | h'
  · exact h1 h'
  · obtain ⟨j, hj, e⟩ := List.mem_map.mp h'
    rw [List.mem_range] at hj
    rw [Nat.zero_add] at e
    exact h2 j (by omega) e.symm

theorem cOf_pos {k : Nat} (hk : 0 < k) (c : Bool) : cOf false k c = c.toNat := by
  simp [cOf, Nat.ne_of_gt hk]

theorem cOfT_pos {k : Nat} (hk : 0 < k) (c : Bool) : cOf true k c = c.toNat := by
  simp [cOf, Nat.ne_of_gt hk]

theorem regsVal_top (s : State) (n : Nat) :
    regsVal s 0 (n + 1) = regsVal s 0 n + 2 ^ (64 * n) * (s.gpr (treg n)).toNat := by
  rw [regsVal_succ_top, Nat.zero_add]

theorem regsVal_low' (s : State) (n : Nat) :
    regsVal s 0 (n + 1) = (s.gpr (treg 0)).toNat + 2 ^ 64 * regsVal s 1 n := rfl

theorem wp_gen {c : Prog isa} {s : State} {Q : State → Prop} (h : ∀ t, t = s → WP isa c t Q) : WP isa c s Q :=
  h s rfl

/-- The row `T += x [b]`, `[b]` in `bReg n`, the top word in `r12`. -/
theorem qrowB_ok {t : State} {base : Addr} {size : Nat} (ht : Ws t base size) {n K : Nat}
    (hn0 : 0 < n) (hn : n ≤ 4) (h5 : At t base .r5 K) (hK : K + 8 ≤ size)
    (hb : regsVal t 0 (n + 1) + (word t.mem base K).toNat * gval t (bReg n) n < 2 ^ (64 * (n + 2))) :
    WP isa (.block (qrowB n)) t fun u =>
      regsVal u 0 (n + 1) + 2 ^ (64 * (n + 1)) * (u.gpr .r12).toNat =
        regsVal t 0 (n + 1) + (word t.mem base K).toNat * gval t (bReg n) n ∧
      u.mem = t.mem ∧ Kp (lrow n) t u := by
  have hs15 := ht.small
  simp only [qrowB, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_step (ld_ok ht h5 (by decide) (by decide) (d := 0) (by omega)) ?_
  rw [Nat.add_zero]
  generalize hx : word t.mem base K = x
  generalize ht₁ : t.write .r9 x = t₁
  have hb₁ : ∀ j < n, t₁.gpr (bReg n j) = t.gpr (bReg n j) := fun j _ => by
    rw [← ht₁]; simp only [bReg, write_gpr, treg_eq_r9, ite_false]
  have hr₁ : ∀ d k, regsVal t₁ d k = regsVal t d k := fun d k => regsVal_congr fun j _ => by
    rw [← ht₁]; simp only [write_gpr, treg_eq_r9, ite_false]
  have h9 : t₁.gpr .r9 = x := by rw [← ht₁]; simp only [write_gpr, ite_true]
  have hyB : ∀ j < n, bReg n j ≠ .r11 ∧ bReg n j ≠ .r9 ∧ ∀ i < n, bReg n j ≠ treg (0 + i) :=
    fun j hj => ⟨treg_ne (r := .r11) (by decide) _, treg_ne (r := .r9) (by decide) _,
      fun i hi => treg_ne_of (by omega) (by omega) (by omega)⟩
  have hyB1 : ∀ j < n, bReg n j ≠ .r11 ∧ bReg n j ≠ .r9 ∧ ∀ i < n, bReg n j ≠ treg (1 + i) :=
    fun j hj => ⟨treg_ne (r := .r11) (by decide) _, treg_ne (r := .r9) (by decide) _,
      fun i hi => treg_ne_of (by omega) (by omega) (by omega)⟩
  -- The low words.
  refine WP.block_append (WP.mono (pass_ok (s := t₁) (hi := false) (y := bReg n) (dd := 0) (ds := 0) (W := n)
    (Nat.le_refl _) (by omega) hyB (k := n) (Nat.le_refl _)) fun t₂ ⟨V₂, M₂, K₂⟩ => ?_)
  rw [cOf_pos hn0, hr₁, h9] at V₂
  have nt2 : ∀ r : Reg, r ≠ .r11 → (∀ j < n, r ≠ treg j) → t₂.gpr r = t₁.gpr r := fun r h1 h2 =>
    K₂.gpr _ (by
      intro h; rcases List.mem_cons.mp h with e | e
      · exact h1 e
      · obtain ⟨j, hj, e'⟩ := List.mem_map.mp e; rw [List.mem_range] at hj; exact h2 j hj (by rw [← e', Nat.zero_add]))
  have hxn2 : t₂.gpr (treg n) = t.gpr (treg n) := by
    rw [nt2 _ (treg_ne (r := .r11) (by decide) _) fun j hj => treg_ne_of (by omega) (by omega) (by omega), ← ht₁]
    simp only [write_gpr, treg_eq_r9, ite_false]
  -- The carry into `treg n`, and from it into `r12`.
  refine wp_step exec_addze ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_addze ?_
  refine wp_gen fun t₃ ht₃ => ?_
  generalize hv : (t₂.gpr (treg n)).toNat + t₂.ca.toNat = v at ht₃
  have e3 := RegUpd.toNat_add_ca t₂ (r := treg n) (v := v)
    (by rw [← hv]; have := (t₂.gpr (treg n)).isLt; have := Bool.toNat_le t₂.ca; omega)
  generalize ht₂' : t₂.writeCarry (treg n) v = t₂' at e3 ht₃
  generalize hca' : t₂'.ca.toNat = ca' at e3
  have hca1 : ca' ≤ 1 := hca' ▸ Bool.toNat_le _
  have h12₃ : (t₃.gpr .r12).toNat = ca' := by
    rw [ht₃]
    simp only [RegUpd.ca_write, RegUpd.gpr_writeCarry_self, BitVec.toNat_ofNat, write_gpr, ite_true]
    rw [Nat.zero_mod, Nat.zero_add, hca', Nat.mod_eq_of_lt (by omega)]
  have hxn₃ : t₃.gpr (treg n) = t₂'.gpr (treg n) := by
    rw [ht₃]; simp only [writeCarry_gpr, write_gpr, treg_eq_r12, ite_false]
  have K₂₃ : Kp [treg n, .r12] t₂ t₃ := by
    rw [ht₃, ← ht₂']
    exact ((Kp.writeCarry _ _ (List.mem_cons_self ..)).trans (Kp.write _ _ (by simp))).trans
      (Kp.writeCarry _ _ (by simp))
  have hm₃ : t₃.mem = t₂.mem := by rw [ht₃, ← ht₂']; rfl
  have hr₃ : regsVal t₃ 0 n = regsVal t₂ 0 n := regsVal_kp K₂₃ fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, Nat.zero_add]
    exact ⟨treg_ne_of (by omega) (by omega) (by omega), treg_ne (r := .r12) (by decide) _⟩
  rw [← hxn₃] at e3
  rw [hxn2] at hv
  generalize hc2 : t₂.ca.toNat = c2 at V₂ hv
  clear ht₃
  -- The high words.
  have h9₃ : t₃.gpr .r9 = x := by
    rw [K₂₃.gpr _ (by simp), nt2 _ (by decide) fun j _ => (treg_ne (r := .r9) (by decide) j).symm, h9]
  refine WP.block_append (WP.mono (pass_ok (s := t₃) (hi := true) (y := bReg n) (dd := 1) (ds := 1) (W := n)
    (Nat.le_refl _) (by omega) hyB1 (k := n) (Nat.le_refl _)) fun t₄ ⟨V₄, M₄, K₄⟩ => ?_)
  rw [cOf_pos hn0, h9₃] at V₄
  refine wp_step exec_addze (WP.block_nil ?_)
  have h12₄ : t₄.gpr .r12 = t₃.gpr .r12 := K₄.gpr _ (by simp [tregs])
  have h0₄ : t₄.gpr (treg 0) = t₃.gpr (treg 0) := K₄.gpr _ (by
    intro h; rcases List.mem_cons.mp h with e | e
    · exact treg_ne (r := .r11) (by decide) _ e
    · exact treg_not_mem_tregs (by omega) (by omega) (by omega) e)
  have e5 := RegUpd.toNat_add_ca t₄ (r := .r12) (v := (t₄.gpr .r12).toNat + t₄.ca.toNat)
    (by have := (t₄.gpr .r12).isLt; have := Bool.toNat_le t₄.ca; omega)
  generalize ht₅ : t₄.writeCarry .r12 ((t₄.gpr .r12).toNat + t₄.ca.toNat) = t₅ at e5 ⊢
  rw [h12₄, h12₃] at e5
  generalize hc4 : t₄.ca.toNat = c4 at V₄ e5
  have hr₅ : regsVal t₅ 0 (n + 1) = regsVal t₄ 0 (n + 1) := regsVal_congr fun j _ => by
    rw [← ht₅]; simp only [writeCarry_gpr, treg_eq_r12, ite_false]
  -- The values.
  have hPL : pv false x.toNat t₁ (bReg n) n = pv false x.toNat t (bReg n) n := pv_congr hb₁
  have hPH : pv true x.toNat t₃ (bReg n) n = pv true x.toNat t (bReg n) n := pv_congr fun j hj => by
    have hnm : bReg n j ∉ [treg n, .r12] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨treg_ne_of (by omega) (by omega) (by omega), treg_ne (r := .r12) (by decide) _⟩
    rw [K₂₃.gpr _ hnm, nt2 (bReg n j) (hyB1 j hj).1
      (fun i hi => treg_ne_of (i := n + 1 + j) (j := i) (by omega) (by omega) (by omega)), hb₁ j hj]
  have hsplit := pv_split x.toNat t (bReg n) n
  rw [hPL] at V₂
  rw [hPH] at V₄
  have hgB : gval t (bReg n) n = gval t (bReg n) n := rfl
  have eT : regsVal t 0 (n + 1) = regsVal t 0 n + 2 ^ (64 * n) * (t.gpr (treg n)).toNat := regsVal_top t n
  have e3T : regsVal t₃ 0 (n + 1) = regsVal t₂ 0 n + 2 ^ (64 * n) * (t₃.gpr (treg n)).toNat := by
    rw [regsVal_top, hr₃]
  have e3L := regsVal_low' t₃ n
  have e4L := regsVal_low' t₄ n
  rw [h0₄] at e4L
  have hP2 : 2 ^ (64 * (n + 1)) = 2 ^ 64 * 2 ^ (64 * n) := pow64_succ n
  have hP3 : 2 ^ (64 * (n + 2)) = 2 ^ 64 * (2 ^ 64 * 2 ^ (64 * n)) := by
    rw [show n + 2 = (n + 1) + 1 by omega, pow64_succ, pow64_succ]
  rw [hx] at hb
  refine ⟨?_, by rw [← ht₅]; show t₄.mem = t.mem; rw [M₄, hm₃, M₂, ← ht₁]; rfl, ?_⟩
  · rw [hr₅, hP2, ← hsplit, eT]
    rw [← hsplit, eT, hP3] at hb
    generalize 2 ^ (64 * n) = P at *
    generalize (t₅.gpr .r12).toNat = w5 at *
    generalize t₅.ca.toNat = c5 at *
    generalize regsVal t₄ 0 (n + 1) = R4 at *
    generalize regsVal t₄ 1 n = R41 at *
    generalize regsVal t₃ 1 n = R31 at *
    generalize regsVal t₃ 0 (n + 1) = R3 at *
    generalize regsVal t₂ 0 n = R2 at *
    generalize regsVal t 0 n = R0 at *
    generalize pv false x.toNat t (bReg n) n = PL at *
    generalize pv true x.toNat t (bReg n) n = PH at *
    generalize (t.gpr (treg n)).toNat = xt at *
    generalize (t₃.gpr (treg n)).toNat = x3 at *
    generalize (t₃.gpr (treg 0)).toNat = T0 at *
    have key : R4 + 2 ^ 64 * P * w5 + 2 ^ 64 * (2 ^ 64 * P) * c5 = R0 + P * xt + (PL + 2 ^ 64 * PH) := by
      have e5' := congrArg (2 ^ 64 * P * ·) e5
      have V₄' := congrArg (2 ^ 64 * ·) V₄
      have e3' := congrArg (P * ·) e3
      have hv' := congrArg (P * ·) hv
      simp only [Nat.mul_add] at e5' V₄' e3' hv'
      grind
    have hc5 : c5 = 0 := by
      rcases Nat.eq_zero_or_pos c5 with h | h
      · exact h
      · exfalso
        have : 2 ^ 64 * (2 ^ 64 * P) ≤ 2 ^ 64 * (2 ^ 64 * P) * c5 := Nat.le_mul_of_pos_right _ h
        omega
    rw [hc5, Nat.mul_zero, Nat.add_zero] at key
    exact key
  · exact ((((ht₁ ▸ Kp.write t x (lrow_of (n := n) (l := [.r9]) (by simp) _ (List.mem_singleton_self _)) :
        Kp (lrow n) t t₁).trans
      (K₂.mono (lrow_of (n := n) fun r hr => by
        rcases List.mem_cons.mp hr with h | h
        · exact .inl (by simp [h])
        · exact tregs_sub_lrow (d := 0) (k := n) (by omega) r h)))).trans
      (K₂₃.mono (lrow_of (n := n) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr ⟨n, Nat.le_refl _, rfl⟩
        · exact .inl (by simp)))).trans
      ((K₄.mono (lrow_of (n := n) fun r hr => by
        rcases List.mem_cons.mp hr with h | h
        · exact .inl (by simp [h])
        · exact tregs_sub_lrow (d := 1) (k := n) (by omega) r h)).trans
      (by rw [← ht₅]; exact Kp.writeCarry _ _ (lrow_of (n := n) (l := [.r12]) (by simp) _ (List.mem_singleton_self _))))

theorem mReg_ne {j : Nat} (hj : j < 4) : mReg j ≠ .r11 ∧ mReg j ≠ .r9 ∧ mReg j ≠ .r12 ∧ mReg j ∉ hiRegs ∧
    mReg j ≠ .r3 ∧ mReg j ≠ .r4 ∧ mReg j ≠ .r5 ∧ mReg j ≠ .r8 :=
  (by decide : ∀ j < 4, mReg j ≠ .r11 ∧ mReg j ≠ .r9 ∧ mReg j ≠ .r12 ∧ mReg j ∉ hiRegs ∧
    mReg j ≠ .r3 ∧ mReg j ≠ .r4 ∧ mReg j ≠ .r5 ∧ mReg j ≠ .r8) j hj

theorem mReg_ne_treg {j : Nat} (hj : j < 4) (i : Nat) : mReg j ≠ treg i := fun e =>
  (mReg_ne hj).2.2.2.1 (e ▸ treg_hi i)

theorem gval_low (s : State) (f : Nat → Reg) {k : Nat} (hk : 0 < k) : gval s f k % 2 ^ 64 = (s.gpr (f 0)).toNat := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · simp only [gval, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
      exact Nat.mod_eq_of_lt (BitVec.isLt _)
    · rw [gval, show 64 * k = 64 + 64 * (k - 1) by omega, Nat.pow_add, Nat.mul_assoc, Nat.add_mul_mod_self_left, ih hk']

theorem pv_low (hi : Bool) (x : Nat) (s : State) (f : Nat → Reg) {k : Nat} (hk : 0 < k) :
    pv hi x s f k % 2 ^ 64 = (if hi then x * (s.gpr (f 0)).toNat / 2 ^ 64 else x * (s.gpr (f 0)).toNat % 2 ^ 64) % 2 ^ 64 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · simp only [pv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
    · rw [pv, show 64 * k = 64 + 64 * (k - 1) by omega, Nat.pow_add, Nat.mul_assoc, Nat.add_mul_mod_self_left, ih hk']

theorem regsVal_low0 (s : State) {k : Nat} (hk : 0 < k) : regsVal s 0 k % 2 ^ 64 = (s.gpr (treg 0)).toNat := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact regsVal_low s 0 k'

/-- `qhead`: `r9 = q`, `q = t₀ m' mod 2⁶⁴` for an `m'` with `m m' = -1 mod 2⁶⁴`,
`m'` in `mpReg n`. -/
theorem qhead_ok {t : State} {M : Mod} {m : Nat}
    (hinv : (m * (t.gpr (mpReg M.n)).toNat + 1) % 2 ^ 64 = 0)
    (hone : M.minv.toNat = 1 → (t.gpr (mpReg M.n)).toNat = 1) {rest : List Instr} {Q : State → Prop}
    (k : ∀ (t₁ : State) (qv : BitVec 64) (mp : Nat), (m * mp + 1) % 2 ^ 64 = 0 →
      qv.toNat = (t.gpr (treg 0)).toNat * mp % 2 ^ 64 → t₁.gpr .r9 = qv → t₁.mem = t.mem →
      Kp [.r11, .r9] t t₁ → WP isa (.block rest) t₁ Q) :
    WP isa (.block (qhead M ++ rest)) t Q := by
  unfold qhead
  split
  · rename_i h1
    refine wp_step exec_ori ?_
    refine k _ (t.gpr (treg 0) ||| (0 : BitVec 16).setWidth 64) 1 (by rw [hone h1] at hinv; exact hinv) ?_
      (by simp only [write_gpr, ite_true]) rfl
      (Kp.write _ _ (by simp))
    rw [BitVec.toNat_or, Nat.mul_one, Nat.mod_eq_of_lt (BitVec.isLt _)]
    simp
  · simp only [List.cons_append, List.nil_append]
    refine wp_step exec_mul ?_
    refine k _ (t.gpr (treg 0) * t.gpr (mpReg M.n)) _ hinv ?_
      (by simp only [write_gpr, ite_true]) rfl (Kp.write _ _ (by simp))
    simp only [BitVec.toNat_mul]

/-- The row `T = (T + q m) / 2⁶⁴`, the modulus in `mReg`, `m'` in `mpReg`. -/
theorem qrowM_ok {t : State} {base : Addr} {size : Nat} (ht : Ws t base size) {M : Mod} {m : Nat}
    (hn0 : 0 < M.n) (hn : M.n ≤ 4)
    (hm : gval t mReg M.n = m) (hinv : (m * (t.gpr (mpReg M.n)).toNat + 1) % 2 ^ 64 = 0)
    (hone : M.minv.toNat = 1 → (t.gpr (mpReg M.n)).toNat = 1)
    (hb : regsVal t 0 (M.n + 1) + 2 ^ (64 * (M.n + 1)) * (t.gpr .r12).toNat + 2 ^ 64 * m < 2 ^ (64 * (M.n + 2))) :
    WP isa (.block (qrowM M)) t fun u =>
      (∃ q, q < 2 ^ 64 ∧ 2 ^ 64 * regsVal u 0 (M.n + 1) =
        regsVal t 0 (M.n + 1) + 2 ^ (64 * (M.n + 1)) * (t.gpr .r12).toNat + q * m) ∧
      u.mem = t.mem ∧ Kp (lrow M.n) t u := by
  have hs15 := ht.small
  generalize hN : M.n = n at *
  simp only [qrowM, hN, List.append_assoc, List.cons_append, List.nil_append]
  refine qhead_ok (M := M) (by rw [hN]; exact hinv) (by rw [hN]; exact hone) fun t₁ qv mp hinv hqv h9 M₁' K₁' => ?_
  have hq64 : qv.toNat < 2 ^ 64 := qv.isLt
  have nt1 : ∀ r : Reg, r ≠ .r11 → r ≠ .r9 → t₁.gpr r = t.gpr r := fun r h1 h2 =>
    K₁'.gpr _ (by simp [h1, h2])
  have hr₁ : ∀ d k, regsVal t₁ d k = regsVal t d k := fun d k => regsVal_congr fun j _ =>
    nt1 _ (treg_ne (r := .r11) (by decide) _) (treg_ne (r := .r9) (by decide) _)
  have hm₁ : ∀ j < n, t₁.gpr (mReg j) = t.gpr (mReg j) := fun j hj =>
    nt1 _ (mReg_ne (by omega)).1 (mReg_ne (by omega)).2.1
  have hyM : ∀ d, ∀ j < n, mReg j ≠ .r11 ∧ mReg j ≠ .r9 ∧ ∀ i < n, mReg j ≠ treg (d + i) :=
    fun d j hj => ⟨(mReg_ne (by omega)).1, (mReg_ne (by omega)).2.1, fun i _ => mReg_ne_treg (by omega) _⟩
  -- The low words.
  refine WP.block_append (WP.mono (pass_ok (s := t₁) (hi := false) (y := mReg) (dd := 0) (ds := 0) (W := n)
    (Nat.le_refl _) (by omega) (hyM 0) (k := n) (Nat.le_refl _)) fun t₂ ⟨V₂, M₂, K₂⟩ => ?_)
  rw [cOf_pos hn0, hr₁, h9] at V₂
  have nt2 : ∀ r : Reg, r ≠ .r11 → (∀ j < n, r ≠ treg j) → t₂.gpr r = t₁.gpr r := fun r h1 h2 =>
    K₂.gpr _ (by
      intro h; rcases List.mem_cons.mp h with e | e
      · exact h1 e
      · obtain ⟨j, hj, e'⟩ := List.mem_map.mp e; rw [List.mem_range] at hj; exact h2 j hj (by rw [← e', Nat.zero_add]))
  have hxn2 : t₂.gpr (treg n) = t.gpr (treg n) := by
    rw [nt2 _ (treg_ne (r := .r11) (by decide) _) fun j hj => treg_ne_of (by omega) (by omega) (by omega),
      nt1 _ (treg_ne (r := .r11) (by decide) _) (treg_ne (r := .r9) (by decide) _)]
  have h12₂ : t₂.gpr .r12 = t.gpr .r12 := by
    rw [nt2 _ (by decide) fun j _ => (treg_ne (r := .r12) (by decide) j).symm, nt1 _ (by decide) (by decide)]
  -- The carry into `treg n` and `r12`.
  refine wp_step exec_addze ?_
  refine wp_step exec_addze ?_
  refine wp_gen fun t₃ ht₃ => ?_
  generalize hv : (t₂.gpr (treg n)).toNat + t₂.ca.toNat = v at ht₃
  have e3 := RegUpd.toNat_add_ca t₂ (r := treg n) (v := v)
    (by rw [← hv]; have := (t₂.gpr (treg n)).isLt; have := Bool.toNat_le t₂.ca; omega)
  generalize ht₂' : t₂.writeCarry (treg n) v = t₂' at e3 ht₃
  have hw : ((t₂'.gpr .r12).toNat + t₂'.ca.toNat) < 2 ^ 65 := by
    have := (t₂'.gpr .r12).isLt; have := Bool.toNat_le t₂'.ca; omega
  have e3b := RegUpd.toNat_add_ca t₂' (r := .r12) (v := (t₂'.gpr .r12).toNat + t₂'.ca.toNat) hw
  rw [← ht₃] at e3b
  have h12' : t₂'.gpr .r12 = t₂.gpr .r12 := by rw [← ht₂']; simp only [writeCarry_gpr, r12_eq_treg, ite_false]
  rw [h12', h12₂] at e3b
  generalize hca3 : t₂'.ca.toNat = c3 at e3 e3b
  have hxn₃ : t₃.gpr (treg n) = t₂'.gpr (treg n) := by
    rw [ht₃]; simp only [writeCarry_gpr, treg_eq_r12, ite_false]
  rw [← hxn₃] at e3
  have K₂₃ : Kp [treg n, .r12] t₂ t₃ := by
    rw [ht₃, ← ht₂']
    exact (Kp.writeCarry _ _ (List.mem_cons_self ..)).trans (Kp.writeCarry _ _ (by simp))
  have hm₃ : t₃.mem = t₂.mem := by rw [ht₃, ← ht₂']; rfl
  have hr₃ : regsVal t₃ 0 n = regsVal t₂ 0 n := regsVal_kp K₂₃ fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, Nat.zero_add]
    exact ⟨treg_ne_of (by omega) (by omega) (by omega), treg_ne (r := .r12) (by decide) _⟩
  have h0₃ : t₃.gpr (treg 0) = t₂.gpr (treg 0) := K₂₃.gpr _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨treg_ne_of (by omega) (by omega) (by omega), treg_ne (r := .r12) (by decide) _⟩)
  rw [hxn2] at hv
  generalize hc2 : t₂.ca.toNat = c2 at V₂ hv
  have h9₃ : t₃.gpr .r9 = qv := by
    rw [K₂₃.gpr _ (by simp), nt2 _ (by decide) fun j _ => (treg_ne (r := .r9) (by decide) j).symm, h9]
  clear ht₃
  -- The high words, one register down.
  refine WP.block_append (WP.mono (pass_ok (s := t₃) (hi := true) (y := mReg) (dd := 0) (ds := 1) (W := n)
    (by omega) (by omega) (hyM 0) (k := n) (Nat.le_refl _)) fun t₄ ⟨V₄, M₄, K₄⟩ => ?_)
  rw [cOf_pos hn0, h9₃] at V₄
  refine wp_step exec_addze (WP.block_nil ?_)
  have h12₄ : t₄.gpr .r12 = t₃.gpr .r12 := K₄.gpr _ (by simp [tregs])
  have hw5 : (t₄.gpr .r12).toNat + t₄.ca.toNat < 2 ^ 65 := by
    have := (t₄.gpr .r12).isLt; have := Bool.toNat_le t₄.ca; omega
  have e5 := RegUpd.toNat_add_ca t₄ (r := treg n) (v := (t₄.gpr .r12).toNat + t₄.ca.toNat) hw5
  generalize ht₅ : t₄.writeCarry (treg n) ((t₄.gpr .r12).toNat + t₄.ca.toNat) = t₅ at e5 ⊢
  rw [h12₄] at e5
  generalize hc4 : t₄.ca.toNat = c4 at V₄ e5
  have hr₅ : regsVal t₅ 0 n = regsVal t₄ 0 n := regsVal_congr fun j hj => by
    rw [← ht₅]; simp only [writeCarry_gpr, Nat.zero_add, treg_ne_of (show j < 10 by omega) (show n < 10 by omega)
      (show j ≠ n by omega), ite_false]
  -- The values.
  have hQL : pv false qv.toNat t₁ mReg n = pv false qv.toNat t mReg n := pv_congr hm₁
  have hQH : pv true qv.toNat t₃ mReg n = pv true qv.toNat t mReg n := pv_congr fun j hj => by
    have hnm : mReg j ∉ [treg n, .r12] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨mReg_ne_treg (by omega) _, (mReg_ne (by omega)).2.2.1⟩
    rw [K₂₃.gpr _ hnm, nt2 _ (mReg_ne (by omega)).1 (fun i _ => mReg_ne_treg (by omega) _), hm₁ j hj]
  have hsplit := pv_split qv.toNat t mReg n
  rw [hm] at hsplit
  rw [hQL] at V₂
  rw [hQH] at V₄
  -- The low word of the first chain is zero.
  have hm0 : (t.gpr (mReg 0)).toNat = m % 2 ^ 64 := by rw [← hm, gval_low _ _ hn0]
  have hP : 2 ^ (64 * n) = 2 ^ 64 * 2 ^ (64 * (n - 1)) := by rw [← Nat.pow_add]; congr 1; omega
  have hlow : (t₂.gpr (treg 0)).toNat = 0 := by
    have A : (regsVal t₂ 0 n + 2 ^ (64 * n) * c2) % 2 ^ 64 = (t₂.gpr (treg 0)).toNat := by
      rw [hP, Nat.mul_assoc, Nat.add_mul_mod_self_left, regsVal_low0 _ hn0]
    have hql : pv false qv.toNat t mReg n % 2 ^ 64 = qv.toNat * (t.gpr (mReg 0)).toNat % 2 ^ 64 := by
      rw [pv_low _ _ _ _ hn0]; simp only [Bool.false_eq_true, ite_false, Nat.mod_mod]
    rw [← A, V₂, Nat.add_mod, regsVal_low0 _ hn0, hql, hm0, Nat.mul_mod_mod, Nat.add_mod_mod, hqv]
    exact mont_low _ _ _ hinv
  have e3L := regsVal_low' t₃ n
  have e3T := regsVal_top t₃ n
  have e5T := regsVal_top t₅ n
  have eT := regsVal_top t n
  rw [h0₃, hlow, Nat.zero_add] at e3L
  rw [hr₃] at e3T
  rw [hr₅] at e5T
  have hqm : qv.toNat * m ≤ 2 ^ 64 * m := Nat.mul_le_mul_right _ (by omega)
  have hP2 : 2 ^ (64 * (n + 1)) = 2 ^ 64 * 2 ^ (64 * n) := pow64_succ n
  have hP3 : 2 ^ (64 * (n + 2)) = 2 ^ 64 * (2 ^ 64 * 2 ^ (64 * n)) := by
    rw [show n + 2 = (n + 1) + 1 by omega, pow64_succ, pow64_succ]
  refine ⟨⟨qv.toNat, hq64, ?_⟩, ?_, ?_⟩
  · rw [e5T, eT, hP2, ← hsplit]
    rw [eT, hP2, hP3] at hb
    generalize 2 ^ (64 * n) = P at *
    generalize regsVal t 0 n = R0 at *
    generalize regsVal t₂ 0 n = R2 at *
    generalize regsVal t₃ 1 n = R31 at *
    generalize regsVal t₃ 0 (n + 1) = R3 at *
    generalize regsVal t₄ 0 n = R4 at *
    generalize pv false qv.toNat t mReg n = QL at *
    generalize pv true qv.toNat t mReg n = QH at *
    generalize (t.gpr (treg n)).toNat = xt at *
    generalize (t₃.gpr (treg n)).toNat = x3 at *
    generalize (t₅.gpr (treg n)).toNat = x5 at *
    generalize (t.gpr .r12).toNat = r12 at *
    generalize (t₃.gpr .r12).toNat = r3 at *
    generalize t₃.ca.toNat = c3' at *
    generalize t₅.ca.toNat = c5 at *
    have key : 2 ^ 64 * (R4 + P * x5) + 2 ^ 64 * (2 ^ 64 * P) * (c3' + c5) =
        R0 + P * xt + 2 ^ 64 * P * r12 + (QL + 2 ^ 64 * QH) := by
      have a1 := congrArg (2 ^ 64 * ·) V₄
      have a2 := congrArg (2 ^ 64 * P * ·) e5
      have a3 := congrArg (2 ^ 64 * P * ·) e3b
      have a4 := congrArg (P * ·) e3
      have a5 := congrArg (P * ·) hv
      simp only [Nat.mul_add] at a1 a2 a3 a4 a5
      grind
    have hc : c3' + c5 = 0 := by
      rcases Nat.eq_zero_or_pos (c3' + c5) with h | h
      · exact h
      · exfalso
        have : 2 ^ 64 * (2 ^ 64 * P) ≤ 2 ^ 64 * (2 ^ 64 * P) * (c3' + c5) := Nat.le_mul_of_pos_right _ h
        rw [hsplit] at key
        omega
    rw [hc, Nat.mul_zero, Nat.add_zero] at key
    exact key
  · rw [← ht₅]; show t₄.mem = t.mem; rw [M₄, hm₃, M₂, M₁']
  · have k1 : Kp (lrow n) t t₁ := by
      exact K₁'.mono (lrow_of (n := n) (l := [.r11, .r9]) (by simp))
    have k2 : Kp (lrow n) t₁ t₂ := K₂.mono (lrow_of (n := n) fun r hr => by
      rcases List.mem_cons.mp hr with h | h
      · exact .inl (by simp [h])
      · exact tregs_sub_lrow (d := 0) (k := n) (by omega) r h)
    have k3 : Kp (lrow n) t₂ t₃ := K₂₃.mono (lrow_of (n := n) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr ⟨n, Nat.le_refl _, rfl⟩
      · exact .inl (by simp))
    have k4 : Kp (lrow n) t₃ t₄ := K₄.mono (lrow_of (n := n) fun r hr => by
      rcases List.mem_cons.mp hr with h | h
      · exact .inl (by simp [h])
      · exact tregs_sub_lrow (d := 0) (k := n) (by omega) r h)
    have k5 : Kp (lrow n) t₄ t₅ := by
      rw [← ht₅]
      exact Kp.writeCarry _ _ (lrow_of (n := n) (l := [treg n]) (fun r hr => .inr ⟨n, Nat.le_refl _,
        List.mem_singleton.mp hr⟩) _ (List.mem_singleton_self _))
    exact (((k1.trans k2).trans k3).trans k4).trans k5

/-! ## The multiplication of at most four words: the loop -/

/-- The registers the loop writes. -/
def qclob (n : Nat) : List Reg := .r5 :: .r8 :: lrow n

theorem bReg_not_qclob {n j : Nat} (hn : n ≤ 4) (hj : j < n) : bReg n j ∉ qclob n := by
  intro h
  rcases List.mem_cons.mp h with e | h
  · exact treg_ne (r := .r5) (by decide) _ e
  rcases List.mem_cons.mp h with e | h
  · exact treg_ne (r := .r8) (by decide) _ e
  exact not_mem_lrow (n := n) (by simp) (fun i hi => treg_ne_of (by omega) (by omega) (by omega)) h

theorem mReg_not_qclob {n j : Nat} (hj : j < 4) : mReg j ∉ qclob n := by
  intro h
  rcases List.mem_cons.mp h with e | h
  · exact (mReg_ne hj).2.2.2.2.2.2.1 e
  rcases List.mem_cons.mp h with e | h
  · exact (mReg_ne hj).2.2.2.2.2.2.2 e
  exact not_mem_lrow (n := n) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨(mReg_ne hj).2.1, (mReg_ne hj).1, (mReg_ne hj).2.2.1⟩) (fun i _ => mReg_ne_treg hj i) h

theorem mpReg_not_qclob {n : Nat} (hn : n ≤ 4) : mpReg n ∉ qclob n := by
  intro h
  rcases List.mem_cons.mp h with e | h
  · exact treg_ne (r := .r5) (by decide) _ e
  rcases List.mem_cons.mp h with e | h
  · exact treg_ne (r := .r8) (by decide) _ e
  exact not_mem_lrow (n := n) (by simp) (fun i hi => treg_ne_of (by omega) (by omega) (by omega)) h

theorem lo_not_qclob {n : Nat} {r : Reg} (h1 : r ∉ [Reg.r5, .r8, .r9, .r11, .r12]) (h2 : r ∉ hiRegs) : r ∉ qclob n := by
  intro h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1
  rcases List.mem_cons.mp h with e | h
  · exact h1.1 e
  rcases List.mem_cons.mp h with e | h
  · exact h1.2.1 e
  exact not_mem_lrow (n := n) (by simp [h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2]) (fun i _ e => h2 (by rw [e]; exact treg_hi i)) h

/-- The invariant of `rmul4`'s loop, before the iteration for word `k`. -/
structure QLoopInv (base : Addr) (M : Mod) (a b m k : Nat) (s t : State) : Prop where
  r5 : At t base .r5 (a + 8 * k)
  r8 : t.gpr .r8 = BitVec.ofNat 64 (M.n - k)
  mem : t.mem = s.mem
  kp : Kp (qclob M.n) s t
  lt : regsVal t 0 (M.n + 1) < 2 * m
  cong : ∃ U, 2 ^ (64 * k) * regsVal t 0 (M.n + 1) = wordsVal s.mem base a k * wordsVal s.mem base b M.n + U * m

/-- What the loop needs of the state it starts from. -/
structure QPre (base : Addr) (M : Mod) (size a b m : Nat) (s : State) : Prop where
  ws : Ws s base size
  r3 : At s base .r3 0
  n0 : 0 < M.n
  n4 : M.n ≤ 4
  a_le : a + 8 * M.n ≤ size
  bv : gval s (bReg M.n) M.n = wordsVal s.mem base b M.n
  mv : gval s mReg M.n = m
  inv : (m * (s.gpr (mpReg M.n)).toNat + 1) % 2 ^ 64 = 0
  one : M.minv.toNat = 1 → (s.gpr (mpReg M.n)).toNat = 1
  b_lt : wordsVal s.mem base b M.n < m
  m_lt : m < 2 ^ (64 * M.n)

theorem qrow_eq (M : Mod) : qrow M = qrowB M.n ++ (qrowM M ++ ([.addi .r5 .r5 8, .subi .r8 .r8 1] : List Instr)) := by
  simp only [qrow, List.append_assoc]

/-- An iteration of the loop. -/
theorem qrow_ok {s : State} {base : Addr} {size : Nat} {M : Mod} {a b m k : Nat} (P : QPre base M size a b m s)
    (hk : k < M.n) {t : State} (I : QLoopInv base M a b m k s t) :
    WP isa (.block (qrow M)) t fun u => QLoopInv base M a b m (k + 1) s u := by
  have hs15 := P.ws.small
  have hn0 := P.n0
  have hn4 := P.n4
  have ht := I.kp.ws P.ws
  rw [qrow_eq]
  have hB : gval t (bReg M.n) M.n = wordsVal s.mem base b M.n := by
    rw [← P.bv]; exact gval_congr fun j hj => I.kp.gpr _ (bReg_not_qclob hn4 hj)
  have hM : gval t mReg M.n = m := by
    rw [← P.mv]; exact gval_congr fun j hj => I.kp.gpr _ (mReg_not_qclob (by omega))
  have hBm := P.b_lt
  generalize hBv : wordsVal s.mem base b M.n = B at hB hBm
  have hmn := P.m_lt
  have hu : word t.mem base (a + 8 * k) = word s.mem base (a + 8 * k) := by rw [I.mem]
  generalize huv : word s.mem base (a + 8 * k) = u at hu
  have hP2 : 2 ^ (64 * (M.n + 2)) = 2 ^ 64 * (2 ^ 64 * 2 ^ (64 * M.n)) := by
    rw [show M.n + 2 = (M.n + 1) + 1 by omega, pow64_succ, pow64_succ]
  have hbnd : regsVal t 0 (M.n + 1) + u.toNat * B < 2 ^ (64 * (M.n + 2)) := by
    have := I.lt
    have : u.toNat * B ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul (by have := u.isLt; omega) (by omega)
    rw [hP2]
    have : 2 * m + (2 ^ 64 - 1) * m ≤ 2 ^ 64 * (2 ^ 64 * 2 ^ (64 * M.n)) := by
      have : (2 ^ 64 + 1) * m ≤ (2 ^ 64 + 1) * 2 ^ (64 * M.n) := Nat.mul_le_mul_left _ (by omega)
      have : (2 ^ 64 + 1) * 2 ^ (64 * M.n) ≤ 2 ^ 64 * (2 ^ 64 * 2 ^ (64 * M.n)) := by
        rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by decide)
      omega
    omega
  refine WP.block_append (WP.mono (qrowB_ok ht hn0 hn4 I.r5 (by have := P.a_le; omega)
    (by rw [hu, hB]; exact hbnd)) fun t₁ ⟨V₁, M₁, K₁⟩ => ?_)
  rw [hu, hB] at V₁
  have hTlt := I.lt
  obtain ⟨U, hU⟩ := I.cong
  generalize hT : regsVal t 0 (M.n + 1) = T at V₁ hbnd hTlt hU
  have hM₁ : gval t₁ mReg M.n = m := by
    rw [← hM]; exact gval_congr fun j hj => K₁.gpr _ (fun h => mReg_not_qclob (n := M.n) (by omega)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
  have hmp : t₁.gpr (mpReg M.n) = s.gpr (mpReg M.n) := by
    rw [K₁.gpr _ (fun h => mpReg_not_qclob hn4 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))),
      I.kp.gpr _ (mpReg_not_qclob hn4)]
  refine WP.block_append (WP.mono (qrowM_ok (K₁.ws ht) (m := m) hn0 hn4 hM₁
    (by rw [hmp]; exact P.inv) (by rw [hmp]; exact P.one) (by
      rw [V₁, hP2]
      have := I.lt
      have : u.toNat * B ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul (by have := u.isLt; omega) (by omega)
      have : (2 ^ 64 + 2 ^ 64 + 1) * m ≤ (2 ^ 64 + 2 ^ 64 + 1) * 2 ^ (64 * M.n) := Nat.mul_le_mul_left _ (by omega)
      have : (2 ^ 64 + 2 ^ 64 + 1) * 2 ^ (64 * M.n) ≤ 2 ^ 64 * (2 ^ 64 * 2 ^ (64 * M.n)) := by
        rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by decide)
      omega)) fun t₂ ⟨⟨q, hq, V₂⟩, M₂, K₂⟩ => ?_)
  rw [V₁] at V₂
  refine wp_step (exec_addi (by decide) (by decide)) ?_
  refine wp_step (exec_subi (by decide) (by decide)) (WP.block_nil ?_)
  have K₀₂ : Kp (qclob M.n) t t₂ := (K₁.trans K₂).mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
  have hrv : ∀ (x y : BitVec 64), regsVal ((t₂.write .r5 x).write .r8 y) 0 (M.n + 1) = regsVal t₂ 0 (M.n + 1) :=
    fun _ _ => regsVal_congr fun j _ => by simp only [write_gpr, treg_eq_r5, treg_eq_r8, ite_false]
  have h5₂ : t₂.gpr .r5 = t.gpr .r5 := (K₁.trans K₂).gpr _ (by simp [lrow, tregs])
  have h8₂ : t₂.gpr .r8 = t.gpr .r8 := (K₁.trans K₂).gpr _ (by simp [lrow, tregs])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [At, write_gpr, reduceCtorEq, ite_false, ite_true]
    rw [h5₂, I.r5, off_add, show a + 8 * k + 8 = a + 8 * (k + 1) by omega]
  · simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
    rw [h8₂, I.r8]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · show t₂.mem = s.mem; rw [M₂, M₁, I.mem]
  · exact I.kp.trans (K₀₂.trans ((Kp.write _ _ (List.mem_cons_self ..)).trans
      (Kp.write _ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
  · rw [hrv]
    have hrow := row_lt hTlt u.isLt hBm hq
    generalize regsVal t₂ 0 (M.n + 1) = T' at V₂ ⊢
    have : 2 ^ 64 * T' < 2 ^ 64 * (2 * m) := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  · refine ⟨U + q * 2 ^ (64 * k), ?_⟩
    rw [hrv]
    generalize regsVal t₂ 0 (M.n + 1) = T' at V₂ ⊢
    have hA : wordsVal s.mem base a (k + 1) = wordsVal s.mem base a k + 2 ^ (64 * k) * u.toNat := by
      rw [wordsVal_succ_top, huv]
    rw [hA, show 64 * (k + 1) = 64 * k + 64 by omega, Nat.pow_add, Nat.mul_assoc, V₂, Nat.mul_add, Nat.mul_add, hU, hBv]
    grind

/-- The loop of `rmul4`. -/
theorem qloop_ok {s : State} {base : Addr} {size : Nat} {M : Mod} {a b m : Nat} (P : QPre base M size a b m s)
    {t : State} (h0 : QLoopInv base M a b m 0 s t) :
    WP isa (.loop (.block (qrow M)) (.nonzero .d .r8)) t fun u => QLoopInv base M a b m M.n s u := by
  have hD15 : M.n < 2 ^ 15 := by have := P.n4; omega
  refine WP.loop (M := isa)
    (fun n t' => ∃ k, n = M.n - k ∧ k < M.n ∧ QLoopInv base M a b m k s t') ?_ M.n t ⟨0, rfl, P.n0, h0⟩
  rintro n t' ⟨k, rfl, hk, I⟩
  refine WP.mono (qrow_ok P hk I) fun u I' => ?_
  have he := eval_nonzero_ofNat I'.r8 (x := M.n - (k + 1)) (by omega)
  by_cases hk1 : k + 1 = M.n
  · exact .inl ⟨by rw [he]; simp [hk1], hk1 ▸ I'⟩
  · exact .inr ⟨by rw [he]; simp; omega, M.n - (k + 1), by omega, k + 1, rfl, by omega, I'⟩

/-! ## The multiplication of at most four words: the reduction -/

theorem qsubRs_succ (n k : Nat) :
    (List.range (k + 1)).flatMap (qsubRStep n) = (List.range k).flatMap (qsubRStep n) ++ qsubRStep n k := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The low `k` words of `T + 2^(64 k) - m` (both in registers) to `bReg`,
no borrow to CA. -/
theorem qsubRs_ok {s : State} {n : Nat} (hn : n ≤ 4) :
    ∀ {k : Nat}, k ≤ n →
    WP isa (.block ((List.range k).flatMap (qsubRStep n))) s fun u =>
      gval u (bReg n) k + 2 ^ (64 * k) * cOf true k u.ca + gval s mReg k =
        regsVal s 0 k + (2 ^ (64 * k) - 1) + 1 ∧
      u.mem = s.mem ∧ Kp (tregs (n + 1) k) s u
  | 0, _ => WP.block_nil ⟨by simp [regsVal, gval, cOf], rfl, Kp.refl _ _⟩
  | k + 1, hk => by
    rw [qsubRs_succ]
    refine WP.block_append (WP.mono (qsubRs_ok hn (k := k) (by omega)) fun s₁ ⟨V₁, M₁, K₁⟩ => ?_)
    simp only [qsubRStep]
    refine wp_step (exec_carryOp _ _ _ _ _ _) (WP.block_nil ?_)
    simp only [ite_true]
    have ht : s₁.gpr (treg k) = s.gpr (treg k) := K₁.gpr _ (treg_not_mem_tregs (by omega) (by omega) (.inl (by omega)))
    have hy : s₁.gpr (mReg k) = s.gpr (mReg k) := K₁.gpr _ (fun h => by
      obtain ⟨j, -, e⟩ := List.mem_map.mp h; exact mReg_ne_treg (show k < 4 by omega) _ e.symm)
    generalize hv : (s₁.gpr (treg k)).toNat + (2 ^ 64 - 1 - (s₁.gpr (mReg k)).toNat) + cOf true k s₁.ca = v
    have e := RegUpd.toNat_add_ca s₁ (r := bReg n k) (v := v)
      (by rw [← hv]; have := (s₁.gpr (treg k)).isLt; have : cOf true k s₁.ca ≤ 1 := by
            unfold cOf; split <;> exact Bool.toNat_le _
          omega)
    have hg : gval (s₁.writeCarry (bReg n k) v) (bReg n) k = gval s₁ (bReg n) k := gval_congr fun j hj => by
      simp only [writeCarry_gpr, bReg, treg_ne_of (show n + 1 + j < 10 by omega) (show n + 1 + k < 10 by omega)
        (by omega), ite_false]
    refine ⟨?_, by rw [RegUpd.mem_writeCarry, M₁], (K₁.mono fun r hr => by
        rw [tregs_succ]; exact List.mem_append_left _ hr).trans
      (Kp.writeCarry _ _ (by rw [tregs_succ]; exact List.mem_append_right _ (List.mem_singleton_self _)))⟩
    rw [gval, hg, regsVal_succ_top, gval, pow64_succ, Nat.zero_add]
    generalize hcb : (s₁.writeCarry (bReg n k) v).ca = cb at *
    generalize hlo : (s₁.writeCarry (bReg n k) v).gpr (bReg n k) = lo at e
    rw [ht, hy] at hv
    have hc : cOf true k s₁.ca ≤ 1 := by unfold cOf; split <;> exact Bool.toNat_le _
    generalize hcc : cOf true k s₁.ca = c at *
    simp only [cOf, Nat.succ_ne_zero, ite_false]
    have hP : 1 ≤ 2 ^ (64 * k) := Nat.one_le_two_pow
    generalize 2 ^ (64 * k) = P at *
    rw [← hv] at e
    have e2 := congrArg (P * ·) e
    simp only [Nat.mul_add] at e2
    have hyl := (s.gpr (mReg k)).isLt
    generalize (s.gpr (mReg k)).toNat = y at *
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

theorem qsels_succ (n k : Nat) :
    (List.range (k + 1)).flatMap (qselWord n) = (List.range k).flatMap (qselWord n) ++ qselWord n k := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The low `k` words of `T`, or of `T - m` (in `bReg`) where the mask `r10`
is all ones, to `[r4]`. -/
theorem qsels_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {n O : Nat} (hn : n ≤ 4)
    (h4 : At s base .r4 O) (hmk : s.gpr .r10 = 0 ∨ s.gpr .r10 = BitVec.allOnes 64) (hO : O + 8 * n ≤ size) :
    ∀ {k : Nat}, k ≤ n →
    WP isa (.block ((List.range k).flatMap (qselWord n))) s fun u =>
      Outside base O (8 * k) s.mem u.mem ∧
      wordsVal u.mem base O k = (if s.gpr .r10 = 0 then regsVal s 0 k else gval s (bReg n) k) ∧
      Kp [.r11, .r12] s u
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, by simp [wordsVal, regsVal, gval], Kp.refl _ _⟩
  | k + 1, hk => by
    have hn' := hs.nowrap
    have hs15 := hs.small
    rw [qsels_succ]
    refine WP.block_append (WP.mono (qsels_ok hs hn h4 hmk hO (k := k) (by omega))
      fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hs₁ := K₁.ws hs
    simp only [qselWord]
    refine wp_step exec_logic ?_
    refine wp_step exec_logic ?_
    refine wp_step exec_logic ?_
    refine wp_step (std_ok ((((hs₁.write _ _).write _ _).write _ _))
      (((K₁.at h4).write _).write _ |>.write _) (by decide) (by omega) (d := 8 * k) (by omega))
      (WP.block_nil ?_)
    simp only [write_gpr, write_mem, reduceCtorEq, ite_false, ite_true, bReg, treg_eq_r12]
    have ht : s₁.gpr (treg k) = s.gpr (treg k) := K₁.gpr _ (by simp)
    have hb : s₁.gpr (treg (n + 1 + k)) = s.gpr (treg (n + 1 + k)) := K₁.gpr _ (by simp)
    have h10 : s₁.gpr .r10 = s.gpr .r10 := K₁.g
    rw [ht, hb, h10, sel_mask _ _ hmk]
    generalize hv : (if s.gpr .r10 = 0 then s.gpr (treg k) else s.gpr (treg (n + 1 + k))) = v
    have W := writeW_outside s₁.mem base (d := O + 8 * k) v (by omega)
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (W.mono (by omega) (by omega)), ?_, ?_⟩
    · rw [wordsVal_succ_top, regsVal_succ_top, gval, W.wordsVal (by omega) (by omega), V₁,
        word_writeW_self, ← hv, Nat.zero_add]
      split <;> rfl
    · exact K₁.trans ((((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans
        (Kp.write _ _ (by decide))).trans (Kp.store _ _ _))

/-- `[r4] = T mod m`, for `T` below `2m` in `treg 0`, …, `treg n` and the
modulus in `mReg`, `T - m` through `bReg`. -/
theorem qcsubR_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {n O m : Nat}
    (h4 : At s base .r4 O) (hn0 : 0 < n) (hn4 : n ≤ 4) (o_le : O + 8 * n ≤ size)
    (hm : gval s mReg n = m) (hm0 : m < 2 ^ (64 * n)) (hN : regsVal s 0 (n + 1) < 2 * m) :
    WP isa (.block (qcsubR n)) s fun u =>
      wordsVal u.mem base O n = regsVal s 0 (n + 1) % m ∧
      Outside base O (8 * n) s.mem u.mem ∧
      Kp (([.r10, .r11, .r12] : List Reg) ++ tregs (n + 1) n) s u := by
  simp only [qcsubR, List.append_assoc]
  refine WP.block_append (WP.mono (qsubRs_ok (s := s) hn4 (k := n) (Nat.le_refl _)) fun s₂ ⟨V₂, M₂, K₂⟩ => ?_)
  rw [hm, show cOf true n s₂.ca = s₂.ca.toNat by simp only [cOf]; split <;> omega] at V₂
  have hs₂ := K₂.ws hs
  refine wp_step exec_addze ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub ?_
  simp only [write_gpr, writeCarry_gpr, ite_true, reduceCtorEq, ite_false]
  have htop : s₂.gpr (treg n) = s.gpr (treg n) :=
    K₂.gpr _ (treg_not_mem_tregs (by omega) (by omega) (.inl (by omega)))
  rw [htop]
  generalize hc : s₂.ca.toNat = c at V₂
  generalize hT : (s.gpr (treg n)).toNat = top
  have hL' : regsVal s₂ 0 n = regsVal s 0 n :=
    regsVal_kp K₂ fun j _ => by rw [Nat.zero_add]; exact treg_not_mem_tregs (by omega) (by omega) (.inl (by omega))
  have hN' : regsVal s 0 n + 2 ^ (64 * n) * top < 2 * m := by
    rw [← hT, show treg n = treg (0 + n) by rw [Nat.zero_add], ← regsVal_succ_top]; exact hN
  have hc1 : c ≤ 1 := hc ▸ Bool.toNat_le _
  obtain ⟨hct, hsel⟩ := csub_math hm0 hN' (gval_lt' s₂ (bReg n) n) (by have := V₂; omega) hc1
  have hadd : BitVec.ofNat 64 (top + c) = BitVec.ofNat 64 (c + top) := by rw [Nat.add_comm]
  rw [hadd]
  have h4₂ := K₂.at h4 (by simp [tregs])
  refine WP.mono (qsels_ok (n := n) ((((hs₂.writeCarry _ _).write _ _).write _ _)) hn4
    (((h4₂.writeCarry _).write _).write _)
    (by simp only [write_gpr, ite_true]; exact neg_mask hct) o_le (k := n) (Nat.le_refl _))
    fun u ⟨O₃, V₃, K₃⟩ => ⟨?_, ?_, ?_⟩
  · simp only [write_gpr, ite_true] at V₃
    have hr : regsVal (((s₂.writeCarry .r10 (top + c)).write .r11 (BitVec.ofNat 64 0)).write .r10
        (BitVec.ofNat 64 0 - BitVec.ofNat 64 (c + top))) 0 n = regsVal s 0 n := by
      rw [← hL']; exact regsVal_congr fun j _ => by
        simp only [write_gpr, writeCarry_gpr, treg_eq_r10, treg_eq_r11, ite_false]
    have hg : gval (((s₂.writeCarry .r10 (top + c)).write .r11 (BitVec.ofNat 64 0)).write .r10
        (BitVec.ofNat 64 0 - BitVec.ofNat 64 (c + top))) (bReg n) n = gval s₂ (bReg n) n :=
      gval_congr fun j _ => by
        simp only [bReg, write_gpr, writeCarry_gpr, treg_eq_r10, treg_eq_r11, ite_false]
    rw [V₃, hr, hg, regsVal_succ_top, Nat.zero_add, hT, ← hsel]
    simp only [neg_mask_zero hct]
  · simp only [write_mem, RegUpd.mem_writeCarry] at O₃
    rw [← M₂]; exact O₃
  · exact (K₂.mono fun r hr => List.mem_append_right _ hr).trans ((((Kp.writeCarry _ _ (by simp)).trans
      ((Kp.write _ _ (by simp)).trans (Kp.write _ _ (by simp)))).trans
      (K₃.mono fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)))

/-! ## Constants of 64 bits in registers -/

theorem movImm64_ok {s : State} {d : Reg} {w : Nat} (hw : w < 2 ^ 64) {is : List Instr} {Q : State → Prop}
    (k : WP isa (.block is) (s.write d (BitVec.ofNat 64 w)) Q) : WP isa (.block (movImm64 d w ++ is)) s Q := by
  unfold movImm64
  split
  · rename_i h
    exact wp_step (exec_li h) k
  split
  · rename_i _ h
    subst h
    refine wp_step exec_lis (wp_step exec_ori ?_)
    rw [write_write]
    simp only [write_gpr, ite_true]
    exact (by decide : ((((0xffff : BitVec 16) ++ (0 : BitVec 16)).signExtend 64 ||| (0xffff : BitVec 16).setWidth 64)) =
      BitVec.ofNat 64 (2 ^ 64 - 1)) ▸ k
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine wp_movImm fun v hv => ?_
    refine wp_step (exec_lsl (by decide)) (wp_step exec_oris (wp_step exec_ori ?_))
    rw [write_write, write_write, write_write]
    simp only [write_gpr, ite_true]
    have e : (v <<< 32 ||| BitVec.setWidth 64 (BitVec.ofNat 16 (w >>> 16)) <<< 16 |||
        BitVec.setWidth 64 (BitVec.ofNat 16 w)) = BitVec.ofNat 64 w := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
      have hA : v.toNat * 2 ^ 32 % 2 ^ 64 = 2 ^ 32 * (w / 2 ^ 32) := by
        rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by decide, Nat.mul_mod_mul_right, hv, BitVec.toNat_ofNat,
          Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
      have hB : w >>> 16 % 2 ^ 16 % 2 ^ 64 * 2 ^ 16 % 2 ^ 64 = 2 ^ 16 * (w / 2 ^ 16 % 2 ^ 16) := by
        have h1 : w / 2 ^ 16 % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by decide)
        have h2 : w / 2 ^ 16 % 2 ^ 16 % 2 ^ 64 = w / 2 ^ 16 % 2 ^ 16 := Nat.mod_eq_of_lt (Nat.lt_trans h1 (by decide))
        have h3 : w / 2 ^ 16 % 2 ^ 16 * 2 ^ 16 < 2 ^ 64 :=
          Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h1 (by decide)) (by decide)
        rw [Nat.shiftRight_eq_div_pow, h2, Nat.mod_eq_of_lt h3, Nat.mul_comm]
      have hC : w % 2 ^ 16 % 2 ^ 64 = w % 2 ^ 16 :=
        Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
      rw [hA, hB, hC, ← Nat.two_pow_add_eq_or_of_lt (i := 32) (b := 2 ^ 16 * (w / 2 ^ 16 % 2 ^ 16)) (by omega),
        show 2 ^ 32 * (w / 2 ^ 32) + 2 ^ 16 * (w / 2 ^ 16 % 2 ^ 16) =
          2 ^ 16 * (2 ^ 16 * (w / 2 ^ 32) + w / 2 ^ 16 % 2 ^ 16) by omega,
        ← Nat.two_pow_add_eq_or_of_lt (i := 16) (b := w % 2 ^ 16) (by omega)]
      omega
    rw [e]; exact k

theorem mword_lt (m j : Nat) : mword m j < 2 ^ 64 := Nat.mod_lt _ (by decide)

def gwords (m : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => gwords m k + 2 ^ (64 * k) * mword m k

theorem mwords_eq (m : Nat) : ∀ k, gwords m k = m % 2 ^ (64 * k)
  | 0 => by simp [gwords, Nat.mod_one]
  | k + 1 => by
    rw [gwords, mwords_eq m k, mword, Nat.shiftRight_eq_div_pow, show 64 * (k + 1) = 64 * k + 64 by omega, Nat.pow_add,
      Nat.mod_mul, Nat.mul_comm (2 ^ (64 * k))]

/-! ## The multiplication of at most four words -/

theorem gval_of_words {s : State} {f : Nat → Reg} {mem : Mem} {base : Addr} {d : Nat} :
    ∀ {k : Nat}, (∀ j < k, s.gpr (f j) = word mem base (d + 8 * j)) → gval s f k = wordsVal mem base d k
  | 0, _ => rfl
  | k + 1, h => by rw [gval, wordsVal_succ_top, gval_of_words fun j hj => h j (by omega), h k (by omega)]

theorem qloadB_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {n B : Nat} (hn : n ≤ 4)
    (h6 : At s base .r6 B) (hB : B + 8 * n ≤ size) : ∀ {k : Nat}, k ≤ n →
    WP isa (.block ((List.range k).map fun j => .load .d (bReg n j) .r6 (8 * j))) s
      fun u => u.mem = s.mem ∧ (∀ j < k, u.gpr (bReg n j) = word s.mem base (B + 8 * j)) ∧ Kp (tregs (n + 1) k) s u
  | 0, _ => WP.block_nil ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _), Kp.refl _ _⟩
  | k + 1, hk => by
    have hs15 := hs.small
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    refine WP.block_append (WP.mono (qloadB_ok hs hn h6 hB (k := k) (by omega)) fun s₁ ⟨M₁, Z₁, K₁⟩ => ?_)
    refine wp_step (ld_ok (K₁.ws hs) (K₁.at h6 (by simp [tregs])) (by decide) (by omega) (d := 8 * k) (by omega))
      (WP.block_nil ?_)
    refine ⟨M₁, fun j hj => ?_, (K₁.mono fun r hr => by rw [tregs_succ]; exact List.mem_append_left _ hr).trans
      (Kp.write _ _ (by rw [tregs_succ]; exact List.mem_append_right _ (List.mem_singleton_self _)))⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [write_gpr]
      simp only [bReg, treg_ne_of (show n + 1 + j < 10 by omega) (show n + 1 + k < 10 by omega) (by omega), ite_false]
      exact Z₁ j hj
    · rw [write_gpr]; simp only [ite_true]; rw [M₁]

theorem qimmM_ok {s : State} {n m : Nat} (hn : n ≤ 4) : ∀ {k : Nat}, k ≤ n →
    WP isa (.block ((List.range k).flatMap fun j => movImm64 (mReg j) (mword m j))) s
      fun u => u.mem = s.mem ∧ (∀ j < k, u.gpr (mReg j) = BitVec.ofNat 64 (mword m j)) ∧
        Kp ((List.range k).map mReg) s u
  | 0, _ => WP.block_nil ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _), Kp.refl _ _⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.block_append (WP.mono (qimmM_ok (m := m) hn (k := k) (by omega)) fun s₁ ⟨M₁, Z₁, K₁⟩ => ?_)
    rw [← List.append_nil (movImm64 _ _)]
    refine movImm64_ok (mword_lt m k) (WP.block_nil ?_)
    refine ⟨by rw [write_mem, M₁], fun j hj => ?_, (K₁.mono fun r hr => by
        rw [List.map_append]; exact List.mem_append_left _ hr).trans
      (Kp.write _ _ (by rw [List.map_append]; exact List.mem_append_right _ (List.mem_singleton_self _)))⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [write_gpr]
      have : mReg j ≠ mReg k := (by decide : ∀ a < 4, ∀ b < 4, a ≠ b → mReg a ≠ mReg b) j (by omega) k (by omega) (by omega)
      simp only [this, ite_false]
      exact Z₁ j hj
    · rw [write_gpr]; simp only [ite_true]

theorem gval_of_imm {s : State} {f : Nat → Reg} {m : Nat} :
    ∀ {k : Nat}, (∀ j < k, s.gpr (f j) = BitVec.ofNat 64 (mword m j)) → gval s f k = gwords m k
  | 0, _ => rfl
  | k + 1, h => by
    rw [gval, gwords, gval_of_imm fun j hj => h j (by omega), h k (by omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (mword_lt m k)]

/-- What `rmul4` needs: `OpPre` but the modulus in memory. -/
structure RegPre (base : Addr) (size O A B m : Nat) (s : State) : Prop where
  ws : Ws s base size
  r3 : At s base .r3 0
  r4 : At s base .r4 O
  r5 : At s base .r5 A
  r6 : At s base .r6 B
  m0 : 0 < m

/-- `[r4] = [r5] [r6] R⁻¹ mod m`, for `[r6]` below `m` and `n ≤ 4`, with
the accumulator, `[b]` and the modulus in registers. -/
theorem rmul4_ok {M : Mod} {base : Addr} {size acc O A B m : Nat} {s : State} (hp : RegPre base size O A B m s)
    (hL : OpLay M size acc O A B) (hn4 : M.n ≤ 4) (hm : m < 2 ^ (64 * M.n))
    (sta : M.tmp + 8 * M.n ≤ A ∨ A + 8 * M.n ≤ M.tmp) (stb : M.tmp + 8 * M.n ≤ B ∨ B + 8 * M.n ≤ M.tmp)
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) (hb : wordsVal s.mem base B M.n < m) :
    WP isa (rmul4 M m acc) s fun u =>
      wordsVal u.mem base O M.n < m ∧
      wordsVal u.mem base O M.n * 2 ^ (64 * M.n) % m = wordsVal s.mem base A M.n * wordsVal s.mem base B M.n % m ∧
      Outs base (opOuts M acc O) s.mem u.mem ∧ Kp (.r6 :: opClob) s u := by
  have hn := hp.ws.nowrap
  have hs15 := hp.ws.small
  have hL' := hL
  obtain ⟨n0, acc_le, tmp_le, mo_le, o_le, a_le, b_le, acc4, tmp4, sat, am, ao, aa, ab, tm, to⟩ := hL'
  refine WP.seq ?_
  simp only [rsave, rzero, qload, List.append_assoc]
  refine WP.block_append (WP.mono (rsave_ok hp.ws hp.r3 acc4 (acc := acc) (k := 2 * M.n + 1)
    (by omega)) fun s₁ ⟨O₁, Z₁, K₁, G₁⟩ => ?_)
  -- `mpReg` saved at `[M.tmp]`, then `m'` in it.
  refine wp_step (std_ok (K₁.ws hp.ws) (K₁.at hp.r3) (by decide) tmp4 (d := M.tmp) (by omega)) ?_
  refine movImm64_ok M.minv.isLt (wp_gen fun s₂ hs₂ => ?_)
  have M₂ : s₂.mem = s₁.mem.writeW (off base M.tmp) (s.gpr (mpReg M.n)) := by
    rw [hs₂, write_mem, G₁, Nat.zero_add]
  have R₂ : ∀ r, s₂.gpr r = if r = mpReg M.n then BitVec.ofNat 64 M.minv.toNat else s.gpr r := fun r => by
    rw [hs₂, write_gpr]; show (if _ then _ else s₁.gpr r) = _; rw [G₁]
  have K₂ : Kp [mpReg M.n] s s₂ := by
    rw [hs₂]; exact ((K₁.mono (by simp)).trans (Kp.store _ _ _)).trans (Kp.write _ _ (List.mem_singleton_self _))
  have W₂ := writeW_outside s₁.mem base (d := M.tmp) (s.gpr (mpReg M.n)) (by omega)
  refine WP.block_append (WP.mono (rzero_ok (s := s₂) (k := M.n + 1) (by omega)) fun s₃ ⟨M₃, Z₃, K₃⟩ => ?_)
  have keep3 : ∀ r : Reg, r ∉ hiRegs → s₃.gpr r = s.gpr r := fun r h2 => by
    rw [K₃.gpr _ (fun h => by obtain ⟨j, -, e⟩ := List.mem_map.mp h; exact h2 (e ▸ treg_hi _)),
      K₂.gpr _ (fun h => h2 (by rw [List.mem_singleton.mp h]; exact treg_hi _))]
  have hs₃ : Ws s₃ base size := K₃.ws (K₂.ws hp.ws)
  have h6₃ : At s₃ base .r6 B := by rw [At, keep3 _ (by decide)]; exact hp.r6
  have h3₃ : At s₃ base .r3 0 := by rw [At, keep3 _ (by decide)]; exact hp.r3
  refine WP.block_append (WP.mono (qloadB_ok hs₃ hn4 h6₃ b_le (k := M.n) (Nat.le_refl _)) fun s₄ ⟨M₄, Z₄, K₄⟩ => ?_)
  have h3₄ : At s₄ base .r3 0 := K₄.at h3₃ (by simp [tregs])
  refine WP.block_append (WP.mono (qimmM_ok (s := s₄) (m := m) hn4 (k := M.n) (Nat.le_refl _))
    fun s₅ ⟨M₅, Z₅, K₅⟩ => ?_)
  refine wp_step (exec_li (by omega)) (WP.block_nil ?_)
  generalize hu : s₅.write .r8 (BitVec.ofNat 64 M.n) = u
  have hum : u.mem = s₂.mem := by rw [← hu]; show s₅.mem = s₂.mem; rw [M₅, M₄, M₃]
  have nm5 : ∀ r : Reg, (∀ j < M.n, r ≠ mReg j) → s₅.gpr r = s₄.gpr r := fun r h => K₅.gpr _ (by
    intro h'; obtain ⟨j, hj, e⟩ := List.mem_map.mp h'; rw [List.mem_range] at hj; exact h j hj e.symm)
  have nb4 : ∀ r : Reg, r ∉ hiRegs → s₄.gpr r = s₃.gpr r := fun r h => K₄.gpr _ (by
    intro h'; obtain ⟨j, -, e⟩ := List.mem_map.mp h'; exact h (e ▸ treg_hi _))
  have keep : ∀ r : Reg, r ∉ [Reg.r0, .r6, .r7, .r8, .r10, .r11] → r ∉ hiRegs → u.gpr r = s.gpr r := by
    intro r h1 h2
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1
    rw [← hu]
    simp only [write_gpr, h1.2.2.2.1, ite_false]
    rw [nm5 _ (fun j hj => by
      have := (by decide : ∀ j < 4, mReg j = .r6 ∨ mReg j = .r7 ∨ mReg j = .r10 ∨ mReg j = .r0) j (by omega)
      rcases this with e | e | e | e <;> rw [e] <;> simp_all), nb4 _ h2, keep3 _ h2]
  have Ous : Outs base (opOuts M acc O) s.mem u.mem := by
    rw [hum]
    have o₁ : Outs base (opOuts M acc O) s.mem s₁.mem :=
      Outs.of_outside (O₁.mono (o' := acc) (n' := 4 * (4 * M.n + 2)) (Nat.le_refl _) (by omega))
        (List.mem_cons_self ..)
    have o₂ : Outs base (opOuts M acc O) s₁.mem s₂.mem := by
      rw [M₂]; exact Outs.of_outside (W₂.mono (o' := M.tmp) (n' := 8 * M.n) (Nat.le_refl _) (by omega))
        (by simp [opOuts])
    exact o₁.trans o₂
  have hmpm : word u.mem base M.tmp = s.gpr (mpReg M.n) := by rw [hum, M₂, word_writeW_self]
  have hAu : wordsVal u.mem base A M.n = wordsVal s.mem base A M.n := by
    rw [hum, M₂, W₂.wordsVal (by omega) (by omega), O₁.wordsVal (by omega) (by omega)]
  have hBu : wordsVal u.mem base B M.n = wordsVal s.mem base B M.n := by
    rw [hum, M₂, W₂.wordsVal (by omega) (by omega), O₁.wordsVal (by omega) (by omega)]
  have hsv : ∀ j < 2 * M.n + 1, word u.mem base (acc + 8 * j) = s.gpr (treg j) := fun j hj => by
    rw [hum, M₂, W₂.word (by omega) (by omega), Z₁ j hj]
  have hws : Ws u base size := by rw [← hu]; exact (K₅.ws (K₄.ws hs₃)).write _ _
  have hreg : ∀ r : Reg, r ≠ .r8 → u.gpr r = s₅.gpr r := fun r h => by
    rw [← hu]; simp only [write_gpr, h, ite_false]
  have hBv : gval u (bReg M.n) M.n = wordsVal u.mem base B M.n := by
    rw [hBu, ← O₁.wordsVal (by omega) (by omega), ← W₂.wordsVal (by omega) (by omega), ← M₂, ← M₃]
    refine gval_of_words fun j hj => ?_
    rw [hreg (bReg M.n j) (treg_ne (r := .r8) (by decide) _),
      nm5 (bReg M.n j) (fun i hi e => mReg_ne_treg (by omega) _ e.symm), Z₄ j hj]
  have hMv : gval u mReg M.n = m := by
    rw [gval_of_imm fun j hj => by rw [hreg _ (mReg_ne (by omega)).2.2.2.2.2.2.2, Z₅ j hj], mwords_eq,
      Nat.mod_eq_of_lt hm]
  have hz : regsVal u 0 (M.n + 1) = 0 := by
    have : ∀ j < M.n + 1, u.gpr (treg (0 + j)) = 0 := fun j hj => by
      rw [Nat.zero_add, hreg _ (treg_ne (r := .r8) (by decide) _), nm5 _ (fun i hi e => mReg_ne_treg (by omega) _ e.symm),
        K₄.gpr _ (treg_not_mem_tregs (by omega) (by omega) (by omega))]
      exact Z₃ j hj
    exact regsVal_zero_of this
  have hmp : (u.gpr (mpReg M.n)).toNat = M.minv.toNat := by
    rw [hreg (mpReg M.n) (treg_ne (r := .r8) (by decide) _),
      nm5 (mpReg M.n) (fun j hj e => mReg_ne_treg (by omega) _ e.symm),
      K₄.gpr (mpReg M.n) (treg_not_mem_tregs (i := 2 * M.n + 1) (by omega) (by omega) (.inr (by omega))),
      K₃.gpr (mpReg M.n) (treg_not_mem_tregs (i := 2 * M.n + 1) (by omega) (by omega) (.inr (by omega))), R₂,
      ite_eq_left rfl,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt M.minv.isLt]
  have P : QPre base M size A B m u := ⟨hws, by rw [At, keep _ (by decide) (by decide)]; exact hp.r3, n0, hn4, a_le,
    by rw [hBv], hMv, by rw [hmp]; exact hinv, fun h => hmp.trans h, by rw [hBu]; exact hb, hm⟩
  -- The invariant at word 0.
  have h0 : QLoopInv base M A B m 0 u u := by
    refine ⟨?_, ?_, rfl, Kp.refl _ _, ?_, ?_⟩
    · rw [Nat.mul_zero, Nat.add_zero, At, keep _ (by decide) (by decide)]; exact hp.r5
    · rw [← hu]; simp only [write_gpr, ite_true, Nat.sub_zero]
    · rw [hz]; have := hp.m0; omega
    · exact ⟨0, by rw [hz]; simp [wordsVal]⟩
  refine WP.seq (WP.mono (qloop_ok P h0) fun t I => ?_)
  -- The reduction, and the registers restored.
  obtain ⟨U, hU⟩ := I.cong
  have h3t : At t base .r3 0 := by
    rw [At, I.kp.gpr _ (lo_not_qclob (by decide) (by decide)), keep _ (by decide) (by decide)]; exact hp.r3
  have h4t : At t base .r4 O := by
    rw [At, I.kp.gpr _ (lo_not_qclob (by decide) (by decide)), keep _ (by decide) (by decide)]; exact hp.r4
  have hMt : gval t mReg M.n = m := by
    rw [← hMv]; exact gval_congr fun j hj => I.kp.gpr _ (mReg_not_qclob (by omega))
  refine WP.block_append (WP.mono (qcsubR_ok (I.kp.ws hws) h4t n0 hn4 o_le hMt hm I.lt) fun v ⟨V₃, O₃, Kc⟩ => ?_)
  have hsv' : ∀ j < 2 * M.n + 1, word v.mem base (acc + 8 * j) = s.gpr (treg j) := fun j hj => by
    rw [O₃.word (by omega) (by omega), I.mem, hsv j hj]
  have hmpv : word v.mem base M.tmp = s.gpr (mpReg M.n) := by
    rw [O₃.word (by omega) (by omega), I.mem, hmpm]
  have hwv := Kc.ws (I.kp.ws hws)
  have h3v : At v base .r3 0 := Kc.at h3t (by simp [tregs])
  refine WP.block_append (WP.mono (rrestore_ok hwv h3v acc4 (k := 2 * M.n + 1) (by omega) (by omega))
    fun w ⟨M₆, R₆, K₆⟩ => ?_)
  refine wp_step (ld0_ok (K₆.ws hwv) (K₆.at h3v (by simp [tregs])) (by decide) tmp4 (by omega))
    (WP.block_nil ⟨?_, ?_, ?_, ?_⟩)
  · rw [write_mem, M₆, V₃]; exact Nat.mod_lt _ hp.m0
  · rw [write_mem, M₆, V₃, Nat.mod_mul_mod, Nat.mul_comm, hU, hAu, hBu, Nat.add_mul_mod_self_right]
  · rw [write_mem, M₆]
    refine (Ous.trans ?_).trans (Outs.of_outside O₃ (by simp [opOuts]))
    rw [I.mem]; exact Outs.refl _ _ _
  · have hrest : ∀ j < 2 * M.n + 2, (w.write (mpReg M.n) (word w.mem base M.tmp)).gpr (treg j) = s.gpr (treg j) :=
      fun j hj => by
        rw [write_gpr]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [ite_eq_right (show treg j ≠ mpReg M.n from treg_ne_of (by omega) (by omega) (by omega)), R₆ j hj,
            hsv' j hj]
        · rw [ite_eq_left (show treg (2 * M.n + 1) = mpReg M.n from rfl), M₆, hmpv]; rfl
    have memL : ∀ r, (r ∈ [Reg.r0, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] ∨ ∃ j ≤ 2 * M.n + 1, r = treg j) →
        r ∈ (.r6 :: opClob) ++ tregs 0 (2 * M.n + 2) := by
      intro r h
      rcases h with h | ⟨j, hj, rfl⟩
      · exact List.mem_append_left _ (by revert h; revert r; decide)
      · exact List.mem_append_right _ (by simpa using treg_mem_tregs (d := 0) (k := 2 * M.n + 2) (j := j) (by omega))
    have tsub : ∀ d k, d + k ≤ 2 * M.n + 2 → ∀ r ∈ tregs d k, r ∈ (.r6 :: opClob) ++ tregs 0 (2 * M.n + 2) :=
      fun d k hk r hr => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
        rw [List.mem_range] at hj
        exact memL _ (.inr ⟨d + j, by omega, rfl⟩)
    have K₀u : Kp ((.r6 :: opClob) ++ tregs 0 (2 * M.n + 2)) s u := by
      rw [← hu]
      refine (((K₂.mono fun r hr => by
          rw [List.mem_singleton.mp hr]; exact memL _ (.inr ⟨2 * M.n + 1, Nat.le_refl _, rfl⟩)).trans
        (K₃.mono (tsub 0 (M.n + 1) (by omega)))).trans
        (K₄.mono (tsub (M.n + 1) M.n (by omega)))).trans
        ((K₅.mono fun r hr => ?_).trans (Kp.write _ _ (memL _ (.inl (by simp)))))
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      rw [List.mem_range] at hj
      exact memL _ (.inl ((by decide : ∀ j < 4, mReg j ∈ [Reg.r0, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]) j (by omega)))
    have Kall : Kp ((.r6 :: opClob) ++ tregs 0 (2 * M.n + 2)) s (w.write (mpReg M.n) (word w.mem base M.tmp)) :=
      (((K₀u.trans (I.kp.mono fun r hr => by
          rcases List.mem_cons.mp hr with h | hr
          · exact memL _ (.inl (by simp [h]))
          rcases List.mem_cons.mp hr with h | hr
          · exact memL _ (.inl (by simp [h]))
          rcases List.mem_append.mp hr with h | h
          · exact memL _ (.inl (by simp at h; rcases h with rfl | rfl | rfl <;> simp))
          · exact tsub 0 (M.n + 1) (by omega) r h)).trans
        (Kc.mono fun r hr => (List.mem_append.mp hr).elim
          (fun h => memL _ (.inl (by simp at h; rcases h with rfl | rfl | rfl <;> simp)))
          (tsub (M.n + 1) M.n (by omega) r))).trans
        (K₆.mono (tsub 0 (2 * M.n + 1) (by omega)))).trans
        (Kp.write _ _ (memL _ (.inr ⟨2 * M.n + 1, Nat.le_refl _, rfl⟩)))
    refine ⟨fun r hr => ?_, Kall.rd, Kall.wr, Kall.sp, Kall.lr⟩
    by_cases ht : r ∈ tregs 0 (2 * M.n + 2)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
      rw [List.mem_range] at hj
      rw [Nat.zero_add]; exact hrest j hj
    · exact Kall.gpr r (fun h => (List.mem_append.mp h).elim hr ht)

/-! ## Sums and differences of at most four words: the chains -/

theorem vReg_ne {j : Nat} (hj : j < 4) : vReg j ∈ [Reg.r7, .r8, .r9, .r10] :=
  (by decide : ∀ j < 4, vReg j ∈ [Reg.r7, .r8, .r9, .r10]) j hj

theorem vReg_inj {i j : Nat} (hi : i < 4) (hj : j < 4) (h : i ≠ j) : vReg i ≠ vReg j :=
  (by decide : ∀ i < 4, ∀ j < 4, i ≠ j → vReg i ≠ vReg j) i hi j hj h

/-- The registers `vReg 0`, …, `vReg (k - 1)`. -/
def vregs (k : Nat) : List Reg := (List.range k).map vReg

theorem vregs_succ (k : Nat) : vregs (k + 1) = vregs k ++ [vReg k] := by
  simp only [vregs, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem vregs_sub {k : Nat} (hk : k ≤ 4) : ∀ r ∈ vregs k, r ∈ [Reg.r7, .r8, .r9, .r10] := by
  intro r hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  rw [List.mem_range] at hj
  exact vReg_ne (by omega)

theorem not_vregs {r : Reg} (h : r ∉ [Reg.r7, .r8, .r9, .r10]) {k : Nat} (hk : k ≤ 4) : r ∉ vregs k :=
  fun h' => h (vregs_sub hk r h')

theorem vReg_not_vregs {j k : Nat} (hj : j < 4) (hk : k ≤ j) : vReg j ∉ vregs k := by
  intro h
  obtain ⟨i, hi, e⟩ := List.mem_map.mp h
  rw [List.mem_range] at hi
  exact vReg_inj (by omega) hj (by omega) e

/-- The low `k` words of `m`, word by word. -/
theorem ldSteps_succ (sub : Bool) (k : Nat) :
    (List.range (k + 1)).flatMap (ldStep sub) = (List.range k).flatMap (ldStep sub) ++ ldStep sub k := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The low `k` words of `[r5] + [r6]` (for `sub`, of `[r5] + 2^(64 k) - [r6]`)
to `vReg`, the carry (no borrow) to CA. -/
theorem ldSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {sub : Bool} {A B W : Nat}
    (h5 : At s base .r5 A) (h6 : At s base .r6 B) (hA : A + 8 * W ≤ size) (hB : B + 8 * W ≤ size) (hW : W ≤ 4) :
    ∀ {k : Nat}, k ≤ W →
    WP isa (.block ((List.range k).flatMap (ldStep sub))) s fun u =>
      gval u vReg k + 2 ^ (64 * k) * cOf sub k u.ca + (if sub then wordsVal s.mem base B k else 0) =
        wordsVal s.mem base A k + (if sub then 2 ^ (64 * k) - 1 else wordsVal s.mem base B k) + sub.toNat ∧
      u.mem = s.mem ∧ Kp (.r11 :: .r12 :: vregs k) s u
  | 0, _ => WP.block_nil ⟨by cases sub <;> simp [gval, wordsVal, cOf], rfl, Kp.refl _ _⟩
  | k + 1, hk => by
    have hs15 := hs.small
    rw [ldSteps_succ]
    refine WP.block_append (WP.mono (ldSteps_ok hs h5 h6 hA hB hW (k := k) (by omega)) fun s₁ ⟨V₁, M₁, K₁⟩ => ?_)
    have hs₁ := K₁.ws hs
    have h5₁ : At s₁ base .r5 A := K₁.at h5 (by simp [not_vregs (r := .r5) (by decide) (show k ≤ 4 by omega)])
    have h6₁ : At s₁ base .r6 B := K₁.at h6 (by simp [not_vregs (r := .r6) (by decide) (show k ≤ 4 by omega)])
    have hvk := vReg_ne (show k < 4 by omega)
    simp only [ldStep]
    refine wp_step (ld_ok hs₁ h5₁ (by decide) (by omega) (d := 8 * k) (by omega)) ?_
    refine wp_step (ld_ok (hs₁.write _ _) (h6₁.write _) (by decide) (by omega) (d := 8 * k) (by omega)) ?_
    refine wp_step (exec_carryOp _ _ _ _ _ _) ?_
    refine wp_gen fun u hu => WP.block_nil ?_
    simp only [write_gpr, write_mem, ite_true, reduceCtorEq, ite_false, RegUpd.ca_write] at hu
    generalize hx : word s₁.mem base (A + 8 * k) = x at hu
    generalize hy : word s₁.mem base (B + 8 * k) = y at hu
    generalize hv : x.toNat + (if sub then 2 ^ 64 - 1 - y.toNat else y.toNat) + cOf sub k s₁.ca = v at hu
    have hc : cOf sub k s₁.ca ≤ 1 := by unfold cOf; split <;> exact Bool.toNat_le _
    have e := RegUpd.toNat_add_ca ((s₁.write .r11 x).write .r12 y) (r := vReg k) (v := v)
      (by rw [← hv]; have := x.isLt; have := y.isLt; split <;> omega)
    rw [← hu] at e
    have hgk : gval u vReg k = gval s₁ vReg k := gval_congr fun j hj => by
      rw [hu]
      simp only [writeCarry_gpr, write_gpr, vReg_inj (show j < 4 by omega) (show k < 4 by omega) (by omega), ite_false]
      have : vReg j ∈ [Reg.r7, .r8, .r9, .r10] := vReg_ne (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with h | h | h | h <;> rw [h] <;> simp
    rw [M₁] at hx hy
    refine ⟨?_, by rw [hu]; show s₁.mem = s.mem; exact M₁, ?_⟩
    · rw [gval, hgk, wordsVal_succ_top, wordsVal_succ_top, hx, hy, show cOf sub (k + 1) u.ca = u.ca.toNat from rfl,
        pow64_succ]
      have hP : 1 ≤ 2 ^ (64 * k) := Nat.one_le_two_pow
      generalize 2 ^ (64 * k) = P at *
      generalize cOf sub k s₁.ca = c at *
      generalize u.ca.toNat = c' at *
      generalize (u.gpr (vReg k)).toNat = w at *
      have e3 := congrArg (P * ·) e
      simp only [Nat.mul_add] at e3
      have hyl := y.isLt
      cases sub
      · simp only [ite_false, Bool.false_eq_true, Nat.add_zero, Bool.toNat_false] at V₁ hv ⊢
        rw [← hv] at e3
        simp only [Nat.mul_add] at e3
        grind
      · simp only [ite_true, Bool.toNat_true] at V₁ hv ⊢
        rw [← hv] at e3
        have hA' : P * (2 ^ 64 - 1 - y.toNat) + P * y.toNat = 2 ^ 64 * P - P := by
          rw [← Nat.mul_add, show 2 ^ 64 - 1 - y.toNat + y.toNat = 2 ^ 64 - 1 by omega, Nat.mul_sub, Nat.mul_one,
            Nat.mul_comm]
        have hC : P ≤ 2 ^ 64 * P := Nat.le_mul_of_pos_left _ (by decide)
        simp only [Nat.mul_add] at e3
        have hB' : P * (2 ^ 64 * c') = 2 ^ 64 * P * c' := by rw [Nat.mul_left_comm, Nat.mul_assoc]
        rw [hB'] at e3
        generalize P * (2 ^ 64 - 1 - y.toNat) = A1 at *
        generalize P * y.toNat = B1 at *
        generalize 2 ^ 64 * P * c' = D at *
        generalize 2 ^ 64 * P = E at *
        omega
    · rw [hu]
      refine (K₁.mono ?_).trans (((Kp.write _ _ (by simp)).trans (Kp.write _ _ (by simp))).trans
        (Kp.writeCarry _ _ (by simp [vregs_succ])))
      intro r hr
      simp only [List.mem_cons] at hr ⊢
      rcases hr with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (by rw [vregs_succ]; exact List.mem_append_left _ h))

theorem subMs_succ (m k : Nat) :
    (List.range (k + 1)).flatMap (subMStep m) = (List.range k).flatMap (subMStep m) ++ subMStep m k := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The low `k` words of `m` subtracted from `vReg`, in place, no borrow to CA. -/
theorem subMs_ok {s : State} {m W : Nat} (hW : W ≤ 4) :
    ∀ {k : Nat}, k ≤ W →
    WP isa (.block ((List.range k).flatMap (subMStep m))) s fun u =>
      gval u vReg k + 2 ^ (64 * k) * cOf true k u.ca + gwords m k = gval s vReg k + (2 ^ (64 * k) - 1) + 1 ∧
      u.mem = s.mem ∧ Kp (.r12 :: vregs k) s u
  | 0, _ => WP.block_nil ⟨by simp [gval, gwords, cOf], rfl, Kp.refl _ _⟩
  | k + 1, hk => by
    rw [subMs_succ]
    refine WP.block_append (WP.mono (subMs_ok hW (k := k) (by omega)) fun s₁ ⟨V₁, M₁, K₁⟩ => ?_)
    simp only [subMStep]
    refine movImm64_ok (mword_lt m k) ?_
    refine wp_step (exec_carryOp _ _ _ _ _ _) ?_
    refine wp_gen fun u hu => WP.block_nil ?_
    have hvk := vReg_ne (show k < 4 by omega)
    have h12 : vReg k ≠ .r12 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hvk; rcases hvk with h | h | h | h <;> rw [h] <;> decide
    simp only [write_gpr, ite_true, h12, ite_false, RegUpd.ca_write, ite_true] at hu
    have ht : s₁.gpr (vReg k) = s.gpr (vReg k) := K₁.gpr _ (by
      intro h; rcases List.mem_cons.mp h with e | e
      · exact h12 e
      · exact vReg_not_vregs (show k < 4 by omega) (Nat.le_refl _) e)
    generalize hv : (s₁.gpr (vReg k)).toNat + (2 ^ 64 - 1 - (BitVec.ofNat 64 (mword m k)).toNat) + cOf true k s₁.ca = v at hu
    have hc : cOf true k s₁.ca ≤ 1 := by unfold cOf; split <;> exact Bool.toNat_le _
    have e := RegUpd.toNat_add_ca (s₁.write .r12 (BitVec.ofNat 64 (mword m k))) (r := vReg k) (v := v)
      (by rw [← hv]; have := (s₁.gpr (vReg k)).isLt; omega)
    rw [← hu] at e
    have hgk : gval u vReg k = gval s₁ vReg k := gval_congr fun j hj => by
      rw [hu]
      simp only [writeCarry_gpr, write_gpr, vReg_inj (show j < 4 by omega) (show k < 4 by omega) (by omega), ite_false]
      have : vReg j ∈ [Reg.r7, .r8, .r9, .r10] := vReg_ne (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with h | h | h | h <;> rw [h] <;> simp
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (mword_lt m k)] at hv
    refine ⟨?_, by rw [hu]; show s₁.mem = s.mem; exact M₁, ?_⟩
    · rw [gval, gval, hgk, gwords, ← ht, show cOf true (k + 1) u.ca = u.ca.toNat from rfl, pow64_succ]
      have hP : 1 ≤ 2 ^ (64 * k) := Nat.one_le_two_pow
      have hyl := mword_lt m k
      generalize 2 ^ (64 * k) = P at *
      generalize cOf true k s₁.ca = c at *
      generalize u.ca.toNat = c' at *
      generalize (u.gpr (vReg k)).toNat = w at *
      generalize mword m k = y at *
      rw [← hv] at e
      have e3 := congrArg (P * ·) e
      simp only [Nat.mul_add] at e3
      have hA' : P * (2 ^ 64 - 1 - y) + P * y = 2 ^ 64 * P - P := by
        rw [← Nat.mul_add, show 2 ^ 64 - 1 - y + y = 2 ^ 64 - 1 by omega, Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
      have hC : P ≤ 2 ^ 64 * P := Nat.le_mul_of_pos_left _ (by decide)
      have hB' : P * (2 ^ 64 * c') = 2 ^ 64 * P * c' := by rw [Nat.mul_left_comm, Nat.mul_assoc]
      rw [hB'] at e3
      generalize P * (2 ^ 64 - 1 - y) = A1 at *
      generalize P * y = B1 at *
      generalize 2 ^ 64 * P * c' = D at *
      generalize 2 ^ 64 * P = E at *
      omega
    · rw [hu]
      refine (K₁.mono ?_).trans ((Kp.write _ _ (List.mem_cons_self ..)).trans
        (Kp.writeCarry _ _ (by simp [vregs_succ])))
      intro r hr
      rcases List.mem_cons.mp hr with h | h
      · exact List.mem_cons.mpr (.inl h)
      · exact List.mem_cons.mpr (.inr (by rw [vregs_succ]; exact List.mem_append_left _ h))

theorem backs_succ (m k : Nat) :
    (List.range (k + 1)).flatMap (backStep m) = (List.range k).flatMap (backStep m) ++ backStep m k := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem and_mask (x mk : BitVec 64) (h : mk = 0 ∨ mk = BitVec.allOnes 64) :
    (x &&& mk).toNat = if mk = 0 then 0 else x.toNat := by
  rcases h with rfl | rfl
  · simp
  · have : BitVec.allOnes 64 ≠ 0 := by decide
    simp only [this, ite_false, BitVec.and_allOnes]

/-- The low `k` words of `vReg + (m under the mask r11)` to `[r4]`, the carry
to CA. -/
theorem backs_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {m O W : Nat} (hW : W ≤ 4)
    (h4 : At s base .r4 O) (hO : O + 8 * W ≤ size) (hmk : s.gpr .r11 = 0 ∨ s.gpr .r11 = BitVec.allOnes 64) :
    ∀ {k : Nat}, k ≤ W →
    WP isa (.block ((List.range k).flatMap (backStep m))) s fun u =>
      wordsVal u.mem base O k + 2 ^ (64 * k) * cOf false k u.ca =
        gval s vReg k + (if s.gpr .r11 = 0 then 0 else gwords m k) ∧
      Outside base O (8 * k) s.mem u.mem ∧ Kp (.r12 :: vregs k) s u
  | 0, _ => WP.block_nil ⟨by simp [gval, gwords, wordsVal, cOf], Outside.refl _ _ _ _, Kp.refl _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    have hs15 := hs.small
    rw [backs_succ]
    refine WP.block_append (WP.mono (backs_ok hs hW h4 hO hmk (k := k) (by omega)) fun s₁ ⟨V₁, O₁, K₁⟩ => ?_)
    have hvk := vReg_ne (show k < 4 by omega)
    have h12 : vReg k ≠ .r12 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hvk; rcases hvk with h | h | h | h <;> rw [h] <;> decide
    have h11 : s₁.gpr .r11 = s.gpr .r11 := K₁.gpr _ (by simp [not_vregs (r := .r11) (by decide) (show k ≤ 4 by omega)])
    have h4₁ : At s₁ base .r4 O := K₁.at h4 (by simp [not_vregs (r := .r4) (by decide) (show k ≤ 4 by omega)])
    have ht : s₁.gpr (vReg k) = s.gpr (vReg k) := K₁.gpr _ (by
      intro h; rcases List.mem_cons.mp h with e | e
      · exact h12 e
      · exact vReg_not_vregs (show k < 4 by omega) (Nat.le_refl _) e)
    have hs₁ := K₁.ws hs
    simp only [backStep]
    refine movImm64_ok (mword_lt m k) ?_
    refine wp_step exec_logic ?_
    refine wp_step (exec_carryOp _ _ _ _ _ _) ?_
    refine wp_gen fun t₂ ht₂ => ?_
    have h4v : vReg k ≠ .r4 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hvk; rcases hvk with h | h | h | h <;> rw [h] <;> decide
    simp only [write_gpr, ite_true, h12, ite_false, RegUpd.ca_write, reduceCtorEq, h11, Bool.false_eq_true] at ht₂
    generalize hw : BitVec.ofNat 64 (mword m k) &&& s.gpr .r11 = w at ht₂
    have hwv : w.toNat = if s.gpr .r11 = 0 then 0 else mword m k := by
      rw [← hw, and_mask _ _ hmk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (mword_lt m k)]
    generalize hv : (s₁.gpr (vReg k)).toNat + w.toNat + cOf false k s₁.ca = v at ht₂
    have hc : cOf false k s₁.ca ≤ 1 := by unfold cOf; split <;> simp [Bool.toNat_le]
    have e := RegUpd.toNat_add_ca ((s₁.write .r12 (BitVec.ofNat 64 (mword m k))).write .r12 w) (r := vReg k) (v := v)
      (by rw [← hv]; have := (s₁.gpr (vReg k)).isLt; have := w.isLt; omega)
    rw [← ht₂] at e
    have h4₂ : At t₂ base .r4 O := by
      rw [At, ht₂, writeCarry_gpr, write_gpr, write_gpr]
      simp only [h4v.symm, reduceCtorEq, ite_false]; exact h4₁
    have hm₂ : t₂.mem = s₁.mem := by rw [ht₂]; rfl
    have hws₂ : Ws t₂ base size := by rw [ht₂]; exact ((hs₁.write _ _).write _ _).writeCarry _ _
    refine wp_step (std_ok hws₂ h4₂ (by decide) (by omega) (d := 8 * k) (by omega)) (WP.block_nil ?_)
    have W' := writeW_outside s₁.mem base (d := O + 8 * k) (t₂.gpr (vReg k)) (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [show ({ t₂ with mem := _ } : State).ca = t₂.ca from rfl, hm₂, show cOf false (k + 1) t₂.ca = t₂.ca.toNat from rfl,
        show ({ t₂ with mem := s₁.mem.writeW (off base (O + 8 * k)) (t₂.gpr (vReg k)) } : State).mem =
          s₁.mem.writeW (off base (O + 8 * k)) (t₂.gpr (vReg k)) from rfl,
        wordsVal_succ_top, W'.wordsVal (by omega) (by omega), word_writeW_self, gval, gwords, pow64_succ, ← ht]
      have hP : 1 ≤ 2 ^ (64 * k) := Nat.one_le_two_pow
      generalize 2 ^ (64 * k) = P at *
      generalize cOf false k s₁.ca = c at *
      generalize t₂.ca.toNat = c' at *
      generalize (t₂.gpr (vReg k)).toNat = x at *
      rw [← hv] at e
      have e3 := congrArg (P * ·) e
      simp only [Nat.mul_add] at e3
      have hB' : P * (2 ^ 64 * c') = 2 ^ 64 * P * c' := by rw [Nat.mul_left_comm, Nat.mul_assoc]
      rw [hB'] at e3
      by_cases hz : s.gpr .r11 = 0
      · simp only [hz, ite_true] at hwv V₁ ⊢
        rw [hwv, Nat.mul_zero, Nat.add_zero] at e3
        generalize P * c = Pc at *
        generalize P * x = Px at *
        generalize P * (s.gpr (vReg k)).toNat = Ps at *
        generalize 2 ^ 64 * P * c' = D at *
        omega
      · simp only [hz, ite_false] at hwv V₁ ⊢
        rw [hwv] at e3
        generalize P * c = Pc at *
        generalize P * x = Px at *
        generalize P * (s.gpr (vReg k)).toNat = Ps at *
        generalize 2 ^ 64 * P * c' = D at *
        generalize P * mword m k = Pm at *
        omega
    · rw [hm₂]
      exact (O₁.mono (Nat.le_refl _) (by omega)).trans (W'.mono (by omega) (by omega))
    · have K₂ : Kp (.r12 :: vregs (k + 1)) s₁ t₂ := by
        rw [ht₂]; exact ((Kp.write _ _ (List.mem_cons_self ..)).trans
          (Kp.write _ _ (List.mem_cons_self ..))).trans (Kp.writeCarry _ _ (by simp [vregs_succ]))
      refine (K₁.mono ?_).trans (K₂.trans (Kp.store _ _ _))
      intro r hr
      rcases List.mem_cons.mp hr with h | h
      · exact List.mem_cons.mpr (.inl h)
      · exact List.mem_cons.mpr (.inr (by rw [vregs_succ]; exact List.mem_append_left _ h))

/-! ## Sums and differences of at most four words -/

theorem gval_vregs_kp {s t : State} {rs : List Reg} (K : Kp rs s t) {k : Nat} (hk : k ≤ 4)
    (h : ∀ r ∈ rs, r ∉ [Reg.r7, .r8, .r9, .r10]) : gval t vReg k = gval s vReg k :=
  gval_congr fun j hj => K.gpr _ fun hr => h _ hr (vReg_ne (by omega))

/-- What `add4` and `sub4` need: the pointers, and the numbers in the working
space. -/
structure AsPre (s : State) (base : Addr) (size n O A B : Nat) : Prop where
  ws : Ws s base size
  r4 : At s base .r4 O
  r5 : At s base .r5 A
  r6 : At s base .r6 B
  n0 : 0 < n
  n4 : n ≤ 4
  o_le : O + 8 * n ≤ size
  a_le : A + 8 * n ≤ size
  b_le : B + 8 * n ≤ size

/-- The registers `add4` and `sub4` write. -/
def asClob : List Reg := [.r0, .r7, .r8, .r9, .r10, .r11, .r12]

theorem vregs_asClob {k : Nat} (hk : k ≤ 4) : ∀ r ∈ vregs k, r ∈ asClob := fun r hr => by
  have := vregs_sub hk r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl <;> decide

/-- `[r4] = [r5] + [r6] mod m`, for `n ≤ 4` words. -/
theorem add4_ok {s : State} {base : Addr} {size n m O A B : Nat} (hp : AsPre s base size n O A B)
    (hm : m < 2 ^ (64 * n)) (hab : wordsVal s.mem base A n + wordsVal s.mem base B n < 2 * m) :
    WP isa (.block (add4 n m)) s fun u =>
      wordsVal u.mem base O n = (wordsVal s.mem base A n + wordsVal s.mem base B n) % m ∧
      Outside base O (8 * n) s.mem u.mem ∧ Kp asClob s u := by
  obtain ⟨hs, h4, h5, h6, hn0, hn4, o_le, a_le, b_le⟩ := hp
  simp only [add4, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_append (WP.mono (ldSteps_ok (sub := false) hs h5 h6 a_le b_le hn4 (k := n) (Nat.le_refl _))
    fun s₁ ⟨V₁, M₁, K₁⟩ => ?_)
  simp only [cOf_pos hn0, Bool.false_eq_true, ite_false, Nat.add_zero, Bool.toNat_false] at V₁
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_addze ?_
  refine wp_gen fun s₂ hs₂ => ?_
  simp only [write_gpr, ite_true, RegUpd.ca_write] at hs₂
  have hc1 := Bool.toNat_le s₁.ca
  generalize hc : s₁.ca.toNat = c at V₁ hs₂ hc1
  have h0₂ : (s₂.gpr .r0).toNat = c := by
    rw [hs₂, RegUpd.gpr_writeCarry_self, BitVec.toNat_ofNat]; simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_add]
    omega
  have K₁₂ : Kp [.r0] s₁ s₂ := by rw [hs₂]; exact (Kp.write _ _ (by simp)).trans (Kp.writeCarry _ _ (by simp))
  have hg₂ : gval s₂ vReg n = gval s₁ vReg n := gval_vregs_kp K₁₂ hn4 (by simp)
  have hm₂ : s₂.mem = s₁.mem := by rw [hs₂]; rfl
  refine WP.block_append (WP.mono (subMs_ok (s := s₂) (m := m) hn4 (k := n) (Nat.le_refl _)) fun s₃ ⟨V₃, M₃, K₃⟩ => ?_)
  rw [cOfT_pos hn0, mwords_eq, Nat.mod_eq_of_lt hm, hg₂] at V₃
  have h0₃ : s₃.gpr .r0 = s₂.gpr .r0 := K₃.gpr _ (by simp [not_vregs (r := .r0) (by decide) hn4])
  refine wp_step exec_addze ?_
  refine wp_step (exec_subi (by decide) (by decide)) ?_
  refine wp_gen fun s₄ hs₄ => ?_
  have hcb1 := Bool.toNat_le s₃.ca
  generalize hcb : s₃.ca.toNat = cb at V₃ hs₄ hcb1
  rw [h0₃, h0₂] at hs₄
  -- The arithmetic of the reduction.
  have hP := wordsVal_lt s.mem base A n
  obtain ⟨hct, hsel⟩ := csub_math hm (L := gval s₁ vReg n) (top := c)
    (by rw [V₁]; exact hab) (gval_lt' s₃ vReg n) (by omega) hcb1
  have hmk : s₄.gpr .r11 = (if cb + c = 0 then BitVec.allOnes 64 else 0) := by
    rw [hs₄]
    simp only [write_gpr, ite_true, RegUpd.gpr_writeCarry_self]
    rcases Nat.eq_zero_or_pos (cb + c) with h | h
    · simp only [h, ite_true, show c + cb = 0 by omega]; decide
    · have h' : ¬ (cb + c = 0) := by omega
      simp only [h', ite_false, show c + cb = 1 by omega]; decide
  have hmk' : s₄.gpr .r11 = 0 ∨ s₄.gpr .r11 = BitVec.allOnes 64 := by rw [hmk]; split <;> simp
  have K₃₄ : Kp [.r11] s₃ s₄ := by rw [hs₄]; exact (Kp.writeCarry _ _ (by simp)).trans (Kp.write _ _ (by simp))
  have hg₄ : gval s₄ vReg n = gval s₃ vReg n := gval_vregs_kp K₃₄ hn4 (by simp)
  have hm₄ : s₄.mem = s₃.mem := by rw [hs₄]; rfl
  have K₀₄ : Kp asClob s s₄ :=
    (((K₁.mono fun r hr => by
      rcases List.mem_cons.mp hr with h | h
      · rw [h]; decide
      rcases List.mem_cons.mp h with h | h
      · rw [h]; decide
      · exact vregs_asClob hn4 r h).trans (K₁₂.mono (by decide))).trans
      (K₃.mono fun r hr => by
        rcases List.mem_cons.mp hr with h | h
        · rw [h]; decide
        · exact vregs_asClob hn4 r h)).trans (K₃₄.mono (by decide))
  have h4₄ : At s₄ base .r4 O := K₀₄.at h4
  refine WP.mono (backs_ok (K₀₄.ws hs) (m := m) hn4 h4₄ o_le hmk' (k := n) (Nat.le_refl _)) fun u ⟨V₅, O₅, K₅⟩ => ?_
  rw [cOf_pos hn0, mwords_eq, Nat.mod_eq_of_lt hm, hg₄, hmk] at V₅
  refine ⟨?_, ?_, K₀₄.trans (K₅.mono fun r hr => by
      rcases List.mem_cons.mp hr with h | h
      · rw [h]; decide
      · exact vregs_asClob hn4 r h)⟩
  · rw [← V₁, ← hsel]
    have hu := wordsVal_lt u.mem base O n
    have hg1 := gval_lt' s₁ vReg n
    have hg3 := gval_lt' s₃ vReg n
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Bool.toNat_le u.ca) with hcu | hcu <;> rw [hcu] at V₅ <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcb1 with hb' | hb' <;> rw [hb'] at V₃ <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc1 with hc' | hc' <;> subst hb' hc' <;>
      simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add, ite_true, ite_false,
        (by decide : BitVec.allOnes 64 ≠ 0), Nat.reduceAdd,
        Nat.one_ne_zero] at V₅ hct ⊢ <;> omega
  · rw [show s.mem = s₄.mem by rw [hm₄, M₃, hm₂, M₁]]; exact O₅

/-- `[r4] = [r5] - [r6] mod m`, for `n ≤ 4` words. -/
theorem sub4_ok {s : State} {base : Addr} {size n m O A B : Nat} (hp : AsPre s base size n O A B)
    (hm : m < 2 ^ (64 * n)) (ha : wordsVal s.mem base A n < m) (hb : wordsVal s.mem base B n < m) :
    WP isa (.block (sub4 n m)) s fun u =>
      wordsVal u.mem base O n = (wordsVal s.mem base A n + m - wordsVal s.mem base B n) % m ∧
      Outside base O (8 * n) s.mem u.mem ∧ Kp asClob s u := by
  obtain ⟨hs, h4, h5, h6, hn0, hn4, o_le, a_le, b_le⟩ := hp
  simp only [sub4, List.append_assoc, List.cons_append, List.nil_append]
  refine WP.block_append (WP.mono (ldSteps_ok (sub := true) hs h5 h6 a_le b_le hn4 (k := n) (Nat.le_refl _))
    fun s₁ ⟨V₁, M₁, K₁⟩ => ?_)
  simp only [cOfT_pos hn0, ite_true, Bool.toNat_true] at V₁
  refine wp_step exec_sube ?_
  refine wp_gen fun s₂ hs₂ => ?_
  have hcb1 := Bool.toNat_le s₁.ca
  generalize hcb : s₁.ca.toNat = cb at V₁ hs₂ hcb1
  have hmk : s₂.gpr .r11 = (if cb = 0 then BitVec.allOnes 64 else 0) := by
    rw [hs₂, RegUpd.gpr_writeCarry_self]
    have hx := (s₁.gpr .r11).isLt
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcb1 with h | h <;> subst h <;> simp only [ite_true, Nat.one_ne_zero,
      ite_false]
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_allOnes, Nat.add_zero]
      omega
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      show _ = 0
      omega
  have hmk' : s₂.gpr .r11 = 0 ∨ s₂.gpr .r11 = BitVec.allOnes 64 := by rw [hmk]; split <;> simp
  have K₁₂ : Kp [.r11] s₁ s₂ := by rw [hs₂]; exact Kp.writeCarry _ _ (by simp)
  have hg₂ : gval s₂ vReg n = gval s₁ vReg n := gval_vregs_kp K₁₂ hn4 (by simp)
  have hm₂ : s₂.mem = s₁.mem := by rw [hs₂]; rfl
  have K₀₂ : Kp asClob s s₂ :=
    (K₁.mono fun r hr => by
      rcases List.mem_cons.mp hr with h | h
      · rw [h]; decide
      rcases List.mem_cons.mp h with h | h
      · rw [h]; decide
      · exact vregs_asClob hn4 r h).trans (K₁₂.mono (by decide))
  refine WP.mono (backs_ok (K₀₂.ws hs) (m := m) hn4 (K₀₂.at h4) o_le hmk' (k := n) (Nat.le_refl _)) fun u ⟨V₅, O₅, K₅⟩ => ?_
  rw [cOf_pos hn0, mwords_eq, Nat.mod_eq_of_lt hm, hg₂, hmk] at V₅
  refine ⟨?_, ?_, K₀₂.trans (K₅.mono fun r hr => by
      rcases List.mem_cons.mp hr with h | h
      · rw [h]; decide
      · exact vregs_asClob hn4 r h)⟩
  · have hu := wordsVal_lt u.mem base O n
    have hP1 : 1 ≤ 2 ^ (64 * n) := Nat.one_le_two_pow
    have hg1 := gval_lt' s₁ vReg n
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Bool.toNat_le u.ca) with hcu | hcu <;> rw [hcu] at V₅ <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcb1 with hb' | hb' <;> subst hb' <;>
      simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, ite_true, Nat.one_ne_zero, ite_false,
        (by decide : BitVec.allOnes 64 ≠ 0)] at V₅ V₁ ⊢
    · exfalso; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · exfalso; omega
  · rw [show s.mem = s₂.mem by rw [hm₂, M₁]]; exact O₅

end VG.Proof.Mont.PPC64LE
