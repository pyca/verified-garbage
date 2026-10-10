import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnX
import VerifiedGarbage.Proof.Mont.X86_64.SqrP

/-!
# P-521's product modulo `p` as a function, on x86-64

`mulFn` (`Impl/Weierstrass/X86_64/Mont.lean`) runs the columns of the
inline product `mulP` (or of the square `sqrP`, when `a = b`) with their
operands read through `rsi = ws + a` and `rbx = ws + b`: a term reads any
operands whose registers it does not change (`termR_ok`), so the columns'
arithmetic is `mulP`'s and `sqrP`'s (`pColSum`, `sColSum`). The result plus
one then goes into `xWin 9` (`plusOne_ok`) for `mulFnX`'s exit.
-/

namespace VG.Proof.Weierstrass.X86_64.Mont

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Impl.Weierstrass.X86_64.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono se0 add_carry adc_carry mulx_arith)

/-! ## Operands -/

/-- The registers an operand's value depends on. -/
def srcRegs : Src → List Reg
  | .reg r => [r]
  | .imm _ => []
  | .mem m => m.base :: m.index.toList

theorem readSrc_congr {s s' : State} {x : Src} (hg : ∀ r ∈ srcRegs x, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : readSrc s' x = readSrc s x := by
  cases x with
  | reg r => simp only [readSrc, hg r (by simp [srcRegs])]
  | imm v => rfl
  | mem m =>
    have he : s'.ea m = s.ea m := by
      unfold State.ea
      cases hi : m.index with
      | none => simp only [hg m.base (by simp [srcRegs])]
      | some i => simp only [hg m.base (by simp [srcRegs]), hg i (by simp [srcRegs, hi])]
    simp only [readSrc, State.load64, he, hm, hrd, hwr]

/-- The registers a term changes. -/
abbrev termRegs : List Reg := [.rax, .rcx, .rdx, .r9, .r10, .r11]

theorem pAccs_sub (c : Nat) : ∀ r ∈ pAccs c, r ∈ termRegs := by
  intro r hr
  have := (pAccs_ok c).2 r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
  rcases this with rfl | rfl | rfl <;> simp

/-! ## A term -/

/-- `rcx = y`. -/
theorem movRcxSrc_ok (s : State) {sy : Src} {wy : BitVec 64} (hy : readSrc s sy = some wy) :
    WP isa (.block [.mov .rcx sy]) s fun s' => s'.gpr .rcx = wy ∧ Keeps [.rcx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hy, Option.map_some,
    RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

/-- `rdx:rax = [mx] · rcx`, then `r0–r2 += rdx:rax` (`pMulAcc_ok` through
any operand). -/
theorem pMulAccR_ok {s : State} {r0 r1 r2 : Reg} (hd : [r0, r1, r2, .rax, .rcx, .rdx, .rdi].Nodup)
    {mx : MemOp} {wx : BitVec 64} (hx : readSrc s (.mem mx) = some wx)
    (hb : regsVal s [r0, r1, r2] + wx.toNat * (s.gpr .rcx).toNat < 2 ^ 192) :
    WP isa (.block [.mov .rax (.mem mx), .mul .rcx, .alu .add r0 (.reg .rax),
      .alu .adc r1 (.reg .rdx), .alu .adc r2 (.imm 0)]) s fun s' =>
      regsVal s' [r0, r1, r2] = regsVal s [r0, r1, r2] + wx.toNat * (s.gpr .rcx).toNat ∧
      Keeps [.rax, .rdx, r0, r1, r2] s s' ∧
      (s'.gpr .rax).toNat + 2 ^ 64 * (s'.gpr .rdx).toNat = wx.toNat * (s.gpr .rcx).toNat := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h0a, h0c, h0d, h0i⟩, ⟨h12, h1a, h1c, h1d, h1i⟩, ⟨h2a, h2c, h2d, h2i⟩, -⟩ := hd
  have hx' : s.load64 (s.ea mx) = some wx := hx
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hx', readSrc, execMul,
    execAlu, Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ite_false,
    reduceCtorEq, Ne.symm h01, Ne.symm h02, Ne.symm h12, h0a, h1a, h2a, h0d, h1d, h2d,
    Ne.symm h0d, Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, ?_⟩
  · simp only [regsVal, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, ite_true, ite_false,
      h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12, Nat.mul_zero, Nat.add_zero]
    have em := mulx_arith wx (s.gpr .rcx)
    generalize BitVec.ofNat 64 (wx.toNat * (s.gpr .rcx).toNat) = lo at em ⊢
    generalize BitVec.ofNat 64 (wx.toNat * (s.gpr .rcx).toNat / 2 ^ 64) = hi at em ⊢
    have e0 := add_carry (s.gpr r0) lo
    generalize decide (2 ^ 64 ≤ (s.gpr r0).toNat + lo.toNat) = c0 at e0 ⊢
    have e1 := adc_carry (s.gpr r1) hi c0
    generalize decide (2 ^ 64 ≤ (s.gpr r1).toNat + hi.toNat + c0.toNat) = c1 at e1 ⊢
    have e2 := adc_carry (s.gpr r2) 0 c1
    generalize decide (2 ^ 64 ≤ (s.gpr r2).toNat + (0 : BitVec 64).toNat + c1.toNat) = c2 at e2
    simp only [regsVal, Nat.mul_zero, Nat.add_zero] at hb
    have z : (0 : BitVec 64).toNat = 0 := rfl
    have := Bool.toNat_le c2
    have := (s.gpr r0 + lo).isLt; have := (s.gpr r1 + hi + (BitVec.ofBool c0).setWidth 64).isLt
    have := (s.gpr r2 + 0 + (BitVec.ofBool c1).setWidth 64).isLt
    rw [z] at e2
    rcases Nat.lt_or_ge c2.toNat 1 with h | h <;> omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2, ite_false]
  · simp only [Ne.symm h0a, Ne.symm h1a, Ne.symm h2a, Ne.symm h1d, Ne.symm h2d, ite_false]
    exact mulx_arith wx (s.gpr .rcx)

/-- A term: `acc += x · y`, twice if `two`, for operands whose registers it
does not change. -/
theorem termR_ok (s : State) (c : Nat) {mx : MemOp} {sy : Src} {wx wy : BitVec 64} (two : Bool)
    (hx : readSrc s (.mem mx) = some wx) (hy : readSrc s sy = some wy)
    (hreg : ∀ r ∈ srcRegs (.mem mx), r ∉ termRegs)
    (hb : regsVal s (pAccs c) + mult two * (wx.toNat * wy.toNat) < 2 ^ 192) :
    WP isa (.block (termR2 c mx sy two)) s fun s' =>
      regsVal s' (pAccs c) = regsVal s (pAccs c) + mult two * (wx.toNat * wy.toNat) ∧
      Keeps (.rax :: .rcx :: .rdx :: pAccs c) s s' := by
  have hok := pAccs_ok c
  rw [termR2, termR, show ([.mov .rcx sy, .mov .rax (.mem mx), .mul .rcx, .alu .add (pAcc c 0) (.reg .rax),
      .alu .adc (pAcc c 1) (.reg .rdx), .alu .adc (pAcc c 2) (.imm 0)] : List Instr) =
      [.mov .rcx sy] ++ [.mov .rax (.mem mx), .mul .rcx, .alu .add (pAcc c 0) (.reg .rax),
      .alu .adc (pAcc c 1) (.reg .rdx), .alu .adc (pAcc c 2) (.imm 0)] from rfl, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (movRcxSrc_ok s hy) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hx₁ : readSrc s₁ (.mem mx) = some wx := by
    rw [readSrc_congr (fun r hr => k₁.1 r (by
      simp only [List.mem_singleton]; intro h; exact hreg r hr (by simp [h]))) k₁.2.1 k₁.2.2.1 k₁.2.2.2, hx]
  have hacc : regsVal s₁ (pAccs c) = regsVal s (pAccs c) := regsVal_congr fun r hr => k₁.1 r (by
    have := hok.2 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    rcases this with rfl | rfl | rfl <;> decide)
  rw [WP.block_append_iff]
  refine WP.mono (pMulAccR_ok hok.1 hx₁ (by
    rw [show [pAcc c 0, pAcc c 1, pAcc c 2] = pAccs c from rfl, hacc, e₁]
    cases two <;> simp only [mult, Bool.false_eq_true, ↓reduceIte] at hb <;> omega_arith))
    fun s₂ ⟨e₂, k₂, x₂⟩ => ?_
  rw [show [pAcc c 0, pAcc c 1, pAcc c 2] = pAccs c from rfl, hacc, e₁] at e₂
  rw [e₁] at x₂
  have k₁₂ : Keeps (.rax :: .rcx :: .rdx :: pAccs c) s s₂ :=
    (k₁.mono (by simp)).trans (k₂.mono (by simp [pAccs]))
  cases two with
  | false => exact WP.block_nil ⟨by rw [e₂]; simp [mult], k₁₂⟩
  | true =>
    simp only [ite_true]
    refine WP.mono (sAdd_ok s₂ hok.1 (by
      rw [show [pAcc c 0, pAcc c 1, pAcc c 2] = pAccs c from rfl, e₂, x₂]
      simp only [mult, ↓reduceIte] at hb; omega_arith)) fun s₃ ⟨e₃, k₃⟩ =>
        ⟨?_, k₁₂.trans (k₃.mono (by simp [pAccs]))⟩
    rw [show [pAcc c 0, pAcc c 1, pAcc c 2] = pAccs c from rfl, e₂, x₂] at e₃
    rw [e₃]; simp only [mult, ↓reduceIte]; omega_arith

/-! ## A column -/

/-- An operand's value, as a number. -/
abbrev val (s : State) (x : Src) : Nat := ((readSrc s x).getD 0).toNat

/-- The sum of a column's terms, with their multiplicities. -/
def tSum (s : State) (ts : List (MemOp × Src × Bool)) : Nat :=
  (ts.map fun t => mult t.2.2 * (val s (.mem t.1) * val s t.2.1)).sum

/-- The terms read operands, through registers they do not change. -/
def TermsOk (s : State) (ts : List (MemOp × Src × Bool)) : Prop :=
  ∀ t ∈ ts, (readSrc s (.mem t.1)).isSome ∧ (readSrc s t.2.1).isSome ∧
    (∀ r ∈ srcRegs (.mem t.1), r ∉ termRegs) ∧ (∀ r ∈ srcRegs t.2.1, r ∉ termRegs)

theorem readSrc_keep {s s' : State} {rs : List Reg} (k : Keeps rs s s') (hsub : ∀ r ∈ rs, r ∈ termRegs)
    {x : Src} (hx : ∀ r ∈ srcRegs x, r ∉ termRegs) : readSrc s' x = readSrc s x :=
  readSrc_congr (fun r hr => k.1 r (fun h => hx r hr (hsub r h))) k.2.1 k.2.2.1 k.2.2.2

theorem term_sub (c : Nat) : ∀ r ∈ Reg.rax :: Reg.rcx :: Reg.rdx :: pAccs c, r ∈ termRegs := by
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | rfl | hr
  · simp
  · simp
  · simp
  · exact pAccs_sub c r hr

/-- A column's terms, by induction on them. -/
theorem termsR_ok (c : Nat) : ∀ (ts : List (MemOp × Src × Bool)) {s : State},
    TermsOk s ts → regsVal s (pAccs c) + tSum s ts < 2 ^ 192 →
    WP isa (.block (ts.flatMap fun t => termR2 c t.1 t.2.1 t.2.2)) s fun s' =>
      regsVal s' (pAccs c) = regsVal s (pAccs c) + tSum s ts ∧
      Keeps (.rax :: .rcx :: .rdx :: pAccs c) s s'
  | [], s, _, _ => WP.block_nil ⟨by simp [tSum], fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, hok, hb => by
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ⟨hx, hy, hrx, hry⟩ := hok t List.mem_cons_self
    obtain ⟨wx, ewx⟩ := Option.isSome_iff_exists.mp hx
    obtain ⟨wy, ewy⟩ := Option.isSome_iff_exists.mp hy
    have hv : mult t.2.2 * (val s (.mem t.1) * val s t.2.1) = mult t.2.2 * (wx.toNat * wy.toNat) := by
      simp only [val, ewx, ewy, Option.getD_some]
    simp only [tSum, List.map_cons, List.sum_cons] at hb
    refine WP.mono (termR_ok s c t.2.2 ewx ewy hrx (by omega_arith)) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hok₁ : TermsOk s₁ ts := fun t' ht' => by
      obtain ⟨a1, a2, a3, a4⟩ := hok t' (List.mem_cons_of_mem _ ht')
      rw [readSrc_keep k₁ (term_sub c) a3, readSrc_keep k₁ (term_sub c) a4]
      exact ⟨a1, a2, a3, a4⟩
    have hsum : tSum s₁ ts = tSum s ts := by
      simp only [tSum]
      congr 1
      apply List.map_congr_left
      intro t' ht'
      obtain ⟨-, -, a3, a4⟩ := hok t' (List.mem_cons_of_mem _ ht')
      simp only [val, readSrc_keep k₁ (term_sub c) a3, readSrc_keep k₁ (term_sub c) a4]
    refine WP.mono (termsR_ok c ts hok₁ (by rw [e₁, hsum]; simp only [tSum] at hb ⊢; omega_arith))
      fun s₂ ⟨e₂, k₂⟩ => ⟨?_, k₁.trans k₂⟩
    rw [e₂, e₁, hsum]
    simp only [tSum, List.map_cons, List.sum_cons]
    omega_arith

/-- Column `c`: its terms, and its low word stored at `[fnTmp + 8 (c mod 9)]`;
the rest of the accumulator is the next column's. -/
theorem colR_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {ts : Nat → List (MemOp × Src × Bool)} {c : Nat} (htmp : fnTmp + 72 ≤ size) (hok : TermsOk s (ts c))
    (hb : regsVal s (pAccs c) + tSum s (ts c) < 2 ^ 192) :
    WP isa (.block (colR ts c)) s fun s' =>
      (word s'.mem base (fnTmp + 8 * (c % 9))).toNat + 2 ^ 64 * regsVal s' (pAccs (c + 1)) =
        regsVal s (pAccs c) + tSum s (ts c) ∧
      KeepRegs [.rax, .rcx, .rdx, .r9, .r10, .r11] s s' ∧
      Outside base (fnTmp + 8 * (c % 9)) 8 s.mem s'.mem := by
  have hnw := hs.nowrap
  have hc9 := Nat.mod_lt c (show 0 < 9 by decide)
  rw [colR, WP.block_append_iff]
  refine WP.mono (termsR_ok c _ hok hb) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (fun h => absurd (term_sub c _ h) (by decide))
  refine WP.mono (pEnd_ok hs₁ c (t := fnTmp + 8 * (c % 9)) (by omega_arith)) fun s₂ ⟨m₂, e₂, k₂⟩ => ?_
  refine ⟨?_, ⟨fun r hr => ?_, k₂.rd.trans k₁.2.2.1, k₂.wr.trans k₁.2.2.2⟩, ?_⟩
  · rw [m₂, word_writeW_self, ← e₂, e₁]
  · rw [k₂.gpr r (fun h => hr (by
        simp only [List.mem_singleton] at h; exact h ▸ pAccs_sub c _ (by simp [pAccs]))),
      k₁.1 r (fun h => hr (term_sub c r h))]
  · rw [m₂, k₁.2.1]; exact writeW_outside _ _ _ (by omega_arith)

/-! ## The columns -/

/-- The pointers to the operands. -/
def Ptrs (base : Addr) (a b : Nat) (s : State) : Prop := s.gpr .rbx = off base a ∧ s.gpr .rbp = off base b

theorem ptrs_keep {base : Addr} {a b : Nat} {s s' : State} (h : Ptrs base a b s)
    (k : KeepRegs [.rax, .rcx, .rdx, .r9, .r10, .r11] s s') : Ptrs base a b s' :=
  ⟨(k.gpr _ (by decide)).trans h.1, (k.gpr _ (by decide)).trans h.2⟩

theorem readSrc_opA {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) {a : Nat} (hsi : s.gpr .rbx = off base a)
    (ha : a + 72 ≤ Z) {i : Nat} (hi : i < 9) :
    readSrc s (.mem (opA i)) = some (Mont.word s.mem base (a + 8 * i)) :=
  readSrc_ptr hs hsi (by omega_arith)

theorem readSrc_opB {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) {b : Nat} (hbx : s.gpr .rbp = off base b)
    (hb : b + 72 ≤ Z) {j : Nat} (hj : j < 9) :
    readSrc s (.mem (opB j)) = some (Mont.word s.mem base (b + 8 * j)) :=
  readSrc_ptr hs hbx (by omega_arith)

theorem val_512 (s : State) : val s (.imm 512) = 512 := by
  show ((512 : BitVec 32).signExtend 64).toNat = 512
  decide

theorem fnTmp_eq : fnTmp = 4024 := rfl

/-- The reduction's term of column `c`. -/
theorem redTerms_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z) {c : Nat} {l : Nat → Nat}
    (hL : 8 ≤ c → c ≤ 16 → (Mont.word s.mem base (fnTmp + 8 * (c - 8))).toNat = l (c - 8)) :
    TermsOk s (redTerms c) ∧ tSum s (redTerms c) = if 8 ≤ c ∧ c ≤ 16 then l (c - 8) * 512 else 0 := by
  unfold redTerms
  split
  · rename_i h
    have hr := readSrc_sc hs (d := fnTmp + 8 * (c - 8)) (by rw [fnTmp_eq]; omega_arith)
    refine ⟨fun t ht => ?_, ?_⟩
    · simp only [List.mem_singleton] at ht
      subst ht
      exact ⟨by rw [hr]; rfl, rfl, by simp [srcRegs, sc], by simp [srcRegs]⟩
    · simp only [tSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, mult,
        Bool.false_eq_true, ↓reduceIte, Nat.one_mul, val_512, val, hr, Option.getD_some, hL h.1 h.2]
  · exact ⟨fun t ht => by simp at ht, rfl⟩

/-- The product's columns. -/
theorem mulCols_ok {base : Addr} {Z : Nat} (hZ : 4096 ≤ Z) {m₀ : Mem} {a b : Nat} (ha : a + 72 ≤ 3520) (hb : b + 72 ≤ 3520) :
    ColOk (fnMod true) base Z m₀ (colR mulTerms)
      (pColSum (fun i => (Mont.word m₀ base (a + 8 * i)).toNat) (fun j => (Mont.word m₀ base (b + 8 * j)).toNat))
      (Ptrs base a b) :=
  fun c hc s l hs hP O hacc hL => by
    have hnw := hs.nowrap
    have hA : ∀ i < 9, Mont.word s.mem base (a + 8 * i) = Mont.word m₀ base (a + 8 * i) :=
      fun i hi => O.word (by rw [fnTmp_val]; omega_arith) (by omega_arith)
    have hB : ∀ j < 9, Mont.word s.mem base (b + 8 * j) = Mont.word m₀ base (b + 8 * j) :=
      fun j hj => O.word (by rw [fnTmp_val]; omega_arith) (by omega_arith)
    obtain ⟨rok, rsum⟩ := redTerms_ok hs hZ (c := c) hL
    have hok : TermsOk s (mulTerms c) := by
      intro t ht
      simp only [mulTerms, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
        decide_eq_true_eq] at ht
      rcases ht with ⟨i, ⟨hi, -, hj⟩, rfl⟩ | ht
      · exact ⟨by rw [readSrc_opA hs hP.1 (by omega_arith) hi]; rfl, by rw [readSrc_opB hs hP.2 (by omega_arith) hj]; rfl,
          by simp [srcRegs, opA, rcR], by simp [srcRegs, opB, rcR]⟩
      · exact rok t ht
    have hsum : tSum s (mulTerms c) = pColSum (fun i => (Mont.word m₀ base (a + 8 * i)).toNat)
        (fun j => (Mont.word m₀ base (b + 8 * j)).toNat) l c := by
      rw [mulTerms, pColSum, ← rsum]
      simp only [tSum, List.map_append, List.sum_append, List.map_map]
      congr 1
      refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
      simp only [Function.comp, mult, Bool.false_eq_true, ↓reduceIte, Nat.one_mul, val,
        readSrc_opA hs hP.1 (by omega_arith) hi.1, readSrc_opB hs hP.2 (by omega_arith) hi.2.2, Option.getD_some,
        hA i hi.1, hB (c - i) hi.2.2]
    have hcol := pColSum_lt (A := fun i => (Mont.word m₀ base (a + 8 * i)).toNat)
      (B := fun j => (Mont.word m₀ base (b + 8 * j)).toNat) (l := l) c (fun i => (Mont.word _ _ _).isLt)
      (fun j => (Mont.word _ _ _).isLt) (fun h1 h2 => by rw [← hL h1 h2]; exact (Mont.word _ _ _).isLt)
    refine WP.mono (colR_ok hs (ts := mulTerms) (c := c) (by rw [fnTmp_eq]; omega_arith) hok (by rw [hsum]; omega_arith))
      fun s' ⟨e', k', O'⟩ => ⟨by rw [hsum] at e'; exact e', k', O'⟩

/-- The square's columns. -/
theorem sqrCols_ok {base : Addr} {Z : Nat} (hZ : 4096 ≤ Z) {m₀ : Mem} {a : Nat} (ha : a + 72 ≤ 3520) :
    ColOk (fnMod true) base Z m₀ (colR sqrTerms)
      (sColSum fun i => (Mont.word m₀ base (a + 8 * i)).toNat) (Ptrs base a a) :=
  fun c hc s l hs hP O hacc hL => by
    have hnw := hs.nowrap
    have hA : ∀ i < 9, Mont.word s.mem base (a + 8 * i) = Mont.word m₀ base (a + 8 * i) :=
      fun i hi => O.word (by rw [fnTmp_val]; omega_arith) (by omega_arith)
    obtain ⟨rok, rsum⟩ := redTerms_ok hs hZ (c := c) hL
    have hok : TermsOk s (sqrTerms c) := by
      intro t ht
      simp only [sqrTerms, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
        decide_eq_true_eq] at ht
      rcases ht with (⟨i, ⟨hi, -, hj⟩, rfl⟩ | ht) | ht
      · exact ⟨by rw [readSrc_opA hs hP.1 (by omega_arith) hi]; rfl, by rw [readSrc_opA hs hP.1 (by omega_arith) hj]; rfl,
          by simp [srcRegs, opA, rcR], by simp [srcRegs, opA, rcR]⟩
      · split at ht
        · rename_i h
          simp only [List.mem_singleton] at ht
          subst ht
          exact ⟨by rw [readSrc_opA hs hP.1 (by omega_arith) h.2]; rfl, by rw [readSrc_opA hs hP.1 (by omega_arith) h.2]; rfl,
            by simp [srcRegs, opA, rcR], by simp [srcRegs, opA, rcR]⟩
        · simp at ht
      · exact rok t ht
    have hsum : tSum s (sqrTerms c) = sColSum (fun i => (Mont.word m₀ base (a + 8 * i)).toNat) l c := by
      rw [sqrTerms, sColSum, ← rsum]
      simp only [tSum, List.map_append, List.sum_append, List.map_map]
      rw [Nat.add_assoc]
      refine congrArg₂ (· + ·) ?_ (congrArg (· + _) ?_)
      · refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
        simp only [Function.comp, mult, ↓reduceIte, val, readSrc_opA hs hP.1 (by omega_arith) hi.1,
          readSrc_opA hs hP.1 (by omega_arith) hi.2.2, Option.getD_some, hA i hi.1, hA (c - i) hi.2.2]
      · split
        · rename_i h
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, mult,
            Bool.false_eq_true, ↓reduceIte, Nat.one_mul, val, readSrc_opA hs hP.1 (by omega_arith) h.2,
            Option.getD_some, hA _ h.2]
        · simp
    have hcol := (colSum_s (fun i => (Mont.word m₀ base (a + 8 * i)).toNat) (fun _ => (Mont.word _ _ _).isLt)).lt l c
      fun h1 h2 => by rw [← hL h1 h2]; exact (Mont.word _ _ _).isLt
    refine WP.mono (colR_ok hs (ts := sqrTerms) (c := c) (by rw [fnTmp_eq]; omega_arith) hok (by rw [hsum]; omega_arith))
      fun s' ⟨e', k', O'⟩ => ⟨by rw [hsum] at e'; exact e', k', O'⟩

/-! ## The result plus one -/

/-- `add t, 1`. -/
theorem addOne_ok (s : State) (t : Reg) :
    WP isa (.block [.alu .add t (.imm 1)]) s fun s' =>
      ∃ c', s'.cf = some c' ∧ (s'.gpr t).toNat + 2 ^ 64 * c'.toNat = (s.gpr t).toNat + 1 ∧
        Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg_self, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have h1 : ((1 : BitVec 32).signExtend 64).toNat = 1 := by decide
    have := add_carry (s.gpr t) ((1 : BitVec 32).signExtend 64)
    rw [h1] at this
    simpa [h1] using this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- A carry `c` added up the words `ts`. -/
theorem adcZs_ok : ∀ (ts : List Reg) {s : State} {c : Bool}, ts.Nodup → s.cf = some c →
    WP isa (.block (ts.map fun t => .alu .adc t (.imm 0))) s fun s' =>
      ∃ c', s'.cf = some c' ∧ regsVal s' ts + 2 ^ (64 * ts.length) * c'.toNat = regsVal s ts + c.toNat ∧
        Keeps ts s s'
  | [], s, c, _, hc => WP.block_nil ⟨c, hc, by simp [regsVal], fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, c, hn, hc => by
    rw [List.map_cons, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (adcZ_ok s t hc) fun s₁ ⟨c₁, cf₁, e₁, k₁⟩ => ?_
    have htn := (List.nodup_cons.mp hn).1
    refine WP.mono (adcZs_ok ts (List.nodup_cons.mp hn).2 cf₁) fun s₂ ⟨c₂, cf₂, e₂, k₂⟩ =>
      ⟨c₂, cf₂, ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => htn (h ▸ hq))
    have ht₂ : s₂.gpr t = s₁.gpr t := k₂.1 t htn
    simp only [regsVal, List.length_cons, ht₂]
    rw [hR] at e₂
    rw [show 64 * (ts.length + 1) = 64 + 64 * ts.length by omega_arith, Nat.pow_add, Nat.mul_assoc]
    generalize 2 ^ (64 * ts.length) * c₂.toNat = X at *
    omega_arith

theorem xWin9_get (j : Nat) (h : j < (xWin 9).length) : (xWin 9)[j] = xAcc (9 + j) := by
  simp [xWin]

/-- The number in the temporary area plus one, into `xWin 9`. -/
theorem plusOne_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z)
    (hW : wordsVal s.mem base fnTmp 9 + 1 < (2 ^ 64) ^ 9) :
    WP isa (.block plusOne) s fun s' =>
      hval (xg s') 9 9 = wordsVal s.mem base fnTmp 9 + 1 ∧
      KeepRegs (.rax :: .rcx :: .rdx :: xRegs) s s' ∧ s'.mem = s.mem := by
  rw [plusOne, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_words (xWin 9) hs (a := fnTmp) (by rw [fnTmp_eq]; simp only [xWin, List.length_map, List.length_range]; omega_arith) (xWin_fresh 9).1
    (by decide)) fun s₁ ⟨v₁, k₁⟩ => ?_
  have e₁ : hval (xg s₁) 9 9 = wordsVal s.mem base fnTmp 9 := by
    rw [show fnTmp = fnTmp + 8 * 0 from rfl, wordsVal_hval, hval_shift (xg s₁) 9 0 9]
    refine hval_congr fun j _ hj => ?_
    have := v₁ j (by simp [xWin]; omega_arith)
    rw [xWin9_get j (by simp [xWin]; omega_arith)] at this
    simp only [xg, Nat.add_comm j 9, this, Nat.mul_comm]
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addOne_ok s₁ (xAcc 9)) fun s₂ ⟨c₂, cf₂, e₂, k₂⟩ => ?_
  have hnd : ((List.range 8).map fun k => xAcc (10 + k)).Nodup := by decide
  rw [show ((List.range 8).map fun k => (.alu .adc (xAcc (10 + k)) (.imm 0) : Instr)) =
    ((List.range 8).map fun k => xAcc (10 + k)).map fun t => .alu .adc t (.imm 0) by simp]
  refine WP.mono (adcZs_ok _ hnd cf₂) fun s₃ ⟨c₃, _, e₃, k₃⟩ => ?_
  have hsplit : ∀ s : State, hval (xg s) 9 9 = xg s 9 + 2 ^ 64 * regsVal s ((List.range 8).map fun k => xAcc (10 + k)) := by
    intro s
    rw [regsVal_xAccs s 8 10]; rfl
  have hr₂ : regsVal s₂ ((List.range 8).map fun k => xAcc (10 + k)) =
      regsVal s₁ ((List.range 8).map fun k => xAcc (10 + k)) := regsVal_congr fun q hq => k₂.1 q (by
    simp only [List.mem_singleton]; intro h; subst h; revert hq; decide)
  have hx₃ : xg s₃ 9 = xg s₂ 9 := by
    simp only [xg]; rw [k₃.1 _ (by decide)]
  have hlen : ((List.range 8).map fun k => xAcc (10 + k)).length = 8 := by simp
  rw [hlen] at e₃
  have hl := regsVal_lt s₃ ((List.range 8).map fun k => xAcc (10 + k))
  rw [hlen] at hl
  have hx := (s₃.gpr (xAcc 9)).isLt
  have e : hval (xg s₃) 9 9 + (2 ^ 64) ^ 9 * c₃.toNat = wordsVal s.mem base fnTmp 9 + 1 := by
    rw [hsplit, hx₃, ← e₁, hsplit s₁, ← hr₂]
    simp only [xg] at e₂ ⊢
    rw [Nat.pow_mul 2 64 8] at e₃
    rw [show (2 ^ 64) ^ 9 = 2 ^ 64 * (2 ^ 64) ^ 8 from (Nat.pow_succ' (m := 2 ^ 64) (n := 8)), Nat.mul_assoc]
    generalize (2 ^ 64) ^ 8 * c₃.toNat = Zc at *
    generalize regsVal s₃ ((List.range 8).map fun k => xAcc (10 + k)) = R₃ at *
    generalize regsVal s₂ ((List.range 8).map fun k => xAcc (10 + k)) = R₂ at *
    omega_arith
  refine ⟨?_, ⟨fun r hr => ?_, by rw [k₃.2.2.1, k₂.2.2.1, k₁.2.2.1], by rw [k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]⟩,
    by rw [k₃.2.1, k₂.2.1, k₁.2.1]⟩
  · rcases Nat.eq_zero_or_pos c₃.toNat with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero] at e; exact e
    · have : (2 ^ 64) ^ 9 * 1 ≤ (2 ^ 64) ^ 9 * c₃.toNat := Nat.mul_le_mul_left _ h
      omega_arith
  · have hx : ∀ q ∈ xWin 9, q ∈ Reg.rax :: Reg.rcx :: Reg.rdx :: xRegs := fun q hq =>
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (xWin_sub 9 q hq)))
    have h8 : ∀ q ∈ (List.range 8).map (fun k => xAcc (10 + k)), q ∈ Reg.rax :: Reg.rcx :: Reg.rdx :: xRegs := by
      decide
    rw [k₃.1 r (fun h => hr (h8 r h)), k₂.1 r (fun h => hr (by
      simp only [List.mem_singleton] at h; subst h; decide)), k₁.1 r (fun h => hr (hx r h))]

/-! ## The branches -/

/-- What a branch leaves: only the registers of the columns and the
temporary area changed, and there the result `W < 2m`, with
`2⁵⁷⁶ W = A B + U p`. -/
def BMid (m : Nat) (base : Addr) (A B : Nat) (s s' : State) : Prop :=
  KeepRegs termRegs s s' ∧ Outside base fnTmp 72 s.mem s'.mem ∧
    wordsVal s'.mem base fnTmp 9 < 2 * m ∧ ∃ U, (2 ^ 64) ^ 9 * wordsVal s'.mem base fnTmp 9 = A * B + U * m

/-- The columns, from any column sums that add up to `A B` and the
reduction's `2⁵²¹ U`. -/
theorem colsR_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z) {ts : Nat → List (MemOp × Src × Bool)}
    {S : (Nat → Nat) → Nat → Nat} {P : State → Prop} (hS : ColSum S)
    (hcol : ColOk (fnMod true) base Z s.mem (colR ts) S P) (hP₀ : P s)
    (hP : ∀ s s', P s → KeepRegs [.rax, .rcx, .rdx, .r9, .r10, .r11] s s' → P s') {A B m : Nat}
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hA : A < (2 ^ 64) ^ 9) (hB : B < m)
    (htot : ∀ l, hval (S l) 0 18 = A * B + 512 * (2 ^ 64) ^ 8 * hval l 0 9) :
    WP isa (.block (colsR ts)) s (BMid m base A B s) := by
  have hnw := hs.nowrap
  rw [colsR, WP.block_append_iff,
    show ([.mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0), .mov32 .r11 (.imm 0)] : List Instr) =
      zeros [.r9, .r10, .r11] from rfl]
  refine WP.mono (zeros_ok s [.r9, .r10, .r11]) fun s₁ ⟨z₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have h0 : regsVal s₁ (pAccs 0) = 0 := by
    simp only [show pAccs 0 = [.r9, .r10, .r11] from rfl, regsVal, z₁ .r9 (by simp),
      z₁ .r10 (by simp), z₁ .r11 (by simp)]
    rfl
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have hP₁ : P s₁ := hP _ _ hP₀ ⟨(k₁.mono (by decide)).1, k₁.2.2.1, k₁.2.2.2⟩
  refine WP.mono (cols_ok hs₁ (M := fnMod true) (by rw [fnTmp_val]; omega_arith) hS (by rw [hm₁]; exact hcol) hP₁ hP
    h0 18 (Nat.le_refl _)) fun s₂ ⟨k₂, O₂, _, l, hl64, hlm, e₂⟩ => ?_
  rw [htot, hval_add l 0 9 9, Nat.zero_add,
    show (2 ^ 64) ^ 18 = (2 ^ 64) ^ 9 * (2 ^ 64) ^ 9 by rw [← Nat.pow_add]] at e₂
  have hW : wordsVal s₂.mem base fnTmp 9 = hval l 9 9 := by
    rw [show fnTmp = fnTmp + 8 * 0 from rfl, wordsVal_hval s₂.mem base fnTmp 0 9,
      show (9 : Nat) = 0 + 9 from rfl, hval_shift l 9 0 9]
    exact hval_congr fun c _ hc => by
      have := hlm (c + 9) (by omega_arith) (by omega_arith)
      rwa [show (c + 9) % 9 = c by omega_arith] at this
  have hU : hval l 0 9 < (2 ^ 64) ^ 9 := hval_lt fun c _ hc => hl64 c (by omega_arith)
  rw [← hW, show pAccs 18 = [.r9, .r10, .r11] from rfl] at e₂
  obtain ⟨-, hT2, eT⟩ := mulP_arith (by decide) hm hA hB hU e₂
  refine ⟨⟨fun r hr => ?_, by rw [k₂.rd, k₁.2.2.1], by rw [k₂.wr, k₁.2.2.2]⟩,
    by rw [← hm₁]; exact O₂, hT2, _, eT⟩
  rw [k₂.gpr r (by simpa [termRegs] using hr), k₁.1 r (fun h => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl <;> simp))]

/-- `colsR`, from `rbx = ws + a` and `rcx = ws + b`, moved into `rbp`. -/
theorem colsO_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z) {ts : Nat → List (MemOp × Src × Bool)}
    {S : (Nat → Nat) → Nat → Nat} {a b : Nat} (hS : ColSum S)
    (hcol : ColOk (fnMod true) base Z s.mem (colR ts) S (Ptrs base a b)) (hbx : s.gpr .rbx = off base a)
    (hcx : s.gpr .rcx = off base b) {A B m : Nat}
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hA : A < (2 ^ 64) ^ 9) (hB : B < m)
    (htot : ∀ l, hval (S l) 0 18 = A * B + 512 * (2 ^ 64) ^ 8 * hval l 0 9) :
    WP isa (.block (colsO ts)) s fun s' =>
      KeepRegs (.rbp :: termRegs) s s' ∧ Outside base fnTmp 72 s.mem s'.mem ∧
      wordsVal s'.mem base fnTmp 9 < 2 * m ∧ (∃ U, (2 ^ 64) ^ 9 * wordsVal s'.mem base fnTmp 9 = A * B + U * m) := by
  rw [colsO, WP.block_append_iff]
  refine WP.mono (movReg_ok s .rbp .rcx) fun s₁ ⟨v₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  refine WP.mono (colsR_ok hs₁ hZ hS (by rw [hm₁]; exact hcol)
    ⟨(k₁.1 _ (by decide)).trans hbx, v₁.trans hcx⟩ (fun _ _ h k => ptrs_keep h k) hm hA hB htot)
    fun s₂ ⟨k₂, O₂, hW, U, eW⟩ => ?_
  rw [hm₁] at O₂
  refine ⟨⟨fun r hr => ?_, by rw [k₂.rd, k₁.2.2.1], by rw [k₂.wr, k₁.2.2.2]⟩, O₂, hW, ⟨U, eW⟩⟩
  have ht : r ∉ termRegs := fun h => hr (List.mem_cons_of_mem _ h)
  rw [k₂.gpr r ht, k₁.1 r (fun h => hr (by simp only [List.mem_singleton] at h; subst h; simp))]

/-! ## The function -/

theorem hval_words (m : Mem) (base : Addr) (a : Nat) :
    wordsVal m base a 9 = hval (fun i => (Mont.word m base (a + 8 * i)).toNat) 0 9 := by
  rw [← wordsVal_hval m base a 0 9, Nat.mul_zero, Nat.add_zero]

/-- The middle of `mulFn`: the product or the square, by columns, then plus one. -/
theorem midB_ok {m : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8) :
    MidOk (.seq (.ite .e (.block (colsO sqrTerms)) (.block (colsO mulTerms))) (.block plusOne)) m := by
  intro Z hZ s base a b hs bx cx zf ha hb hB
  have hX : ∀ x, wordsVal s.mem base x 9 < (2 ^ 64) ^ 9 := fun x => by
    rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ 9
  refine WP.seq (WP.mono (Q := fun (s' : State) => KeepRegs (.rbp :: termRegs) s s' ∧ Outside base fnTmp 72 s.mem s'.mem ∧
      wordsVal s'.mem base fnTmp 9 < 2 * m ∧
      (∃ U, (2 ^ 64) ^ 9 * wordsVal s'.mem base fnTmp 9 = wordsVal s.mem base a 9 * wordsVal s.mem base b 9 + U * m))
    (WP.ite (decide (a = b)) zf (fun h => ?_) (fun _ => ?_)) fun s₂ ⟨k₂, O₂, hW, ⟨U, eW⟩⟩ => ?_)
  · have hab : a = b := of_decide_eq_true h
    subst hab
    rw [hval_words s.mem base a]
    exact colsO_ok hs hZ (colSum_s _ fun _ => (Mont.word _ _ _).isLt) (sqrCols_ok hZ ha) bx cx
      hm (by rw [← hval_words]; exact hX a) (by rw [← hval_words]; exact hB) fun l => sColSum_total _ l
  · rw [hval_words s.mem base a, hval_words s.mem base b]
    exact colsO_ok hs hZ (colSum_p _ _ (fun _ => (Mont.word _ _ _).isLt) (fun _ => (Mont.word _ _ _).isLt))
      (mulCols_ok hZ ha hb) bx cx hm (by rw [← hval_words]; exact hX a)
      (by rw [← hval_words]; exact hB) fun l => pColSum_total _ _ l
  have hs₂ : Scr s₂ base Z := ⟨(k₂.gpr _ (by decide)).trans hs.rdi, k₂.wr ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (plusOne_ok hs₂ hZ (by omega_arith)) fun s₃ ⟨e₃, k₃, m₃⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [k₃.rd, k₂.rd], by rw [k₃.wr, k₂.wr]⟩, by rw [m₃]; exact O₂,
    by rw [e₃]; omega_arith, by rw [e₃]; omega_arith, U, by rw [e₃, Nat.add_sub_cancel]; exact eW⟩
  rw [k₃.gpr r (fun h => hr (by
    simp only [List.mem_cons] at h ⊢
    rcases h with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h))))), k₂.gpr r (fun h => hr (by
    simp only [termRegs, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))]

/-- `[o] = [a] [b] 2⁻⁵⁷⁶ mod p` for P-521's `p = m`, without BMI2 and ADX. -/
theorem mulFn_ok {s : State} {base : Addr} {Z : Nat} (hs : Scr s base Z) (hZ : 4096 ≤ Z) {m : Nat}
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (ho : argOf s .rsi + 72 ≤ 3520) (ha : argOf s .rdx + 72 ≤ 3520)
    (hb : argOf s .rcx + 72 ≤ 3520) (hB : wordsVal s.mem base (argOf s .rcx) 9 < m) :
    WP isa mulFn s fun s' =>
      wordsVal s'.mem base (argOf s .rsi) 9 < m ∧
      wordsVal s'.mem base (argOf s .rsi) 9 * (2 ^ 64) ^ 9 % m =
        wordsVal s.mem base (argOf s .rdx) 9 * wordsVal s.mem base (argOf s .rcx) 9 % m ∧
      KeepRegs fnClob s s' ∧
      ∀ x, (ofs base x < argOf s .rsi ∨ argOf s .rsi + 72 ≤ ofs base x) →
        (ofs base x < fnTmp ∨ 4096 ≤ ofs base x) → s'.mem x = s.mem x :=
  fnShape_ok (by decide +kernel) hs hZ hm (midB_ok hm) ho ha hb hB

end VG.Proof.Weierstrass.X86_64.Mont
