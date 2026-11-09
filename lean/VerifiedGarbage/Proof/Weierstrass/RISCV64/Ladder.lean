module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Copy
public import VerifiedGarbage.Proof.Weierstrass.Layout
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.Pow
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# Powers, on RISC-V

A loop counted down in `s1` (`countLoop_ok`), and the mask of bit `s1` of a
number, which `bitMask` reads (`bitMask_ok`), as on PPC64LE
(`Proof/Weierstrass/PPC64LE/Ladder.lean`). The field arithmetic is calls of
the functions of `F`.

`pow P F` leaves `[acc]` reading (in Montgomery form) as `[base]^e`, for the
exponent `e`, the number at `P.bits` (`pow_ok`): an iteration squares the
accumulator, multiplies it by the base into `[tmp]` and keeps that product if
the exponent's bit is set (`powBody_ok`), as on PPC64LE
(`Proof/Weierstrass/PPC64LE/Pow.lean`).
-/

-- separate module: curve-generic, and its proofs (about 3 s) build in parallel with those of
-- the field functions that its importer also imports

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point)

/-! ## The counter and the bit -/

/-- What keeps the callee-saved registers but the counter. -/
structure Kc (s s' : State) : Prop where
  gpr : ∀ r ∈ preserved, r ≠ .s1 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Kc.refl (s : State) : Kc s s := ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem Kc.trans {s₁ s₂ s₃ : State} (h₁ : Kc s₁ s₂) (h₂ : Kc s₂ s₃) : Kc s₁ s₃ :=
  ⟨fun r hr h => (h₂.gpr r hr h).trans (h₁.gpr r hr h), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem Kp.kc {s s' : State} (h : Kp s s') : Kc s s' := ⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, h.sp⟩

theorem Kc.of_rest {ws : List Reg} {s s' : State} (h : Rest ws s s') (hws : ∀ r ∈ ws, r ∉ preserved ∨ r = .s1 := by decide) :
    Kc s s' :=
  ⟨fun r hr hr1 => h.gpr r fun h' => (hws r h').elim (fun h => h hr) hr1, h.rd, h.wr, h.sp⟩

theorem WsReg.of_kc {s s' : State} {base : Addr} (h : WsReg s base) (k : Kc s s') : WsReg s' base :=
  ⟨(k.gpr _ (by decide) (by decide)).trans h.s0, k.wr ▸ h.wr, h.nowrap, h.al⟩

/-- A loop whose body takes the invariant from `j` to `j - 1`, with `s1 = j`
in the invariant, run from `n ≥ 1` (below `2⁶⁴`). -/
theorem countLoop_ok {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop} {n : Nat}
    (hr : ∀ j s, Inv j s → s.gpr .s1 = BitVec.ofNat 64 j)
    (hstep : ∀ j s, 1 ≤ j → j ≤ n → Inv j s → WP isa body s fun s' => Inv (j - 1) s')
    (hQ : ∀ s, Inv 0 s → Q s) (hn : 1 ≤ n) (hn64 : n < 2 ^ 64) {s : State} (hs : Inv n s) :
    WP isa (.loop body more) s Q := by
  refine WP.loop (M := isa) (fun j s => 1 ≤ j ∧ j ≤ n ∧ Inv j s) (fun j s ⟨h1, h2, hi⟩ => ?_) n s
    ⟨hn, Nat.le_refl _, hs⟩
  refine WP.mono (hstep j s h1 h2 hi) fun s' hi' => ?_
  have he := eval_nonzero_ofNat s' .s1 (k := j - 1) (by omega) (hr _ _ hi')
  by_cases hj : j - 1 = 0
  · exact .inl ⟨by rw [he]; simp [hj], hQ s' (by rw [hj] at hi'; exact hi')⟩
  · exact .inr ⟨by rw [he]; simp [hj], j - 1, by omega, by omega, by omega, hi'⟩

theorem ofNat_pred64 {j : Nat} (hj : 1 ≤ j) : BitVec.ofNat 64 j + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (j - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (BitVec.ofInt 64 (-1)).toNat = 2 ^ 64 - 1 from rfl]
  omega

/-- `s1 -= 1`. -/
theorem wp_decCounter {is : List Instr} {s : State} {Q : State → Prop} {j : Nat} (hj : 1 ≤ j)
    (hb : s.gpr .s1 = BitVec.ofNat 64 j)
    (k : ∀ s', Upd s s' .s1 (BitVec.ofNat 64 (j - 1)) → WP isa (.block is) s' Q) :
    WP isa (.block (decCounter :: is)) s Q := by
  refine WP.cons (exec_addi (by decide)) ?_
  rw [hb, ofNat_pred64 hj]; exact k _ (Upd.write _ _ _)

/-- `srl d, n, m`. -/
theorem wp_srlReg {d n m : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (s.gpr n >>> ((s.gpr m).toNat % 64)) → WP isa (.block is) s' Q) :
    WP isa (.block (.shiftReg .srl .d d n m :: is)) s Q :=
  WP.cons rfl (k _ (Upd.write _ _ _))

theorem and1 (w : BitVec 64) (i : Nat) :
    (w >>> i) &&& 1 = if w.toNat.testBit i then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod,
    Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (w.toNat / 2 ^ i) with h | h <;> simp [h]

theorem neg_bit (b : Bool) : (0 : BitVec 64) - (if b then 1 else 0) = if b then BitVec.allOnes 64 else 0 := by
  cases b <;> decide

/-- Bit `j` of a number of words is bit `j mod 64` of its word `j / 64`. -/
theorem testBit_wordsVal (m : Mem) (base : Addr) : ∀ (n src j : Nat), j < 64 * n →
    (word m base (src + 8 * (j / 64))).toNat.testBit (j % 64) = (wordsVal m base src n).testBit j
  | 0, _, _, h => by omega
  | n + 1, src, j, h => by
    rw [wordsVal, Nat.add_comm (word m base src).toNat, Nat.testBit_two_pow_mul_add _ (word m base src).isLt]
    by_cases hj : j < 64
    · rw [ite_eq_left_iff.mpr (fun h => absurd hj h), Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, Nat.mul_zero,
        Nat.add_zero]
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hj), ← testBit_wordsVal m base n (src + 8) (j - 64) (by omega),
        show src + 8 * (j / 64) = src + 8 + 8 * ((j - 64) / 64) by omega, show j % 64 = (j - 64) % 64 by omega]

/-- `a7 = -bit` of bit `j = s1` of the `n`-word number at `src`. -/
theorem bitMask_ok {s : State} {base : Addr} (hw : WsReg s base) {src n j : Nat} (hj : j < 64 * n)
    (hj64 : j < 2 ^ 58) (h1 : s.gpr .s1 = BitVec.ofNat 64 j) (hsrc : src + 8 * n ≤ 4096) (hs8 : src % 8 = 0) :
    WP isa (.block (bitMask src)) s fun s' =>
      s'.gpr .a7 = maskOf ((wordsVal s.mem base src n).testBit j) ∧ Rest [.t0, .t1, .t2, .a7] s s' ∧
        s'.mem = s.mem := by
  have hn := hw.nowrap
  have hq : 8 * (j / 64) + 8 ≤ 8 * n := by
    have : j / 64 < n := Nat.div_lt_of_lt_mul (by omega)
    omega
  rw [bitMask]
  refine wp_srl (by decide) fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ => ?_
  have e3 : s₃.gpr .t0 + BitVec.ofNat 64 src = off base (src + 8 * (j / 64)) := by
    rw [u₃.gpr, u₂.gpr, u₂.other .s0 (by decide), u₁.gpr, u₁.other .s0 (by decide), h1, hw.s0]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, off]
    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)]
    omega
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have r₃ : Rest [.t0] s s₃ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide)))
  show WP isa (.block (ldAt .t1 .t0 src ++ [.shiftReg .srl .d .t1 .t1 ctr, .logicImm .and .t1 .t1 1,
    .li .t2 0, .sub .a7 .t2 .t1])) s₃ _
  refine wp_ldAt (by omega) e3 (by simp only [off]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := hw.al; omega)
    ⟨_, List.mem_append_right _ (r₃.wr ▸ hw.wr), Offset.contains_base base (by omega) (by omega)⟩ fun s₄ u₄ => ?_
  refine wp_srlReg fun s₅ u₅ => wp_andi (imm := 1) (by decide) fun s₆ u₆ => ?_
  refine wp_li (imm := 0) (by decide) fun s₇ u₇ => wp_sub fun s₈ u₈ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [u₈.gpr, u₇.gpr, u₇.other .t1 (by decide), u₆.gpr, u₅.gpr, u₄.gpr,
      u₄.other .s1 (by decide), r₃.gpr .s1 (by decide), h1, m₃, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), show BitVec.ofInt 64 1 = 1 from rfl, and1,
      testBit_wordsVal s.mem base n src j hj, show BitVec.ofNat 64 0 = 0 from rfl, neg_bit]
  · exact (r₃.mono (by decide)).trans ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans
      ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans (u₈.rest (by decide))))))
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃]

/-! ## The ladder -/

/-- What a slot holding `x` stands for, modulo `C.p`. -/
abbrev tmv (C : Curve) (n : Nat) (base : Addr) (s : State) (x : Nat) : Fe C :=
  toM C.p (2 ^ (64 * n)) (wordsVal s.mem base x n)

theorem own_add (n : Nat) (h : 8 * n ≤ own n) : own n + 64 * n ≤ 8192 := by
  have := rvOwn_cases n; simp only [own] at h ⊢; omega

/-! ## Powers -/

/-- What a power writes, for numbers of `k` words: the accumulator, the
temporary and the functions' own working space. -/
def powWx (P : PowCfg) (k : Nat) : List (Nat × Nat) :=
  [(P.acc, 8 * k), (P.tmp, 8 * k), (own k, 64 * k)]

/-- Where a power's slots are, for numbers of `k` words: below the
functions' own working space and in the first 2048 bytes, at multiples of 8,
and what it reads apart from what it writes. -/
structure PowLayR (P : PowCfg) (k : Nat) : Prop where
  acc : P.acc + 8 * k ≤ own k
  tmp : P.tmp + 8 * k ≤ own k
  base : P.base + 8 * k ≤ own k
  one : P.one + 8 * k ≤ own k
  short : P.acc + 8 * k ≤ 4096 ∧ P.tmp + 8 * k ≤ 4096 ∧ P.base + 8 * k ≤ 4096 ∧ P.one + 8 * k ≤ 4096 ∧
    P.bits + 8 * k ≤ 4096
  nbits : 1 ≤ P.nbits ∧ P.nbits ≤ 64 * k ∧ P.nbits < 2048
  k1 : 1 ≤ k
  acc_tmp : P.acc + 8 * k ≤ P.tmp ∨ P.tmp + 8 * k ≤ P.acc
  acc_one : P.acc + 8 * k ≤ P.one ∨ P.one + 8 * k ≤ P.acc
  base_acc : P.base + 8 * k ≤ P.acc ∨ P.acc + 8 * k ≤ P.base
  base_tmp : P.base + 8 * k ≤ P.tmp ∨ P.tmp + 8 * k ≤ P.base
  bits_w : ∀ w ∈ powWx P k, P.bits + 8 * k ≤ w.1 ∨ w.1 + w.2 ≤ P.bits
  acc8 : P.acc % 8 = 0
  tmp8 : P.tmp % 8 = 0
  one8 : P.one % 8 = 0
  bits8 : P.bits % 8 = 0

/-- The loop's invariant at `s1 = j`: the accumulator reads as
`B^(e >>> j)`, for `B` what the base reads as at the start. -/
structure PowInv (P : PowCfg) (k : Nat) (base : Addr) (m e : Nat) [NeZero m] (s₀ s : State)
    (j : Nat) : Prop where
  ws : WsReg s base
  ctr : s.gpr .s1 = BitVec.ofNat 64 j
  keep : Kc s₀ s
  unch : Unch base (powWx P k) s₀.mem s.mem
  lt : wordsVal s.mem base P.acc k < m
  val : toM m (2 ^ (64 * k)) (wordsVal s.mem base P.acc k) =
    toM m (2 ^ (64 * k)) (wordsVal s₀.mem base P.base k) ^ (e >>> j)

/-- An iteration. -/
theorem powBody_ok {P : PowCfg} {F : Field} [NeZero F.S.m] (hF : FieldOk F)
    (hk : P.M.n = F.S.k) (hL : PowLayR P F.S.k) (hm : UnitMod F.S.m (2 ^ (64 * F.S.k))) {base : Addr}
    {s₀ : State} {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ P.nbits)
    (hI : PowInv P F.S.k base F.S.m (wordsVal s₀.mem base P.bits F.S.k) s₀ s j) :
    WP isa (powBody P F) s fun s' => PowInv P F.S.k base F.S.m (wordsVal s₀.mem base P.bits F.S.k) s₀ s' (j - 1) := by
  have hn := hI.ws.nowrap
  have := hL.acc; have := hL.tmp; have := hL.base
  have hsh := hL.short
  have hk1 := hL.k1
  have hnb := hL.nbits
  have hat := hL.acc_tmp
  have hba := hL.base_acc
  have hbt := hL.base_tmp
  have ho : own F.S.k + 64 * F.S.k ≤ 8192 := own_add F.S.k (by omega)
  have hBs : wordsVal s.mem base P.base F.S.k = wordsVal s₀.mem base P.base F.S.k :=
    hI.unch.wordsVal (fun w hw => by
      simp only [powWx, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact hba
      · exact hbt
      · exact .inl hL.base) (by omega)
  -- `s1 -= 1` and `acc = acc²`.
  rw [powBody]
  refine WP.seq (wp_decCounter hj hI.ctr fun s₁ u₁ => WP.block_nil ?_)
  have K₁ : Kc s s₁ := Kc.of_rest (u₁.rest (ws := [.s1]) (by decide))
  have w₁ := hI.ws.of_kc K₁
  have m₁ : s₁.mem = s.mem := u₁.mem
  have c₁ : s₁.gpr .s1 = BitVec.ofNat 64 (j - 1) := u₁.gpr
  refine WP.seq (WP.mono (mulCall_ok hF w₁ hL.acc hL.acc hL.acc (by omega) (by omega) (by omega)
    (by rw [m₁]; exact hI.lt)) fun s₂ ⟨K₂, lt₂, e₂⟩ => ?_)
  have v₂ : toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s₂.mem base P.acc F.S.k) =
      toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s.mem base P.acc F.S.k) ^ 2 := by
    rw [toM_mul hm e₂, m₁, Lean.Grind.Semiring.pow_two]
  have U₂ : Unch base [(P.acc, 8 * F.S.k), (own F.S.k, 64 * F.S.k)] s.mem s₂.mem := by rw [← m₁]; exact K₂.mem
  have hB₂ : wordsVal s₂.mem base P.base F.S.k = wordsVal s₀.mem base P.base F.S.k := by
    rw [U₂.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hba
      · exact .inl hL.base) (by omega), hBs]
  -- `tmp = base · acc`.
  have w₂ := w₁.of_kp K₂.kp
  refine WP.seq (WP.mono (mulCall_ok hF w₂ hL.tmp hL.base hL.acc (by omega) (by omega) (by omega) lt₂)
    fun s₃ ⟨K₃, lt₃, e₃⟩ => ?_)
  have U₃ : Unch base [(P.tmp, 8 * F.S.k), (own F.S.k, 64 * F.S.k)] s₂.mem s₃.mem := K₃.mem
  have hA₃ : wordsVal s₃.mem base P.acc F.S.k = wordsVal s₂.mem base P.acc F.S.k :=
    U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hat
      · exact .inl hL.acc) (by omega)
  have v₃ : toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s₃.mem base P.tmp F.S.k) =
      toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s₂.mem base P.acc F.S.k) *
        toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s₀.mem base P.base F.S.k) := by
    rw [toM_mul hm e₃, hB₂, Lean.Grind.CommSemiring.mul_comm]
  -- The mask of bit `j - 1`, and the selection.
  have hU₃ : Unch base (powWx P F.S.k) s₀.mem s₃.mem := by
    refine ((hI.unch.trans U₂).trans U₃).mono fun w hw => ?_
    simp only [powWx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with ((h | h | h) | h | h) | h | h <;> simp [h]
  have hE₃ : wordsVal s₃.mem base P.bits F.S.k = wordsVal s₀.mem base P.bits F.S.k :=
    hU₃.wordsVal hL.bits_w (by omega)
  have w₃ := w₂.of_kp K₃.kp
  have c₃ : s₃.gpr .s1 = BitVec.ofNat 64 (j - 1) := by rw [K₃.kp.gpr _ (by decide), K₂.kp.gpr _ (by decide), c₁]
  refine WP.block_append (WP.mono (bitMask_ok w₃ (src := P.bits) (n := F.S.k) (by omega) (by omega) c₃
    (by omega) hL.bits8) fun s₄ ⟨g₄, k₄, m₄⟩ => ?_)
  rw [hE₃] at g₄
  rw [hk]
  refine WP.mono (sel_ok ((wordsVal s₀.mem base P.bits F.S.k).testBit (j - 1)) F.S.k (w₃.of_rest k₄) g₄
    (o := P.acc) (a := P.acc) (b := P.tmp) hL.acc8 hL.acc8 hL.tmp8 (by omega) (by omega) (by omega)
    (Or.inl (Nat.le_refl _)) (by omega)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have k₅' : Kc s₃ s₅ := (Kc.of_rest k₄).trans (Kc.of_rest k₅)
  refine ⟨w₃.of_kc k₅', by rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), c₃],
    ((hI.keep.trans K₁).trans K₂.kp.kc).trans (K₃.kp.kc.trans k₅'), fun x hx => ?_, ?_, ?_⟩
  · rw [O₅ x (hx _ (List.mem_cons_self ..)), m₄]
    exact hU₃ x hx
  · rw [e₅, m₄]
    split
    · exact lt₃
    · rw [hA₃]; exact lt₂
  · rw [e₅, m₄, pow_shiftRight _ _ (j - 1), Nat.sub_add_cancel hj, ← hI.val]
    split
    · rw [v₃, v₂]
    · rw [hA₃, v₂, Lean.Grind.Semiring.mul_one]

/-- `[acc] = [base]^e` in Montgomery form, for the exponent `e`, the number at
`P.bits`, below `2^nbits`; only `s1`, caller-saved registers and `powWx`
change. -/
theorem pow_ok {P : PowCfg} {F : Field} [NeZero F.S.m] (hF : FieldOk F)
    (hk : P.M.n = F.S.k) (hL : PowLayR P F.S.k) (hm : UnitMod F.S.m (2 ^ (64 * F.S.k))) {base : Addr}
    {s : State} (hs : WsReg s base) (hm0 : 0 < F.S.m)
    (hO : wordsVal s.mem base P.one F.S.k = 2 ^ (64 * F.S.k) % F.S.m)
    (he : wordsVal s.mem base P.bits F.S.k < 2 ^ P.nbits) :
    WP isa (pow P F) s fun s' => Kc s s' ∧ Unch base (powWx P F.S.k) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc F.S.k < F.S.m ∧
      toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s'.mem base P.acc F.S.k) =
        toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s.mem base P.base F.S.k) ^ wordsVal s.mem base P.bits F.S.k := by
  have hn := hs.nowrap
  have hnb := hL.nbits
  have hsh := hL.short
  have := hL.acc; have := hL.one
  have hao := hL.acc_one
  have hba := hL.base_acc
  rw [pow, hk]
  refine WP.seq (WP.block_append (WP.mono (copy_ok F.S.k hs (o := P.acc) (a := P.one) hL.acc8 hL.one8
    (by omega) (by omega) (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ =>
      wp_li hnb.2.2 fun s₂ u₂ => WP.block_nil ?_))
  have K : Kc s s₂ := (Kc.of_rest k₁).trans (Kc.of_rest (u₂.rest (ws := [.s1]) (by decide)))
  have m₂ : s₂.mem = s₁.mem := u₂.mem
  have hE : wordsVal s₂.mem base P.bits F.S.k = wordsVal s.mem base P.bits F.S.k := by
    rw [m₂]; exact O₁.wordsVal (by have := hL.bits_w _ (List.mem_cons_self ..); exact this) (by omega)
  refine countLoop_ok (Inv := fun j s' => PowInv P F.S.k base F.S.m (wordsVal s₂.mem base P.bits F.S.k) s₂ s' j)
    (n := P.nbits)
    (fun j s' hi => hi.ctr) (fun j s' h1 h2 hi => powBody_ok hF hk hL hm h1 h2 hi)
    (fun s' hi => ?_) hnb.1 (by omega) ?_
  · have hB₂ : wordsVal s₂.mem base P.base F.S.k = wordsVal s.mem base P.base F.S.k := by
      rw [m₂, O₁.wordsVal (by omega) (by omega)]
    refine ⟨K.trans hi.keep, ?_, hi.lt, by rw [hi.val, Nat.shiftRight_zero, hB₂, hE]⟩
    exact (O₁.unch.trans (by rw [← m₂]; exact hi.unch)).mono fun w hw => by
      simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with rfl | hw
      · simp [powWx]
      · exact hw
  · have hv : wordsVal s₂.mem base P.acc F.S.k = wordsVal s.mem base P.one F.S.k := by rw [m₂, e₁]
    refine ⟨hs.of_kc K, u₂.gpr, Kc.refl _, Unch.refl _ _ _, ?_, ?_⟩
    · rw [hv, hO]; exact Nat.mod_lt _ hm0
    · rw [hv, hO, toM_one hm, hE, shiftRight_eq_zero he, Lean.Grind.Semiring.pow_zero]

/-! ## Powers by a chain -/

/-- What a power by a chain writes, for numbers of `k` words: the result, the
table and the functions' own working space. -/
def chainWx (P : ChainCfg) (k : Nat) : List (Nat × Nat) :=
  [(P.acc, 8 * k), (P.tbl, 9 * (8 * k)), (own k, 64 * k)]

/-- Where a chain's slots are, for numbers of `k` words: below the
functions' own working space (and so at offsets `liAt` reaches), at
multiples of 8, apart. -/
structure ChainLayR (P : ChainCfg) (k : Nat) : Prop where
  n : P.M.n = k
  k1 : 1 ≤ k
  acc : P.acc + 8 * k ≤ own k
  base : P.base + 8 * k ≤ own k
  tbl : P.tbl + 9 * (8 * k) ≤ own k
  short : P.acc + 8 * k ≤ 4096 ∧ P.base + 8 * k ≤ 4096 ∧ P.tbl + 9 * (8 * k) ≤ 4096
  acc8 : P.acc % 8 = 0
  base8 : P.base % 8 = 0
  tbl8 : P.tbl % 8 = 0
  acc_base : P.acc + 8 * k ≤ P.base ∨ P.base + 8 * k ≤ P.acc
  acc_tbl : P.acc + 8 * k ≤ P.tbl ∨ P.tbl + 9 * (8 * k) ≤ P.acc
  base_tbl : P.base + 8 * k ≤ P.tbl ∨ P.tbl + 9 * (8 * k) ≤ P.base

/-- The chain is the exponent's: odd digits up to 15, counts `li` can load,
and the value `e`. -/
structure ChainOkR (P : ChainCfg) (e : Nat) : Prop where
  first : P.first % 2 = 1 ∧ P.first ≤ 15
  steps : ∀ st ∈ P.steps, st.1 < 2048 ∧ (st.2 = 0 ∨ (st.2 % 2 = 1 ∧ st.2 ≤ 15))
  val : chainVal P.first P.steps = e

/-- `ChainOkR`, as a computation. -/
def chainCheckR (first : Nat) (steps : List (Nat × Nat)) (e : Nat) : Bool :=
  first % 2 == 1 && decide (first ≤ 15) &&
    steps.all (fun st => decide (st.1 < 2048) && (st.2 == 0 || (st.2 % 2 == 1 && decide (st.2 ≤ 15)))) &&
    chainVal first steps == e

theorem ChainOkR.of_check {P : ChainCfg} {e : Nat} (h : chainCheckR P.first P.steps e = true) :
    ChainOkR P e := by
  simp only [chainCheckR, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨⟨h1, h2⟩, fun st hst => ⟨(h3 st hst).1, (h3 st hst).2.imp id fun h => ⟨h.1, h.2⟩⟩, h4⟩

section chain

variable {P : ChainCfg} {k : Nat}

theorem slotR_eq (hL : ChainLayR P k) (i : Nat) : P.slot i = P.tbl + 8 * k * i := by
  simp only [ChainCfg.slot, hL.n]

/-- Slot `i ≤ 8` of the table, in its area. -/
theorem slotR_le (hL : ChainLayR P k) {i : Nat} (hi : i ≤ 8) :
    P.tbl ≤ P.slot i ∧ P.slot i + 8 * k ≤ P.tbl + 9 * (8 * k) := by
  have := Nat.mul_le_mul_left (8 * k) hi
  rw [slotR_eq hL]
  omega_arith

theorem slotR_apart (hL : ChainLayR P k) {i j : Nat} (h : i ≠ j) :
    P.slot i + 8 * k ≤ P.slot j ∨ P.slot j + 8 * k ≤ P.slot i := by
  rw [slotR_eq hL, slotR_eq hL]
  rcases Nat.lt_or_gt_of_ne h with h | h
  · left; have := Nat.mul_le_mul_left (8 * k) (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at this; omega_arith
  · right; have := Nat.mul_le_mul_left (8 * k) (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at this; omega_arith

theorem slotR_mod8 (hL : ChainLayR P k) (i : Nat) : P.slot i % 8 = 0 := by
  rw [slotR_eq hL, Nat.mul_assoc]; have := hL.tbl8; omega_arith

/-- What holds throughout the power, from `s₀`. -/
structure CSt (P : ChainCfg) (k : Nat) (base : Addr) (s₀ s : State) : Prop where
  ws : WsReg s base
  keep : Kc s₀ s
  unch : Unch base (chainWx P k) s₀.mem s.mem

/-- A call writing the result or a table slot. -/
theorem CSt.call {base : Addr} {s₀ s s' : State} (h : CSt P k base s₀ s) {o : Nat}
    (ho : o = P.acc ∨ (P.tbl ≤ o ∧ o + 8 * k ≤ P.tbl + 9 * (8 * k))) (K : CallKeep k base o s s') :
    CSt P k base s₀ s' := by
  refine ⟨h.ws.of_kp K.kp, h.keep.trans K.kp.kc, (h.unch.trans K.mem).cover fun w hw => ?_⟩
  simp only [chainWx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with (rfl | rfl | rfl) | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Nat.le_refl _, Nat.le_refl _⟩
  · rcases ho with rfl | ho
    · exact ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(P.tbl, 9 * (8 * k)), List.mem_cons_of_mem _ (List.mem_cons_self ..), ho.1, ho.2⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Nat.le_refl _, Nat.le_refl _⟩

/-- A copy into the result or a table slot. -/
theorem CSt.copy {base : Addr} {s₀ s s' : State} (h : CSt P k base s₀ s) {o : Nat}
    (ho : o = P.acc ∨ (P.tbl ≤ o ∧ o + 8 * k ≤ P.tbl + 9 * (8 * k)))
    (hr : Rest [.t0] s s') (hO : Outside base o (8 * k) s.mem s'.mem) : CSt P k base s₀ s' := by
  refine ⟨h.ws.of_rest hr, h.keep.trans (Kc.of_rest hr), (h.unch.trans hO.unch).cover fun w hw => ?_⟩
  simp only [chainWx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with (rfl | rfl | rfl) | rfl
  · exact ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), Nat.le_refl _, Nat.le_refl _⟩
  · rcases ho with rfl | ho
    · exact ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(P.tbl, 9 * (8 * k)), List.mem_cons_of_mem _ (List.mem_cons_self ..), ho.1, ho.2⟩

/-- `B`, what the base reads as. -/
abbrev bvR (P : ChainCfg) (k : Nat) (base : Addr) (m : Nat) [NeZero m] (s : State) : Fin m :=
  toM m (2 ^ (64 * k)) (wordsVal s.mem base P.base k)

/-- The table's slots hold the odd powers `B^(2 i + 1)` for `i < c` and `B²`. -/
def TblR (P : ChainCfg) (k : Nat) (base : Addr) (m : Nat) [NeZero m] (B : Fin m) (c : Nat) (s : State) :
    Prop :=
  (∀ i < c, wordsVal s.mem base (P.slot i) k < m ∧
    toM m (2 ^ (64 * k)) (wordsVal s.mem base (P.slot i) k) = B ^ (2 * i + 1)) ∧
  wordsVal s.mem base (P.slot 8) k < m ∧
    toM m (2 ^ (64 * k)) (wordsVal s.mem base (P.slot 8) k) = B ^ 2

/-- A write to the result keeps the table. -/
theorem TblR.acc {base : Addr} {m : Nat} [NeZero m] {B : Fin m} {c : Nat}
    (hL : ChainLayR P k) {s s' : State} (h : TblR P k base m B c s)
    (hc : c ≤ 8) (U : Unch base [(P.acc, 8 * k), (own k, 64 * k)] s.mem s'.mem) :
    TblR P k base m B c s' := by
  have e : ∀ i ≤ 8, wordsVal s'.mem base (P.slot i) k = wordsVal s.mem base (P.slot i) k :=
    fun i hi => U.wordsVal (fun w hw => by
      have := slotR_le hL hi; have := hL.tbl; have := hL.acc_tbl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · omega_arith
      · exact .inl (by omega_arith)) (by have := slotR_le hL hi; have := hL.short; omega_arith)
  exact ⟨fun i hi => by rw [e i (by omega_arith)]; exact h.1 i hi, by rw [e 8 (Nat.le_refl _)]; exact h.2⟩

variable {F : Field} [NeZero F.S.m]

/-- The odd powers `B³ … B^(2 c + 1)`. -/
theorem odd_ok (hF : FieldOk F) (hL : ChainLayR P F.S.k) (hm : UnitMod F.S.m (2 ^ (64 * F.S.k)))
    {base : Addr} {s₀ : State} :
    ∀ (c : Nat) {s : State}, c ≤ 7 → CSt P F.S.k base s₀ s →
      TblR P F.S.k base F.S.m (bvR P F.S.k base F.S.m s₀) 1 s →
      WP isa (ChainR.odd P F c) s fun s' => CSt P F.S.k base s₀ s' ∧
        TblR P F.S.k base F.S.m (bvR P F.S.k base F.S.m s₀) (c + 1) s'
  | 0, _, _, h, T => WP.block_nil ⟨h, T⟩
  | c + 1, s, hc, h, T => by
    rw [ChainR.odd]
    refine WP.seq (WP.mono (odd_ok hF hL hm c (by omega) h T) fun t ⟨St, Tt⟩ => ?_)
    have hin : ∀ i ≤ 8, P.slot i + 8 * F.S.k ≤ own F.S.k ∧ P.slot i < 4095 := fun i hi => by
      have := slotR_le hL hi; have := hL.tbl; have := hL.short; have := hL.k1; omega_arith
    have Ti := Tt.1 c (by omega)
    refine WP.mono (mulCall_ok hF St.ws (hin (c + 1) (by omega)).1 (hin c (by omega)).1 (hin 8 (Nat.le_refl _)).1
      (hin (c + 1) (by omega)).2 (hin c (by omega)).2 (hin 8 (Nat.le_refl _)).2 Tt.2.1) fun u ⟨Ku, ltu, eu⟩ => ?_
    have hn := St.ws.nowrap
    refine ⟨St.call (Or.inr (slotR_le hL (by omega))) Ku, ?_⟩
    have e : ∀ j ≤ 8, j ≠ c + 1 →
        wordsVal u.mem base (P.slot j) F.S.k = wordsVal t.mem base (P.slot j) F.S.k := fun j hj hne =>
      (show Unch base _ _ _ from Ku.mem).wordsVal (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact slotR_apart hL hne
        · exact .inl (hin j hj).1) (by have := slotR_le hL hj; have := hL.short; omega_arith)
    refine ⟨fun i hi => ?_, by rw [e 8 (Nat.le_refl _) (by omega)]; exact Tt.2.1,
      by rw [e 8 (Nat.le_refl _) (by omega)]; exact Tt.2.2⟩
    rcases Nat.lt_or_ge i (c + 1) with h' | h'
    · rw [e i (by omega) (by omega)]; exact Tt.1 i h'
    · obtain rfl : i = c + 1 := by omega
      refine ⟨ltu, ?_⟩
      rw [toM_mul hm eu, Ti.2, Tt.2.2, ← Lean.Grind.Semiring.pow_add]
      congr 1

/-- The table: `x` (reduced), `x²` and the odd powers. -/
theorem table_ok (hF : FieldOk F) (hL : ChainLayR P F.S.k) (hm : UnitMod F.S.m (2 ^ (64 * F.S.k)))
    {base : Addr} {s : State} {one : Nat} (hone : one + 8 * F.S.k ≤ own F.S.k) (hone' : one < 4095)
    (hO : wordsVal s.mem base one F.S.k = 2 ^ (64 * F.S.k) % F.S.m) (h : CSt P F.S.k base s s) :
    WP isa (ChainR.table P F one) s fun s' =>
      CSt P F.S.k base s s' ∧ TblR P F.S.k base F.S.m (bvR P F.S.k base F.S.m s) 8 s' := by
  have hn := h.ws.nowrap
  have hin : ∀ i ≤ 8, P.slot i + 8 * F.S.k ≤ own F.S.k ∧ P.slot i < 4095 ∧ P.slot i + 8 * F.S.k ≤ 4096 :=
    fun i hi => by have := slotR_le hL hi; have := hL.tbl; have := hL.short; have := hL.k1; omega_arith
  have hsh := hL.short
  have := hL.base
  have := hL.k1
  have hm0 : 0 < F.S.m := Nat.pos_of_ne_zero (NeZero.ne _)
  rw [ChainR.table]
  refine WP.seq (WP.mono (mulCall_ok hF h.ws (hin 0 (by decide)).1 hL.base hone (hin 0 (by decide)).2.1
    (by omega) hone' (by rw [hO]; exact Nat.mod_lt _ hm0)) fun s₁ ⟨K₁, lt₁, e₁⟩ => ?_)
  have S₁ := h.call (Or.inr (slotR_le hL (by decide))) K₁
  have v₁ : toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s₁.mem base (P.slot 0) F.S.k) = bvR P F.S.k base F.S.m s := by
    rw [toM_mul hm e₁, hO, toM_one hm, Lean.Grind.Semiring.mul_one]
  refine WP.seq (WP.mono (mulCall_ok hF S₁.ws (hin 8 (Nat.le_refl _)).1 (hin 0 (by decide)).1
    (hin 0 (by decide)).1 (hin 8 (Nat.le_refl _)).2.1 (hin 0 (by decide)).2.1 (hin 0 (by decide)).2.1 lt₁)
    fun s₂ ⟨K₂, lt₂, e₂⟩ => ?_)
  have S₂ := S₁.call (Or.inr (slotR_le hL (Nat.le_refl _))) K₂
  have e0 : wordsVal s₂.mem base (P.slot 0) F.S.k = wordsVal s₁.mem base (P.slot 0) F.S.k :=
    (show Unch base _ _ _ from K₂.mem).wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact slotR_apart hL (by decide)
      · exact .inl (hin 0 (by decide)).1) (by have := hin 0 (by decide); omega_arith)
  have T₂ : TblR P F.S.k base F.S.m (bvR P F.S.k base F.S.m s) 1 s₂ := by
    refine ⟨fun i hi => ?_, lt₂, ?_⟩
    · obtain rfl : i = 0 := by omega
      rw [e0]
      exact ⟨lt₁, by rw [v₁, Nat.mul_zero, Nat.zero_add, Lean.Grind.Semiring.pow_one]⟩
    · rw [toM_mul hm e₂, v₁, Lean.Grind.Semiring.pow_two]
  exact odd_ok hF hL hm 7 (Nat.le_refl _) S₂ T₂

/-- `acc = acc^(2^c)`, from `B^v`. -/
theorem squares_ok (hF : FieldOk F) (hL : ChainLayR P F.S.k) (hm : UnitMod F.S.m (2 ^ (64 * F.S.k)))
    {base : Addr} {s₀ s : State} {v c : Nat} (hc1 : 1 ≤ c) (hc : c < 2048)
    (h : CSt P F.S.k base s₀ s) (hT : TblR P F.S.k base F.S.m (bvR P F.S.k base F.S.m s₀) 8 s)
    (hlt : wordsVal s.mem base P.acc F.S.k < F.S.m)
    (hv : toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s.mem base P.acc F.S.k) = bvR P F.S.k base F.S.m s₀ ^ v) :
    WP isa (ChainR.squares P F c) s fun s' => CSt P F.S.k base s₀ s' ∧
      TblR P F.S.k base F.S.m (bvR P F.S.k base F.S.m s₀) 8 s' ∧ wordsVal s'.mem base P.acc F.S.k < F.S.m ∧
      toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s'.mem base P.acc F.S.k) =
        bvR P F.S.k base F.S.m s₀ ^ (v * 2 ^ c) := by
  have hsh := hL.short
  have := hL.acc
  have := hL.k1
  rw [ChainR.squares]
  refine WP.seq (wp_li hc fun s₁ u₁ => WP.block_nil ?_)
  have K₁ : Kc s s₁ := Kc.of_rest (u₁.rest (ws := [.s1]) (by decide))
  have m₁ : s₁.mem = s.mem := u₁.mem
  have S₁ : CSt P F.S.k base s₀ s₁ := ⟨h.ws.of_kc K₁, h.keep.trans K₁, by rw [m₁]; exact h.unch⟩
  refine countLoop_ok (n := c) (Inv := fun j t => CSt P F.S.k base s₀ t ∧
      TblR P F.S.k base F.S.m (bvR P F.S.k base F.S.m s₀) 8 t ∧ t.gpr .s1 = BitVec.ofNat 64 j ∧
      wordsVal t.mem base P.acc F.S.k < F.S.m ∧
      toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal t.mem base P.acc F.S.k) =
        bvR P F.S.k base F.S.m s₀ ^ (v * 2 ^ (c - j)))
    (fun j t hi => hi.2.2.1) (fun j t h1 h2 ⟨St, Tt, ct, lt, vt⟩ => ?_)
    (fun t ⟨St, Tt, _, lt, vt⟩ => ⟨St, Tt, lt, by rw [vt, Nat.sub_zero]⟩) hc1 (by omega)
    ⟨S₁, by unfold TblR; rw [m₁]; exact hT, u₁.gpr, by rw [m₁]; exact hlt,
      by rw [m₁, hv, Nat.sub_self, Nat.pow_zero, Nat.mul_one]⟩
  refine WP.seq (wp_decCounter h1 ct fun u uu => WP.block_nil ?_)
  have Ku : Kc t u := Kc.of_rest (uu.rest (ws := [.s1]) (by decide))
  have mu : u.mem = t.mem := uu.mem
  have Su : CSt P F.S.k base s₀ u := ⟨St.ws.of_kc Ku, St.keep.trans Ku, by rw [mu]; exact St.unch⟩
  refine WP.mono (mulCall_ok hF Su.ws hL.acc hL.acc hL.acc (by omega) (by omega) (by omega)
    (by rw [mu]; exact lt)) fun w ⟨Kw, ltw, ew⟩ => ?_
  have Uw : Unch base [(P.acc, 8 * F.S.k), (own F.S.k, 64 * F.S.k)] t.mem w.mem := by rw [← mu]; exact Kw.mem
  refine ⟨Su.call (Or.inl rfl) Kw, Tt.acc hL (Nat.le_refl _) Uw, by rw [Kw.kp.gpr _ (by decide), uu.gpr], ltw, ?_⟩
  rw [toM_mul hm ew, mu, vt, ← Lean.Grind.Semiring.pow_add]
  congr 1
  rw [← Nat.mul_add, ← Nat.two_mul, show c - (j - 1) = c - j + 1 by omega, Nat.pow_succ]
  grind

/-- A step: `B^v` to `B^(v 2^c + d)`. -/
theorem stepR_ok (hF : FieldOk F) (hL : ChainLayR P F.S.k) (hm : UnitMod F.S.m (2 ^ (64 * F.S.k)))
    {base : Addr} {s₀ s : State} {v c d : Nat} (hc : c < 2048) (hd : d = 0 ∨ (d % 2 = 1 ∧ d ≤ 15))
    (h : CSt P F.S.k base s₀ s) (hT : TblR P F.S.k base F.S.m (bvR P F.S.k base F.S.m s₀) 8 s)
    (hlt : wordsVal s.mem base P.acc F.S.k < F.S.m)
    (hv : toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s.mem base P.acc F.S.k) = bvR P F.S.k base F.S.m s₀ ^ v) :
    WP isa (ChainR.step P F (c, d)) s fun s' => CSt P F.S.k base s₀ s' ∧
      TblR P F.S.k base F.S.m (bvR P F.S.k base F.S.m s₀) 8 s' ∧ wordsVal s'.mem base P.acc F.S.k < F.S.m ∧
      toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s'.mem base P.acc F.S.k) =
        bvR P F.S.k base F.S.m s₀ ^ (v * 2 ^ c + d) := by
  have hsh := hL.short
  have := hL.acc
  have := hL.k1
  rw [ChainR.step]
  have hsq : WP isa (if c = 0 then .block [] else ChainR.squares P F c) s fun s' =>
      CSt P F.S.k base s₀ s' ∧ TblR P F.S.k base F.S.m (bvR P F.S.k base F.S.m s₀) 8 s' ∧
      wordsVal s'.mem base P.acc F.S.k < F.S.m ∧
      toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s'.mem base P.acc F.S.k) =
        bvR P F.S.k base F.S.m s₀ ^ (v * 2 ^ c) := by
    split
    · rename_i h0; subst h0
      exact WP.block_nil ⟨h, hT, hlt, by rw [hv, Nat.pow_zero, Nat.mul_one]⟩
    · exact squares_ok hF hL hm (by omega) hc h hT hlt hv
  refine WP.seq (WP.mono hsq fun s₁ ⟨S₁, T₁, lt₁, v₁⟩ => ?_)
  split
  · rename_i h0; subst h0
    exact WP.block_nil ⟨S₁, T₁, lt₁, by rw [v₁, Nat.add_zero]⟩
  · rename_i h0
    obtain ⟨hd1, hd2⟩ : d % 2 = 1 ∧ d ≤ 15 := hd.resolve_left h0
    have hi : (d - 1) / 2 ≤ 8 := by omega
    have Ti := T₁.1 ((d - 1) / 2) (by omega)
    have hle := slotR_le hL hi
    have := hL.tbl
    refine WP.mono (mulCall_ok hF S₁.ws hL.acc hL.acc (by omega) (by omega) (by omega) (by omega) Ti.1)
      fun s₂ ⟨K₂, lt₂, e₂⟩ => ?_
    refine ⟨S₁.call (Or.inl rfl) K₂, T₁.acc hL (Nat.le_refl _) K₂.mem, lt₂, ?_⟩
    rw [toM_mul hm e₂, v₁, Ti.2, ← Lean.Grind.Semiring.pow_add]
    congr 1
    omega

theorem stepsR_ok (hF : FieldOk F) (hL : ChainLayR P F.S.k) (hm : UnitMod F.S.m (2 ^ (64 * F.S.k)))
    {base : Addr} {s₀ : State} :
    ∀ (sts : List (Nat × Nat)) {s : State} {v : Nat},
      (∀ st ∈ sts, st.1 < 2048 ∧ (st.2 = 0 ∨ (st.2 % 2 = 1 ∧ st.2 ≤ 15))) →
      CSt P F.S.k base s₀ s → TblR P F.S.k base F.S.m (bvR P F.S.k base F.S.m s₀) 8 s →
      wordsVal s.mem base P.acc F.S.k < F.S.m →
      toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s.mem base P.acc F.S.k) = bvR P F.S.k base F.S.m s₀ ^ v →
      WP isa (ChainR.steps P F sts) s fun s' => CSt P F.S.k base s₀ s' ∧
        wordsVal s'.mem base P.acc F.S.k < F.S.m ∧
        toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s'.mem base P.acc F.S.k) =
          bvR P F.S.k base F.S.m s₀ ^ chainVal v sts
  | [], _, _, _, h, _, hlt, hv => WP.block_nil ⟨h, hlt, hv⟩
  | (c, d) :: rest, s, v, hst, h, hT, hlt, hv => by
    rw [ChainR.steps]
    have h1 := hst (c, d) (List.mem_cons_self ..)
    exact WP.seq (WP.mono (stepR_ok hF hL hm h1.1 h1.2 h hT hlt hv) fun s₁ ⟨S₁, T₁, lt₁, v₁⟩ =>
      stepsR_ok hF hL hm rest (fun st hs => hst st (List.mem_cons_of_mem _ hs)) S₁ T₁ lt₁ v₁)

/-- `[acc] = [base]^e` in Montgomery form, for the exponent `e` of the chain,
with `R mod m` at `one`; only `s1`, caller-saved registers and `chainWx`
change. -/
theorem chainPow_ok (hF : FieldOk F) (hL : ChainLayR P F.S.k) (hm : UnitMod F.S.m (2 ^ (64 * F.S.k)))
    {base : Addr} {s : State} {e one : Nat} (hs : WsReg s base) (hone : one + 8 * F.S.k ≤ own F.S.k)
    (hone' : one < 4095) (hO : wordsVal s.mem base one F.S.k = 2 ^ (64 * F.S.k) % F.S.m)
    (hC : ChainOkR P e) :
    WP isa (chainPow P one F) s fun s' => Kc s s' ∧ Unch base (chainWx P F.S.k) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc F.S.k < F.S.m ∧
      toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s'.mem base P.acc F.S.k) =
        toM F.S.m (2 ^ (64 * F.S.k)) (wordsVal s.mem base P.base F.S.k) ^ e := by
  have S₀ : CSt P F.S.k base s s := ⟨hs, Kc.refl _, Unch.refl _ _ _⟩
  have hsh := hL.short
  have := hL.k1
  have := hL.tbl
  rw [chainPow]
  refine WP.seq (WP.mono (table_ok hF hL hm hone hone' hO S₀) fun s₁ ⟨S₁, T₁⟩ => ?_)
  have hi : (P.first - 1) / 2 < 8 := by have := hC.first; omega
  have hle := slotR_le hL (i := (P.first - 1) / 2) (by omega)
  rw [hL.n]
  refine WP.seq (WP.mono (copy_ok F.S.k S₁.ws (o := P.acc) (a := P.slot ((P.first - 1) / 2)) hL.acc8
    (slotR_mod8 hL _) (by omega) (by omega) (by have := hL.acc_tbl; omega)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  have S₂ := S₁.copy (Or.inl rfl) k₂ O₂
  have T₂ : TblR P F.S.k base F.S.m (bvR P F.S.k base F.S.m s) 8 s₂ :=
    T₁.acc hL (Nat.le_refl _) (O₂.unch.mono fun w hw => by simp at hw; simp [hw])
  have Ti := T₁.1 _ hi
  refine WP.mono (stepsR_ok hF hL hm P.steps hC.steps S₂ T₂ (by rw [e₂]; exact Ti.1)
    (v := P.first) (by rw [e₂, Ti.2]; congr 1; have := hC.first; omega)) fun s₃ ⟨S₃, lt₃, v₃⟩ =>
    ⟨S₃.keep, S₃.unch, lt₃, by rw [v₃, hC.val]⟩

end chain

end VG.Proof.Weierstrass.RISCV64
