module

public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEight
public import VerifiedGarbage.Proof.Ed25519.Word64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Bignum.Square
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcMath
public import VerifiedGarbage.Proof.Bignum.AArch64.SquareMath
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightBound
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightLoad

/-! ### `Bignum.AArch64.SquareEightTriRow`, which only this module used -/

section

/-! ### `Bignum.AArch64.SquareEightTriChain`, which only this module used -/

section

/-! ### `Bignum.AArch64.SquareEightTriStep`, which only this module used -/

section

/-! # The row-wise triangle of an eight-limb square: one product and its addition -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64.SquareEight

/-- The low (`hi = false`) or high half of a product of two words. -/
def half (hi : Bool) (a b : Word) : Word :=
  if hi then BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64) else a * b

/-- The product instruction of a half, into the temporary. -/
def prod (hi : Bool) (x y : Reg) : Instr :=
  if hi then .umulh tmp x y else .mul .x tmp x y

theorem half_value (a b : Word) :
    (half false a b).toNat + 2 ^ 64 * (half true a b).toNat = a.toNat * b.toNat := by
  simp only [half, Bool.false_eq_true, ↓reduceIte]
  exact mul_toNat _ _

theorem prod_adcs_ok (s : State) (hi : Bool) (r src x y : Reg) (hr : r ≠ tmp) (hs : src ≠ tmp) :
    WP isa (.block [prod hi x y, .adcs .x r src tmp]) s fun t =>
      (t.gpr r = addCarry (s.gpr src) (half hi (s.gpr x) (s.gpr y)) s.c ∧
        t.c = carryOut (s.gpr src) (half hi (s.gpr x) (s.gpr y)) s.c ∧ t.mem = s.mem) ∧
      Keep [tmp, r] s t := by
  cases hi
  all_goals
    refine WP.keep [tmp, r] ?_ (by simp [prod, writesOnly, Code.allInstrs, dsts, dstOf, Option.toList])
      rfl rfl
    simp only [tmp] at hr hs
    brun [prod, tmp, hr, hs, half]
    refine ⟨?_, rfl⟩
    simp only [addCarry, off, BitVec.ofNat_add, BitVec.add_assoc]

theorem prod_adds_ok (s : State) (hi : Bool) (r src x y : Reg) (hr : r ≠ tmp) (hs : src ≠ tmp) :
    WP isa (.block [prod hi x y, .adds .x r src tmp]) s fun t =>
      (t.gpr r = addCarry (s.gpr src) (half hi (s.gpr x) (s.gpr y)) false ∧
        t.c = carryOut (s.gpr src) (half hi (s.gpr x) (s.gpr y)) false ∧ t.mem = s.mem) ∧
      Keep [tmp, r] s t := by
  cases hi
  all_goals
    refine WP.keep [tmp, r] ?_ (by simp [prod, writesOnly, Code.allInstrs, dsts, dstOf, Option.toList])
      rfl rfl
    simp only [tmp] at hr hs
    brun [prod, tmp, hr, hs, half]
    refine ⟨?_, rfl⟩
    simp only [addCarry, off, BitVec.ofNat_add, BitVec.add_assoc]

end VG.Proof.Bignum.AArch64.SquareEight

end

end


/-! # The row-wise triangle of an eight-limb square: a carry chain of products

`n` steps `R i := R i + half(x · Y i) + c`, each forming its product in the
temporary just before its addition, add the halves' number to the
registers' number, with the carry in and out. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64.SquareEight

/-- The number in the registers `R 0, …, R (n - 1)`, least significant first. -/
def regVal (s : State) (R : Nat → Reg) (n : Nat) : Nat :=
  Square.value (2 ^ 64) (fun i => (s.gpr (R i)).toNat) n

/-- The number of the halves of `x · Y 0, …, x · Y (n - 1)`. -/
def halfVal (s : State) (hi : Bool) (x : Reg) (Y : Nat → Reg) (n : Nat) : Nat :=
  Square.value (2 ^ 64) (fun i => (half hi (s.gpr x) (s.gpr (Y i))).toNat) n

/-- The carry out of a chain of `n` steps: none of an empty one. -/
def carryOf (n : Nat) (s : State) : Nat := if n = 0 then 0 else s.c.toNat

/-- The registers a chain writes, with the temporary. -/
abbrev work : List Reg := tmp :: accs

theorem regVal_congr {s t : State} {R : Nat → Reg} {n : Nat}
    (h : ∀ i < n, t.gpr (R i) = s.gpr (R i)) : regVal t R n = regVal s R n :=
  BlockedRedc.value_congr fun i hi => congrArg BitVec.toNat (h i hi)

theorem halfVal_congr {s t : State} {hi : Bool} {x : Reg} {Y : Nat → Reg} {n : Nat}
    (hx : t.gpr x = s.gpr x) (h : ∀ i < n, t.gpr (Y i) = s.gpr (Y i)) :
    halfVal t hi x Y n = halfVal s hi x Y n :=
  BlockedRedc.value_congr fun i hi => by rw [hx, h i hi]

theorem prod_eq (hi : Bool) (x y : Reg) :
    (if hi then Instr.umulh tmp x y else Instr.mul .x tmp x y) = prod hi x y := rfl

private theorem chain_arith {V V' H C C' S R' h P s' : Nat}
    (ih : V + P * C = S + H) (hr : R' + 2 ^ 64 * C' = s' + h + C)
    (hv : V' = V + R' * P) : V' + P * 2 ^ 64 * C' = S + s' * P + (H + h * P) := by
  subst hv; grind

theorem chain_ok (hi : Bool) (x : Reg) (Y R S : Nat → Reg) (n : Nat) (s : State)
    (hw : ∀ i < n, R i ∈ accs) (hx : x ∉ work) (hY : ∀ k < n, Y k ∉ work)
    (hRR : ∀ i < n, ∀ k < n, R i = R k → i = k)
    (hS : ∀ i < n, S i ≠ tmp ∧ ∀ k < i, R k ≠ S i) :
    WP isa (.block (VG.Impl.Bignum.AArch64.SquareEight.chain hi x Y R S n)) s fun t =>
      (regVal t R n + 2 ^ (64 * n) * carryOf n t = regVal s S n + halfVal s hi x Y n ∧
        (∀ r, r ≠ tmp → (∀ i < n, R i ≠ r) → t.gpr r = s.gpr r) ∧ t.mem = s.mem) ∧
      Keep work s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨⟨by simp [regVal, halfVal, carryOf, Square.value], fun _ _ _ => rfl, rfl⟩,
      Keep.refl _ _⟩
  | succ n ih =>
    have hRt : R n ≠ tmp := fun h => by
      have := hw n (by omega_using []); rw [h] at this; exact absurd this (by decide)
    simp only [VG.Impl.Bignum.AArch64.SquareEight.chain, List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, prod_eq]
    apply WP.block_append
    refine WP.mono (ih s (fun i h => hw i (by omega_using [h])) (fun k h => hY k (by omega_using [h]))
      (fun i h k h' => hRR i (by omega_using [h]) k (by omega_using [h'])) (fun i h => hS i (by omega_using [h])))
      fun a ⟨⟨ha, hak, ham⟩, ka⟩ => ?_
    have hSn : a.gpr (S n) = s.gpr (S n) :=
      hak _ (hS n (by omega_using [])).1 fun i hi => (hS n (by omega_using [])).2 i hi
    have hxa : a.gpr x = s.gpr x := ka.gpr x hx
    have hYa : a.gpr (Y n) = s.gpr (Y n) := ka.gpr _ (hY n (by omega_using []))
    have hStep : WP isa (.block [prod hi x (Y n), (if n = 0 then Instr.adds else Instr.adcs) .x (R n) (S n) tmp]) a
        fun t => (t.gpr (R n) = addCarry (a.gpr (S n)) (half hi (a.gpr x) (a.gpr (Y n)))
            (if n = 0 then false else a.c) ∧
          t.c = carryOut (a.gpr (S n)) (half hi (a.gpr x) (a.gpr (Y n))) (if n = 0 then false else a.c) ∧
          t.mem = a.mem) ∧ Keep [tmp, R n] a t := by
      by_cases h0 : n = 0
      · simp only [h0, ↓reduceIte]
        exact prod_adds_ok a hi (R 0) (S 0) x (Y 0) (h0 ▸ hRt) (h0 ▸ (hS n (by omega_using [])).1)
      · simp only [h0, ↓reduceIte]
        exact prod_adcs_ok a hi (R n) (S n) x (Y n) hRt (hS n (by omega_using [])).1
    refine WP.mono hStep fun t ⟨⟨htr, htc, htm⟩, kt⟩ => ?_
    have tKeep : ∀ r, r ≠ tmp → r ≠ R n → t.gpr r = a.gpr r := fun r h1 h2 =>
      kt.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2⟩)
    have hlow : regVal t R n = regVal a R n := regVal_congr fun i hi =>
      tKeep _ (fun h => by have := hw i (by omega_using [hi]); rw [h] at this; exact absurd this (by decide))
        fun h => absurd (hRR i (by omega_using [hi]) n (by omega_using []) h) (by omega_using [hi])
    have hv := addCarry_value (a.gpr (S n)) (half hi (a.gpr x) (a.gpr (Y n))) (if n = 0 then false else a.c)
    rw [← htr, ← htc, hSn, hxa, hYa] at hv
    have hcin : (if n = 0 then false else a.c).toNat = carryOf n a := by
      by_cases h0 : n = 0 <;> simp [h0, carryOf]
    rw [hcin] at hv
    refine ⟨⟨?_, ?_, htm.trans ham⟩, (ka.trans kt).mono ?_⟩
    · have e1 : regVal t R (n + 1) = regVal t R n + (t.gpr (R n)).toNat * (2 ^ 64) ^ n := rfl
      have e2 : regVal s S (n + 1) = regVal s S n + (s.gpr (S n)).toNat * (2 ^ 64) ^ n := rfl
      have e3 : halfVal s hi x Y (n + 1) = halfVal s hi x Y n +
          (half hi (s.gpr x) (s.gpr (Y n))).toNat * (2 ^ 64) ^ n := rfl
      have e4 : carryOf (n + 1) t = t.c.toNat := rfl
      rw [e1, e2, e3, e4, hlow, show 2 ^ (64 * (n + 1)) = (2 ^ 64) ^ n * 2 ^ 64 by
        rw [Nat.mul_succ, Nat.pow_add, Nat.pow_mul]]
      rw [show 2 ^ (64 * n) = (2 ^ 64) ^ n by rw [Nat.pow_mul]] at ha
      exact chain_arith ha hv rfl
    · intro r h1 h2
      exact (tKeep r h1 (fun h => h2 n (by omega_using []) h.symm)).trans
        (hak r h1 fun i hi => h2 i (by omega_using [hi]))
    · intro r hr
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h
      · exact h
      · exact Or.inl h
      · exact Or.inr (h ▸ hw n (by omega_using []))

end VG.Proof.Bignum.AArch64.SquareEight

end

end


/-! # The row-wise triangle of an eight-limb square: a row

Row `j` (`1 ≤ j ≤ 7`) adds `a_j (a_0 + … + a_{j-1} 2^(64(j-1)))` to the
words `j … 2j - 2` held in the accumulators (`win`), leaving the words
`j … 2j`, and stores word `j`. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.SquareEight

/-- The `n` words from word `j` held in the accumulators. -/
def win (s : State) (j n : Nat) : Nat := regVal s (fun i => acc (j + i)) n

theorem acc_mem (k : Nat) : acc k ∈ accs := by
  have h : ∀ i < 8, accs[i]! ∈ accs := by decide
  exact h _ (Nat.mod_lt _ (by decide))

theorem acc_inj {k k' : Nat} (h : acc k = acc k') (h1 : k ≤ k') (h2 : k' < k + 8) : k = k' := by
  have hd : ∀ a < 8, ∀ b < 8, accs[a]! = accs[b]! → a = b := by decide
  have := hd _ (Nat.mod_lt k (by decide)) _ (Nat.mod_lt k' (by decide)) h
  omega_arith

theorem acc_ne_tmp (k : Nat) : acc k ≠ tmp := fun h => by
  have := acc_mem k; rw [h] at this; exact absurd this (by decide)

theorem inp_not_work : ∀ i < 8, inp i ∉ work := by decide

theorem x7_not_work : Reg.x7 ∉ work := by decide
theorem x16_not_work : Reg.x16 ∉ work := by decide

theorem value_succ_left (r : Nat) (f : Nat → Nat) (n : Nat) :
    Square.value r f (n + 1) = f 0 + r * Square.value r (fun i => f (i + 1)) n := by
  induction n with
  | zero => simp [Square.value]
  | succ n ih =>
    rw [Square.value, ih, Square.value, Nat.pow_succ]
    grind

theorem halves_value (s : State) (x : Reg) (Y : Nat → Reg) (n : Nat) :
    halfVal s false x Y n + 2 ^ 64 * halfVal s true x Y n = (s.gpr x).toNat * regVal s Y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := half_value (s.gpr x) (s.gpr (Y n))
    simp only [halfVal, regVal, Square.value] at ih h ⊢
    grind

theorem carryWord_ok (s : State) (r : Reg) (h7 : s.gpr .x7 = 0) :
    WP isa (.block [.adc .x r .x7 .x7]) s fun t =>
      (t.gpr r = BitVec.ofNat 64 s.c.toNat ∧ t.mem = s.mem) ∧ Keep [r] s t := by
  refine WP.keep [r] ?_ (by simp [writesOnly, Code.allInstrs, dsts, dstOf, Option.toList]) rfl rfl
  brun [h7]
  simp

theorem storeWord_ok {s : State} {B : Addr} {Z e : Nat} (r : Reg) (j : Nat)
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e) (he : e + 8 * j + 8 ≤ Z) (hj : j < 4096) :
    WP isa (.block [st r .x16 (8 * j)]) s fun t =>
      (t.mem = s.mem.writeW (off B (e + 8 * j)) (s.gpr r)) ∧ Keep [] s t := by
  refine WP.keep [] ?_ rfl rfl rfl
  have ho : 8 * j % 8 = 0 ∧ 8 * j < 32768 := ⟨by omega_arith, by omega_arith⟩
  brun [h16, hs.st he, ho]

theorem regVal_ext {s t : State} {R R' : Nat → Reg} {n : Nat}
    (h : ∀ i < n, s.gpr (R i) = t.gpr (R' i)) : regVal s R n = regVal t R' n :=
  BlockedRedc.value_congr fun i hi => congrArg BitVec.toNat (h i hi)

theorem acc_inj' {a b : Nat} (h : acc a = acc b) (h1 : a < b + 8) (h2 : b < a + 8) : a = b := by
  rcases Nat.le_total a b with hab | hab
  · exact acc_inj h hab (by omega_arith)
  · exact (acc_inj h.symm hab (by omega_arith)).symm

theorem acc_ne_x7 (k : Nat) : acc k ≠ .x7 := fun h => by
  have := acc_mem k; rw [h] at this; exact absurd this (by decide)

theorem win_succ (s : State) (j n : Nat) :
    win s j (n + 1) = win s j n + (s.gpr (acc (j + n))).toNat * (2 ^ 64) ^ n := rfl

/-- A window splits into its first word and the window after it. -/
theorem win_split (s : State) (j n : Nat) :
    win s j (n + 1) = (s.gpr (acc j)).toNat + 2 ^ 64 * win s (j + 1) n := by
  unfold win regVal
  rw [value_succ_left]
  simp only [Nat.add_zero]
  congr 2
  exact BlockedRedc.value_congr fun i _ => by rw [show j + (i + 1) = j + 1 + i by omega_arith]

private theorem row_arith {W L H Vb Vc bj winb winc cc aval P : Nat}
    (h1 : winb = W + L) (h2 : winb = bj + 2 ^ 64 * Vb) (h3 : Vc + P * cc = Vb + H)
    (h4 : winc = bj + 2 ^ 64 * Vc) (h5 : L + 2 ^ 64 * H = aval) (hb : W + aval < 2 ^ 64 * P)
    (hc : cc ≤ 1) : winc = W + aval := by
  rcases (by omega_arith : cc = 0 ∨ cc = 1) with rfl | rfl
  · omega_arith
  · omega_arith

theorem triRow_ok {s : State} {B : Addr} {Z eT j : Nat} (hj1 : 1 ≤ j) (hj7 : j ≤ 7)
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (hT : eT + 8 * j + 8 ≤ Z)
    (h7 : s.gpr .x7 = 0)
    (hb : win s j (j - 1) + (s.gpr (inp j)).toNat * regVal s inp j < 2 ^ (64 * (j + 1))) :
    WP isa (.block (row j)) s fun t =>
      (win t j (j + 1) = win s j (j - 1) + (s.gpr (inp j)).toNat * regVal s inp j ∧
        t.mem = s.mem.writeW (off B (eT + 8 * j)) (t.gpr (acc j))) ∧ Keep work s t := by
  unfold row low high
  rw [List.append_assoc, List.append_assoc]
  apply WP.block_append
  refine WP.mono (chain_ok false (inp j) inp (fun i => acc (j + i))
    (fun i => if i + 1 = j then .x7 else acc (j + i)) j s
    (fun i _ => acc_mem _) (inp_not_work j (by omega_arith)) (fun k _ => inp_not_work k (by omega_arith))
    (fun i _ k _ h => by have := acc_inj' h (by omega_arith) (by omega_arith); omega_arith)
    (fun i hi => ⟨by split <;> [decide; exact acc_ne_tmp _], fun k hk => by
      split
      · exact acc_ne_x7 _
      · exact fun h => by have := acc_inj' h (by omega_arith) (by omega_arith); omega_arith⟩))
    fun a ⟨⟨ha, hak, ham⟩, ka⟩ => ?_
  have h7a : a.gpr .x7 = 0 := (ka.gpr _ x7_not_work).trans h7
  apply WP.block_append
  refine WP.mono (carryWord_ok a (acc (2 * j)) h7a) fun b ⟨⟨hb2, hbm⟩, kb⟩ => ?_
  have kab := ka.trans kb
  have kabw : Keep work s b := kab.mono fun r hr => by
    rcases List.mem_append.mp hr with h | h
    · exact h
    · rw [List.mem_singleton.mp h]; exact List.mem_cons_of_mem _ (acc_mem _)
  -- the low halves, with the carry word
  have hlowS : regVal s (fun i => if i + 1 = j then .x7 else acc (j + i)) j = win s j (j - 1) := by
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega_arith⟩
    have e : regVal s (fun i => if i + 1 = n + 1 then .x7 else acc (n + 1 + i)) (n + 1) =
        regVal s (fun i => if i + 1 = n + 1 then .x7 else acc (n + 1 + i)) n +
          (s.gpr .x7).toNat * (2 ^ 64) ^ n := by
      simp only [regVal, Square.value, ↓reduceIte]
    rw [e, h7, show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero,
      show n + 1 - 1 = n by omega_arith]
    unfold win
    exact regVal_ext fun i hi => by simp only [show ¬ (i + 1 = n + 1) by omega_arith, ↓reduceIte]
  have hj0 : j ≠ 0 := by omega_arith
  have hcA : carryOf j a = a.c.toNat := by simp [carryOf, hj0]
  have hRb : regVal b (fun i => acc (j + i)) j = regVal a (fun i => acc (j + i)) j :=
    regVal_congr fun i hi => kb.gpr _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => by have := acc_inj' h (by omega_arith) (by omega_arith); omega_arith)
  have hwinb : win b j (j + 1) = win s j (j - 1) + halfVal s false (inp j) inp j := by
    have e1 : win b j (j + 1) = regVal a (fun i => acc (j + i)) j + a.c.toNat * (2 ^ 64) ^ j := by
      rw [win_succ, show j + j = 2 * j by omega_arith, hb2, show (BitVec.ofNat 64 a.c.toNat).toNat = a.c.toNat by
        cases a.c <;> rfl]
      unfold win
      rw [hRb]
    rw [e1, ← hlowS, ← ha, hcA, Nat.pow_mul, Nat.mul_comm (a.c.toNat)]
  -- the high halves
  apply WP.block_append
  refine WP.mono (chain_ok true (inp j) inp (fun i => acc (j + 1 + i)) (fun i => acc (j + 1 + i)) j b
    (fun i _ => acc_mem _) (inp_not_work j (by omega_arith)) (fun k _ => inp_not_work k (by omega_arith))
    (fun i _ k _ h => by have := acc_inj' h (by omega_arith) (by omega_arith); omega_arith)
    (fun i hi => ⟨acc_ne_tmp _, fun k hk h => by have := acc_inj' h (by omega_arith) (by omega_arith); omega_arith⟩))
    fun c ⟨⟨hc, hck, hcm⟩, kc⟩ => ?_
  have hcj : c.gpr (acc j) = b.gpr (acc j) :=
    hck _ (acc_ne_tmp _) fun i _ h => by have := acc_inj' h (by omega_arith) (by omega_arith); omega_arith
  have hin : ∀ i < 8, b.gpr (inp i) = s.gpr (inp i) := fun i hi => kabw.gpr _ (inp_not_work i hi)
  have hhalf : halfVal b true (inp j) inp j = halfVal s true (inp j) inp j :=
    halfVal_congr (hin j (by omega_arith)) fun i hi => hin i (by omega_arith)
  have h16c : c.gpr .x16 = off B eT :=
    (kc.gpr _ x16_not_work).trans ((kabw.gpr _ x16_not_work).trans h16)
  refine WP.mono (storeWord_ok (c.gpr (acc j) |> fun _ => acc j) j (hs.congr (kc.wr.trans kabw.wr))
    h16c hT (by omega_arith)) fun t ⟨htm, kt⟩ => ?_
  have hcc : c.c.toNat ≤ 1 := by cases c.c <;> decide
  have hcarry : carryOf j c = c.c.toNat := by simp [carryOf, hj0]
  have hwt : win t j (j + 1) = win c j (j + 1) := regVal_congr fun i _ => kt.gpr _ (by simp)
  refine ⟨⟨?_, ?_⟩, ((kabw.trans kc).trans kt).mono fun r hr => ?_⟩
  rotate_left 2
  · rcases List.mem_append.mp hr with h | h
    · rcases List.mem_append.mp h with h | h <;> exact h
    · exact absurd h List.not_mem_nil
  · rw [hwt]
    have h2 := win_split b j j
    have h4 := win_split c j j
    rw [hcj] at h4
    have h5 := halves_value s (inp j) inp j
    rw [hhalf, hcarry] at hc
    unfold win at h2 h4
    rw [show 2 ^ (64 * (j + 1)) = 2 ^ 64 * 2 ^ (64 * j) by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]] at hb
    exact row_arith hwinb (by unfold win at hwinb ⊢; exact h2) hc h4 h5 hb hcc
  · rw [htm, hcm, hbm, ham, kt.gpr _ (by simp)]

end VG.Proof.Bignum.AArch64.SquareEight

end

end


/-! # The row-wise triangle of an eight-limb square

The cross products `Σ_{i<j<8} a_i a_j 2^(64(i+j))` of eight words at
`x8`, written as fifteen words at `x16` (word 0, zero before, is not
written): rows 1 to 7 (`triRow_ok`), each storing its first word, then the
accumulators' words 8 to 14. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.SquareEight
open VG.Proof.MlKem.AArch64 (Keep)

abbrev codeRegs : List Reg := inputs ++ work

/-- After the rows before row `j`: the words `0 … j - 1` in memory and the
words `j … 2j - 2` in the accumulators make the cross products of the first
`j` inputs. -/
def TriInv (m0 : Mem) (B : Addr) (eA eT : Nat) (s0 : State) (j : Nat) (t : State) : Prop :=
  wv t.mem B eT j + 2 ^ (64 * j) * win t j (j - 1) = Square.crossValue m0 B eA j ∧
  Outside B (eT + 8) (8 * (j - 1)) s0.mem t.mem ∧ Keep work s0 t

theorem triRows_ok {s0 : State} {B : Addr} {Z eA eT : Nat} (n : Nat) (hn : n ≤ 7)
    (hs : Scr s0 B Z) (h16 : s0.gpr .x16 = off B eT) (hT : eT + 120 ≤ Z) (h7 : s0.gpr .x7 = 0)
    (hin : ∀ i < 8, s0.gpr (inp i) = word s0.mem B (eA + 8 * i))
    (hz : wv s0.mem B eT 1 = 0) :
    WP isa (.block ((List.range n).flatMap fun j => row (j + 1))) s0 (TriInv s0.mem B eA eT s0 (n + 1)) := by
  induction n with
  | zero =>
    refine WP.block_nil ⟨?_, Outside.refl _ _ _ _, Keep.refl _ _⟩
    simp only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, Nat.add_zero, win, regVal, Square.value]
    rw [hz]
    simp [Square.crossValue, Square.cross, Square.value]
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine WP.mono (ih (by omega_arith)) fun t ⟨hv, ho, kt⟩ => ?_
    have hn1 : n + 1 - 1 = n := by omega_arith
    have hin' : ∀ i < 8, t.gpr (inp i) = word s0.mem B (eA + 8 * i) :=
      fun i hi => (kt.gpr _ (inp_not_work i hi)).trans (hin i hi)
    have hval : regVal t inp (n + 1) = wv s0.mem B eA (n + 1) :=
      inputs_value (s := t) (fun i hi => hin' i (by omega_arith))
    have haj : t.gpr (inp (n + 1)) = word s0.mem B (eA + 8 * (n + 1)) := hin' _ (by omega_arith)
    have hcross := Square.crossValue_succ s0.mem B eA (n + 1)
    have hlt := cross_words_succ_lt s0.mem B eA (n + 1)
    rw [hn1] at hv
    have hb : win t (n + 1) n + (t.gpr (inp (n + 1))).toNat * regVal t inp (n + 1) <
        2 ^ (64 * (n + 1 + 1)) := by
      rw [hval, haj]
      have e : wv t.mem B eT (n + 1) + 2 ^ (64 * (n + 1)) *
          (win t (n + 1) n + (word s0.mem B (eA + 8 * (n + 1))).toNat * wv s0.mem B eA (n + 1)) =
          Square.crossValue s0.mem B eA (n + 1 + 1) := by
        rw [hcross, ← hv, Nat.mul_add]; grind
      have hp : 2 ^ (64 * (2 * (n + 1) + 1)) = 2 ^ (64 * (n + 1)) * 2 ^ (64 * (n + 1 + 1)) := by
        rw [← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega_arith)
      rw [hp] at hlt
      exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (e ▸ hlt))
    refine WP.mono (triRow_ok (j := n + 1) (by omega_arith) (by omega_arith) (hs.congr kt.wr)
      ((kt.gpr _ x16_not_work).trans h16) (by omega_arith) ((kt.gpr _ x7_not_work).trans h7)
      (by rw [hn1]; exact hb)) fun u ⟨⟨hu, hum⟩, ku⟩ => ?_
    rw [hn1] at hu
    have hnw : (eT + 8 * (n + 1)) + 8 ≤ 2 ^ 64 := by have := hs.nowrap; omega_arith
    refine ⟨?_, ?_, kt.trans ku |>.mono fun r hr => by
      rcases List.mem_append.mp hr with h | h <;> exact h⟩
    · have hw := wv_writeW_top t.mem B eT (n + 1) (u.gpr (acc (n + 1))) (by omega_arith)
      rw [hum, show n + 1 + 1 - 1 = n + 1 by omega_arith, hw]
      have hs2 := win_split u (n + 1) (n + 1)
      rw [hu] at hs2
      rw [hval, haj] at hs2
      rw [hcross, ← hv]
      rw [show 2 ^ (64 * (n + 1 + 1)) = 2 ^ (64 * (n + 1)) * 2 ^ 64 by
        rw [← Nat.pow_add, Nat.mul_succ]]
      grind
    · rw [hum]
      have hw := writeW_outside t.mem B (u.gpr (acc (n + 1))) (d := eT + 8 * (n + 1)) hnw
      exact (ho.mono (by omega_arith) (by omega_arith)).trans (hw.mono (by omega_arith) (by omega_arith))

/-- The accumulators' words `w … w + k - 1` stored after the words before
them (`w = 8`; a variable, so that no tactic evaluates `2 ^ (64 * 8)`). -/
theorem stores_ok {s : State} {B : Addr} {Z eT w : Nat} (hw : w = 8) (k : Nat) (hk : k ≤ 7)
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (hT : eT + 120 ≤ Z) :
    WP isa (.block ((List.range k).map fun i => st (acc (i + 8)) .x16 (8 * (i + 8)))) s fun t =>
      (wv t.mem B eT (w + k) = wv s.mem B eT w + 2 ^ (64 * w) * win s w k ∧
        Outside B (eT + 8 * w) (8 * k) s.mem t.mem) ∧ Keep [] s t := by
  induction k with
  | zero =>
    refine WP.block_nil ⟨⟨?_, Outside.refl _ _ _ _⟩, Keep.refl _ _⟩
    rw [show win s w 0 = 0 from rfl, Nat.mul_zero, Nat.add_zero, Nat.add_zero]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    apply WP.block_append
    refine WP.mono (ih (by omega_arith)) fun t ⟨⟨hv, ho⟩, kt⟩ => ?_
    refine WP.mono (storeWord_ok (acc (k + 8)) (k + 8) (hs.congr kt.wr) ((kt.gpr _ (by simp)).trans h16)
      (by omega_arith) (by omega_arith)) fun u ⟨hum, ku⟩ => ?_
    have hnw : (eT + 8 * (k + 8)) + 8 ≤ 2 ^ 64 := by have := hs.nowrap; omega_arith
    refine ⟨⟨?_, ?_⟩, (kt.trans ku).mono (by simp)⟩
    · have hwt := wv_writeW_top t.mem B eT (w + k) (t.gpr (acc (k + 8))) (by omega_arith)
      rw [hum, show eT + 8 * (k + 8) = eT + 8 * (w + k) by omega_arith, show w + (k + 1) = w + k + 1 by omega_arith,
        hwt, hv, win_succ, kt.gpr _ (by simp), show w + k = k + 8 by omega_arith, Nat.mul_add 64 k 8,
        ← hw, Nat.pow_add, ← Nat.pow_mul]
      generalize 2 ^ (64 * w) = P
      generalize 2 ^ (64 * k) = Q
      grind
    · rw [hum]
      have hwo := writeW_outside t.mem B (t.gpr (acc (k + 8))) (d := eT + 8 * (k + 8)) hnw
      exact (ho.mono (by omega_arith) (by omega_arith)).trans (hwo.mono (by omega_arith) (by omega_arith))

/-- The scheduled eight-limb triangular product, including input loads,
every carry, and the final output words. -/
theorem code_ok {s : State} {B : Addr} {Z eA eT : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eA) (h16 : s.gpr .x16 = off B eT)
    (hA : eA + 64 ≤ Z) (hT : eT + 120 ≤ Z) (h7 : s.gpr .x7 = 0)
    (hz : wv s.mem B eT 1 = 0) :
    WP isa (.block code) s fun t =>
      wv t.mem B eT 15 = Square.crossValue s.mem B eA 8 ∧
        Outside B (eT + 8) 112 s.mem t.mem ∧ Keep codeRegs s t := by
  unfold code
  rw [List.append_assoc]
  apply WP.block_append
  refine WP.mono (loadInputs_ok hs h8 hA) fun a ⟨⟨hai, ham⟩, ka⟩ => ?_
  have h16a : a.gpr .x16 = off B eT := (ka.gpr _ (by decide)).trans h16
  have h7a : a.gpr .x7 = 0 := (ka.gpr _ (by decide)).trans h7
  apply WP.block_append
  refine WP.mono (triRows_ok (eA := eA) 7 (Nat.le_refl _) (hs.congr ka.wr) h16a hT h7a
    (fun i hi => (hai i hi).trans (by rw [ham])) (by rw [ham]; exact hz)) fun b ⟨hbv, hbo, kb⟩ => ?_
  refine WP.mono (stores_ok (w := 8) rfl 7 (Nat.le_refl _) (hs.congr (kb.wr.trans ka.wr))
    ((kb.gpr _ x16_not_work).trans h16a) hT) fun t ⟨⟨htv, hto⟩, kt⟩ => ?_
  refine ⟨?_, ?_, ((ka.trans kb).trans kt).mono fun r hr => by rwa [List.append_nil] at hr⟩
  · rw [htv]
    rw [ham, show (7 : Nat) + 1 - 1 = 7 from rfl, show (7 : Nat) + 1 = 8 from rfl] at hbv
    exact hbv
  · rw [← ham]
    exact (hbo.mono (by omega_arith) (by omega_arith)).trans (hto.mono (by omega_arith) (by omega_arith))

end VG.Proof.Bignum.AArch64.SquareEight
