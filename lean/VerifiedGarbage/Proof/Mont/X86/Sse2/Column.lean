module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Dot
public import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.X86.ArgFar
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Mont.X86.Sse2.Fold`, which only this module used -/

section

/-! ### `Mont.X86.Sse2.Input`, which only this module used -/

section

/-! ### `Mont.X86.Sse2.Products`, which only this module used -/

section

/-! # A column's products as coefficients

`dot` sums the products of the words at the same index of two numbers
(`dsum`). One of the two is a number stored in reverse (`A'` and the
quotient digits `Q'`), so the sum is a column's `Σ f_i g_(k-i)` over a range
of `i` (`dsum_rev`, `csum`), which is the column's coefficient of a product
(`csum_product`), of a square's products above the diagonal (`csum_cross`),
and of the quotient digits written so far times the modulus
(`csum_reduce`). Each sum is `2³²` times the sum of the products' high words
plus that of their low words (`dsum_split`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.NatSum

/-- The words of a number at offset `x` of the working space. -/
def digits (m : Mem) (W : Addr) (x : Nat) (i : Nat) : Nat := w32 m W (x + 4 * i)

/-- `Σ f_i g_(k-i)` for `i0 ≤ i < i0 + n`. -/
def csum (f g : Nat → Nat) (k i0 n : Nat) : Nat := sum (fun j => f (i0 + j) * g (k - (i0 + j))) n

theorem rsum_eq_sum (f : Nat → Nat) (a n : Nat) : rsum f a n = sum (fun j => f (a + j)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rsum, NatSum.succ, ih]

theorem sum_shift (g : Nat → Nat) (n : Nat) : sum g (n + 1) = g 0 + sum (fun j => g (j + 1)) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [NatSum.succ, ih, NatSum.succ]; omega_using []

theorem sum_rev (f : Nat → Nat) (n : Nat) : sum f n = sum (fun j => f (n - 1 - j)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [NatSum.succ, ih, sum_shift]
    rw [show (n + 1 - 1 - 0) = n by omega_using [], Nat.add_comm]
    congr 1
    apply NatSum.congr
    intro j hj
    congr 1; omega_using []

/-- A sum of products of two numbers, one stored in reverse: the word `N - 1 - i`
of `xp` is `f_i` for `i0 ≤ i < e`. -/
theorem dsum_rev (m : Mem) (W : Addr) (xp y : Nat) (f : Nat → Nat) {N k e i0 : Nat} (he : e ≤ N)
    (hek : e ≤ k + 1) (hi : i0 ≤ e) (hf : ∀ i, i0 ≤ i → i < e → w32 m W (xp + 4 * (N - 1 - i)) = f i) :
    dsum m W (xp + 4 * (N - e)) (y + 4 * (k + 1 - e)) (e - i0) = csum f (digits m W y) k i0 (e - i0) := by
  rw [dsum, rsum_eq_sum, sum_rev, csum]
  apply NatSum.congr
  intro j hj
  simp only [Nat.zero_add, dprod, digits]
  rw [show xp + 4 * (N - e) + 4 * (e - i0 - 1 - j) = xp + 4 * (N - 1 - (i0 + j)) by omega,
    show y + 4 * (k + 1 - e) + 4 * (e - i0 - 1 - j) = y + 4 * (k - (i0 + j)) by omega_using [hek, hj],
    hf (i0 + j) (by omega_using []) (by omega_using [hj])]

theorem csum_product (f g : Nat → Nat) {N k : Nat} :
    csum f g k (k + 1 - N) (min (k + 1) N - (k + 1 - N)) = Column.coeff f g N k := by
  rw [csum, Column.coeff_range, ← interval (fun i => f i * g (k - i)) N (k + 1 - N)
    (min (k + 1) N) (Nat.min_le_right _ _)]
  apply NatSum.congr
  intro i hi
  obtain e : (i ≤ k ∧ k - i < N) ↔ (k + 1 - N ≤ i ∧ i < min (k + 1) N) := by omega_using [hi]
  simp only [e]

theorem csum_cross (f : Nat → Nat) {N k : Nat} (hk : k < 2 * N) :
    csum f f k (k + 1 - N) ((k + 1) / 2 - (k + 1 - N)) = Column.crossCoeff f N k := by
  rw [csum, Column.crossCoeff_scan _ hk]

theorem csum_reduce (q g : Nat → Nat) {N k : Nat} :
    csum q g k (k + 1 - N) (min k N - (k + 1 - N)) = Column.coeff (Column.prefixDigits q k) g N k := by
  rw [csum, Column.coeff_prefix_scan]

/-- The last two terms of a column's sum from `0`. -/
theorem csum_two (q g : Nat → Nat) {k : Nat} (hk : 2 ≤ k) :
    csum q g k 0 k = csum q g k 0 (k - 2) + q (k - 2) * g 2 + q (k - 1) * g 1 := by
  rw [show k = (k - 2) + 1 + 1 by omega_using [hk]]
  simp only [csum, NatSum.succ, Nat.zero_add]
  rw [show k - 2 + 1 + 1 - 2 = k - 2 by omega_using [], show k - 2 + 1 + 1 - (k - 2) = 2 by omega_using [],
    show k - 2 + 1 + 1 - (k - 2 + 1) = 1 by omega_using [], show k - 2 + 1 = k - 2 + 1 from rfl]
  rw [show k - 2 + 1 + 1 - 1 = k - 2 + 1 by omega_using []]

theorem csum_reduce0 (q g : Nat → Nat) {N k : Nat} (hk : k < N) :
    csum q g k 0 k = Column.coeff (Column.prefixDigits q k) g N k := by
  have := csum_reduce q g (N := N) (k := k)
  rwa [show k + 1 - N = 0 by omega_using [hk], show min k N - 0 = k by omega_using [hk]] at this

/-- The products' low words. -/
def dlow (m : Mem) (W : Addr) (x y n : Nat) : Nat := rsum (fun j => dprod m W x y j % 2 ^ 32) 0 n

theorem dsum_split (m : Mem) (W : Addr) (x y n : Nat) :
    dsum m W x y n = 2 ^ 32 * dhigh m W x y n + dlow m W x y n ∧ dlow m W x y n ≤ n * (2 ^ 32 - 1) := by
  induction n with
  | zero => exact ⟨rfl, Nat.le_refl _⟩
  | succ n ih =>
    have := Nat.div_add_mod (dprod m W x y n) (2 ^ 32)
    have := Nat.mod_lt (dprod m W x y n) (show 0 < 2 ^ 32 by decide)
    simp only [dsum, dhigh, dlow, rsum, Nat.zero_add] at ih ⊢
    rw [Nat.succ_mul]
    constructor <;> omega_using [ih]

end VG.Proof.Mont.X86.Sse2

end

end

/-! # A column's sums

`Acc`: the lanes hold a column's sum `P` modulo `2⁶⁴` and the sum `H` of
its products' high words, with `P - 2³² H` the sum of at most `n` low words.
`dot` adds its products (`Acc.dot`); a square's sum is doubled
(`Acc.double`) and gets the diagonal's product (`Acc.single`).

`input sq hi` adds the column's products of `A` and `B` (`input_ok`), and
`reduce hi` those of the quotient digits and `M` (`reduce_ok`), from `A'`
and the digits stored in reverse (`RevA`, `RevQ`) and, while `k < N`, the two
latest digits in `xmm6` (`Window`).
-/

-- Formerly `VerifiedGarbage/Proof/Mont/X86/Sse2/Index.lean`, which only this module imported.
section

/-! # The parameters

The kernel's seven parameters are words on the stack, `d` bytes above `esp`
(`Params`), past the working space, so changes within it keep them; `Sk`
records what a step keeps.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Mont.X86.Dynamic (ArgFar readSrc_keep readSrc_upd)

/-- The parameters `V i` at `[esp + d + 4 i]`, past the working space. -/
structure Params (s : State) (W : Addr) (L : Nat) (V : Nat → BitVec 32) (d : Nat) : Prop where
  read : ∀ i < 7, readSrc s (.mem (prm d i)) = some (V i)
  far : ∀ i < 7, ArgFar s W L (prm d i)

/-- Changes within the working space, with `esp` and the permissions as they
were, keep the parameters. -/
theorem Params.keep {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d : Nat} (h : Params s W L V d)
    (O : Outs W [(0, L)] s.mem t.mem) (hsp : t.gpr .esp = s.gpr .esp) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) : Params t W L V d :=
  ⟨fun i hi => (readSrc_keep (h.far i hi) O (by simp) hsp hrd hwr).trans (h.read i hi),
    fun i hi => (h.far i hi).keep hsp⟩

/-- What scalar code leaves: the registers but `rs`, the memory, the MCDT
depth and the XMM registers. -/
structure Sk (rs : List Reg) (s t : State) : Prop where
  keep : Keeps rs s t
  mem : t.mem = s.mem
  mcdt : t.mcdt = s.mcdt
  xmm : t.xmm = s.xmm

theorem Sk.refl (rs : List Reg) (s : State) : Sk rs s s := ⟨Keeps.refl _ _, rfl, rfl, rfl⟩

theorem Sk.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Sk rs' s₁ s₂) (h₂ : Sk rs s₂ s₃)
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : Sk rs' s₁ s₃ :=
  ⟨h₁.keep.widen h₂.keep hs, h₂.mem.trans h₁.mem, h₂.mcdt.trans h₁.mcdt, h₂.xmm.trans h₁.xmm⟩

theorem Sk.mono {rs : List Reg} {s t : State} (h : Sk rs s t) (rs' : List Reg)
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : Sk rs' s t :=
  ⟨h.keep.mono hs, h.mem, h.mcdt, h.xmm⟩

theorem Sk.of_upd (rs : List Reg) {s t : State} {d : Reg} {v : BitVec 32} (u : Upd s t d v)
    (hm : t.mcdt = s.mcdt) (hx : t.xmm = s.xmm) (hd : d ∈ rs := by decide) : Sk rs s t :=
  ⟨u.keeps.mono fun r hr => by simp only [List.mem_singleton] at hr; exact hr ▸ hd, u.mem, hm, hx⟩

theorem Sk.of_fupd {s t : State} (u : Fupd s t) (hm : t.mcdt = s.mcdt) (hx : t.xmm = s.xmm) (rs : List Reg) :
    Sk rs s t := ⟨u.keeps rs, u.mem, hm, hx⟩

theorem Params.of_sk {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d : Nat} (h : Params s W L V d)
    {rs : List Reg} (K : Sk rs s t) (hsp : .esp ∉ rs := by decide) : Params t W L V d :=
  h.keep (by rw [K.mem]; exact Outs.refl _ _ _) (K.keep.1 _ hsp) K.keep.2.1 K.keep.2.2

/-- A parameter read in a state `Sk` from one where it is known. -/
theorem Params.readSk {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d : Nat} (h : Params s W L V d)
    {rs : List Reg} (K : Sk rs s t) {i : Nat} (hi : i < 7) (hsp : .esp ∉ rs := by decide) :
    readSrc t (.mem (prm d i)) = some (V i) := (h.of_sk K hsp).read i hi

theorem ofNat_of_toNat {v : BitVec 32} {n : Nat} (h : v.toNat = n) : v = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h ▸ v.isLt)]

end VG.Proof.Mont.X86.Sse2
end

end

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.X86.RegUpd VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt

/-- A column's sums: `P` and the high words' `H`, `P - 2³² H` at most `n` low words. -/
structure Acc (x0 x1 : BitVec 128) (P H n : Nat) : Prop where
  sums : Sums x0 x1 P H
  le : 2 ^ 32 * H ≤ P
  low : P - 2 ^ 32 * H ≤ n * (2 ^ 32 - 1)

theorem Acc.zero {x0 x1 : BitVec 128} : Acc (XBinOp.eval .pxor x0 x0) (XBinOp.eval .pxor x1 x1) 0 0 0 := by
  refine ⟨⟨?_, ?_⟩, Nat.le_refl _, Nat.le_refl _⟩ <;> simp only [pxor_self, qword_zero] <;> rfl

theorem Acc.dot {x0 x1 y0 y1 : BitVec 128} {P H n : Nat} (A : Acc x0 x1 P H n) {m : Mem} {W : Addr}
    {x y c : Nat} (D : Sums y0 y1 (P + dsum m W x y c) (H + dhigh m W x y c)) :
    Acc y0 y1 (P + dsum m W x y c) (H + dhigh m W x y c) (n + c) := by
  obtain ⟨e, l⟩ := dsum_split m W x y c
  have := A.le
  have := A.low
  refine ⟨D, by omega_arith, ?_⟩
  rw [Nat.add_mul]; omega_arith

theorem Acc.of_eq' {x0 x1 : BitVec 128} {P P' H n : Nat} (A : Acc x0 x1 P H n) (h : P = P') :
    Acc x0 x1 P' H n := h ▸ A

theorem toNat_add_self (q : BitVec 64) (h : 2 * q.toNat < 2 ^ 64) : (q + q).toNat = 2 * q.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

theorem Acc.double {x0 x1 : BitVec 128} {P H n : Nat} (A : Acc x0 x1 P H n) (hH : 2 * H < 2 ^ 64) :
    Acc (XBinOp.eval .paddq x0 x0) (XBinOp.eval .paddq x1 x1) (2 * P) (2 * H) (2 * n) := by
  have hh := A.sums.high
  have := A.le
  have := A.low
  refine ⟨⟨?_, ?_⟩, by omega_arith, ?_⟩
  · rw [qword_paddq _ _ (by decide), qword_paddq _ _ (by decide),
      show qword x0 0 + qword x0 0 + (qword x0 1 + qword x0 1) = (qword x0 0 + qword x0 1) +
        (qword x0 0 + qword x0 1) by ac_rfl, A.sums.low, ← BitVec.ofNat_add, Nat.two_mul]
  · rw [qword_paddq _ _ (by decide), qword_paddq _ _ (by decide), toNat_add_self _ (by omega_arith),
      toNat_add_self _ (by omega_arith)]
    omega_arith
  · rw [Nat.mul_assoc 2 n]; omega_arith

theorem Acc.single {x0 x1 : BitVec 128} {P H n : Nat} (A : Acc x0 x1 P H n) {u v : BitVec 32}
    (hH : H + 2 ^ 32 < 2 ^ 64) :
    Acc (XBinOp.eval .paddq x0 (singleP u v)) (XBinOp.eval .paddq x1 (XShiftOp.eval .psrlq (singleP u v) 32))
      (P + u.toNat * v.toNat) (H + u.toNat * v.toNat / 2 ^ 32) (n + 1) := by
  obtain hs := A.sums.add (singleP_0 u v) (singleP_1 u v) (word_mul_lt _ _) (by decide) hH
  obtain hd := Nat.div_add_mod (u.toNat * v.toNat) (2 ^ 32)
  obtain hm := Nat.mod_lt (u.toNat * v.toNat) (show 0 < 2 ^ 32 by decide)
  have := A.le
  have := A.low
  refine ⟨by simpa using hs, by omega_arith, ?_⟩
  rw [Nat.succ_mul]; omega_arith

/-- Two products by `pmuludq`, of doublewords 0 and 2. -/
theorem Acc.mul {x0 x1 : BitVec 128} {P H n : Nat} (A : Acc x0 x1 P H n) (u v : BitVec 128)
    (hH : H + 2 * 2 ^ 32 < 2 ^ 64) :
    Acc (XBinOp.eval .paddq x0 (pmuludq u v)) (XBinOp.eval .paddq x1 (XShiftOp.eval .psrlq (pmuludq u v) 32))
      (P + ((dword u 0).toNat * (dword v 0).toNat + (dword u 2).toNat * (dword v 2).toNat))
      (H + ((dword u 0).toNat * (dword v 0).toNat / 2 ^ 32 + (dword u 2).toNat * (dword v 2).toNat / 2 ^ 32))
      (n + 2) := by
  obtain q0 := Nat.div_lt_iff_lt_mul (k := 2 ^ 32) (x := (dword u 0).toNat * (dword v 0).toNat) (y := 2 ^ 32)
    (by decide) |>.2 (by have := word_mul_lt (dword u 0) (dword v 0); omega_arith)
  obtain hs := A.sums.addMul (u := u) (v := v) (by omega_arith)
  obtain d0 := Nat.div_add_mod ((dword u 0).toNat * (dword v 0).toNat) (2 ^ 32)
  obtain m0 := Nat.mod_lt ((dword u 0).toNat * (dword v 0).toNat) (show 0 < 2 ^ 32 by decide)
  obtain d2 := Nat.div_add_mod ((dword u 2).toNat * (dword v 2).toNat) (2 ^ 32)
  obtain m2 := Nat.mod_lt ((dword u 2).toNat * (dword v 2).toNat) (show 0 < 2 ^ 32 by decide)
  have := A.le
  have := A.low
  refine ⟨hs.of_eq (by omega_arith) (by omega_arith), by omega_arith, ?_⟩
  rw [Nat.add_mul]; omega_arith

/-! ## The SSE instructions of the input -/

theorem movdqa_eval (a b : BitVec 128) : XBinOp.eval .movdqa a b = b := rfl

/-- `movd xmm2, eax; pmuludq xmm2, xmm2`, then the product into the sums. -/
theorem sq_run (s : State) (hm : 0 < s.mcdt) :
    ∃ t, runBlock isa (([.xop (.movd .xmm2 .eax), .pmuludq .xmm2 .xmm2] : List Instr) ++ acc .xmm2) s = some t ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mcdt = s.mcdt ∧
      t.xmm .xmm6 = s.xmm .xmm6 ∧
      t.xmm .xmm0 = XBinOp.eval .paddq (s.xmm .xmm0) (singleP (s.gpr .eax) (s.gpr .eax)) ∧
      t.xmm .xmm1 = XBinOp.eval .paddq (s.xmm .xmm1)
        (XShiftOp.eval .psrlq (singleP (s.gpr .eax) (s.gpr .eax)) 32) := by
  simp only [acc, List.cons_append, List.nil_append, runBlock_cons, exec, runStep_some,
    XOp.exec, ↓reduceIte, Option.some.injEq, exists_eq_left', mcdt_setXmm, hm, xmm_setXmm, reduceCtorEq,
    runBlock_nil, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, singleP, and_self]

/-- `paddq xmm0, xmm0; paddq xmm1, xmm1`. -/
theorem double_run (s : State) :
    runBlock isa [.xop (.bin .paddq .xmm0 .xmm0), .xop (.bin .paddq .xmm1 .xmm1)] s =
      some ((s.setXmm .xmm0 (XBinOp.eval .paddq (s.xmm .xmm0) (s.xmm .xmm0))).setXmm .xmm1
        (XBinOp.eval .paddq (s.xmm .xmm1) (s.xmm .xmm1))) := by
  simp only [runBlock_cons, exec, runStep_some, XOp.exec, xmm_setXmm, reduceCtorEq, ↓reduceIte, runBlock_nil]

/-- `movdqa xmm2, xmm6; pmuludq xmm2, xmm4`, then the products into the sums. -/
theorem window_run (s : State) (hm : 0 < s.mcdt) :
    ∃ t, runBlock isa (([.xop (.bin .movdqa .xmm2 .xmm6), .pmuludq .xmm2 .xmm4] : List Instr) ++ acc .xmm2) s =
        some t ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mcdt = s.mcdt ∧
      t.xmm .xmm6 = s.xmm .xmm6 ∧
      t.xmm .xmm0 = XBinOp.eval .paddq (s.xmm .xmm0) (pmuludq (s.xmm .xmm6) (s.xmm .xmm4)) ∧
      t.xmm .xmm1 = XBinOp.eval .paddq (s.xmm .xmm1)
        (XShiftOp.eval .psrlq (pmuludq (s.xmm .xmm6) (s.xmm .xmm4)) 32) := by
  simp only [acc, List.cons_append, List.nil_append, runBlock_cons, exec, runStep_some,
    XOp.exec, ↓reduceIte, Option.some.injEq, exists_eq_left', mcdt_setXmm, hm, xmm_setXmm, reduceCtorEq,
    runBlock_nil, gpr_setXmm, movdqa_eval, mem_setXmm, rd_setXmm, wr_setXmm, and_self]

/-! ## The products of a column -/

/-- What every stage of a column has: the working space, the parameters
(`4 N` among them), `ecx = 4 k` and `pmuludq` allowed. -/
structure ColEnv (s : State) (W : Addr) (L : Nat) (V : Nat → BitVec 32) (N k : Nat) : Prop where
  ws : Ws s W L
  prm : Params s W L V 12
  n4 : (V pN4).toNat = 4 * N
  hk : k < 2 * N
  hN : N < 2 ^ 29
  ecx : s.gpr .ecx = BitVec.ofNat 32 (4 * k)
  mcdt : 0 < s.mcdt

theorem ColEnv.of_keeps {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k : Nat}
    (C : ColEnv s W L V N k) {rs : List Reg} (K : Keeps rs s t) (hm : t.mem = s.mem) (hc : t.mcdt = s.mcdt)
    (hcx : .ecx ∉ rs := by decide) (hsp : .esp ∉ rs := by decide) :
    ColEnv t W L V N k :=
  ⟨C.ws.of_keeps K, C.prm.keep (by rw [hm]; exact Outs.refl _ _ _) (K.1 _ hsp) K.2.1 K.2.2, C.n4, C.hk, C.hN,
    by rw [K.1 _ hcx]; exact C.ecx, by rw [hc]; exact C.mcdt⟩

theorem ColEnv.of_sk {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k : Nat}
    (C : ColEnv s W L V N k) {rs : List Reg} (K : Sk rs s t)
    (hcx : .ecx ∉ rs := by decide) (hsp : .esp ∉ rs := by decide) :
    ColEnv t W L V N k := C.of_keeps K.keep K.mem K.mcdt hcx hsp

/-- `dot`, on the sums. -/
theorem dotAcc_ok {t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k x y n P H n0 : Nat}
    (C : ColEnv t W L V N k) (hx : PtrAt t W .esi x) (hy : PtrAt t W .edi y)
    (hbp : t.gpr .ebp = BitVec.ofNat 32 (4 * n)) (xr : n = 0 ∨ x + 4 * n ≤ L) (yr : n = 0 ∨ y + 4 * n ≤ L)
    (hn : n ≤ 2 * N) (hH : H + (n + 4) * 2 ^ 32 < 2 ^ 64)
    (A : Acc (t.xmm .xmm0) (t.xmm .xmm1) P H n0) :
    WP isa dot t fun u =>
      Acc (u.xmm .xmm0) (u.xmm .xmm1) (P + dsum t.mem W x y n) (H + dhigh t.mem W x y n) (n0 + n) ∧
      Keeps [.eax, .esi, .edi, .ebp] t u ∧ u.mem = t.mem ∧ u.mcdt = t.mcdt ∧
      u.xmm .xmm6 = t.xmm .xmm6 := by
  have hN := C.hN
  exact WP.mono (dot_ok ⟨xr, yr, hH, by omega_arith, C.mcdt⟩ C.ws hx hy hbp A.sums)
    fun u D => ⟨A.dot D.sums, D.keep, D.mem, D.mcdt, D.x6⟩

/-- A pointer from a parameter. -/
theorem ptr_of_param {u : State} {W : Addr} {r : Reg} {v : BitVec 32} {x : Nat} (h : u.gpr r = v)
    (hv : v.toNat = (W.toNat + x) % 2 ^ 32) : PtrAt u W r x := by rw [PtrAt, h, hv]

/-- A pointer as a value. -/
theorem ptr_iff {u : State} {W : Addr} {r : Reg} {x : Nat} :
    PtrAt u W r x ↔ u.gpr r = BitVec.ofNat 32 (W.toNat + x) := by
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat]
  · intro h; rw [PtrAt, h, BitVec.toNat_ofNat]

theorem pv_ofNat {v : BitVec 32} {W : Addr} {x : Nat} (h : v.toNat = (W.toNat + x) % 2 ^ 32) :
    v = BitVec.ofNat 32 (W.toNat + x) := by
  apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat]

theorem ofNat_add3 (a b : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem wp_shrX {s : State} {is : List Instr} {Q : State → Prop} {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ t, Upd s t d (s.gpr d >>> n) → t.mcdt = s.mcdt → t.xmm = s.xmm → WP isa (.block is) t Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q :=
  cons (by simp only [exec, execShift, hn, and_self, ite_true])
    (k _ (Upd.setFlags _ _ (some ((s.gpr d).getLsbD (n - 1))) (if n = 1 then some (s.gpr d).msb else none)
      (some (s.gpr d >>> n == 0)) (some (s.gpr d >>> n).msb) _) rfl rfl)

/-- `endHalf`'s `ebx`: `4 ⌊(k + 1) / 2⌋`. -/
theorem half_val {k : Nat} (hk : 4 * (k + 1) < 2 ^ 32) :
    let v := (BitVec.ofNat 32 (4 * k) + 4) >>> 3
    v + v + (v + v) = BitVec.ofNat 32 (4 * ((k + 1) / 2)) := by
  intro v
  obtain hv : v.toNat = (k + 1) / 2 := by
    simp only [v, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]
    rw [Nat.mod_eq_of_lt (a := 4 * k) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  apply ofNat_of_toNat
  simp only [BitVec.toNat_add, hv]
  omega_arith

/-- The parameters' values: pointers into the working space and `4 N`. -/
structure PVals (V : Nat → BitVec 32) (W : Addr) (N S mo inv o a b : Nat) : Prop where
  a : (V pA).toNat = (W.toNat + a) % 2 ^ 32
  b : (V pB).toNat = (W.toNat + b) % 2 ^ 32
  mo : (V pM).toNat = (W.toNat + mo) % 2 ^ 32
  o : (V pO).toNat = (W.toNat + o) % 2 ^ 32
  s : (V pS).toNat = (W.toNat + S) % 2 ^ 32
  inv : (V pInv).toNat = (W.toNat + inv) % 2 ^ 32
  n4 : (V pN4).toNat = 4 * N

/-- `A'`: `A` in reverse at `S + 24 + 4 N`. -/
def RevA (m : Mem) (W : Addr) (N S a : Nat) : Prop :=
  ∀ i < N, w32 m W (S + 24 + 4 * N + 4 * (N - 1 - i)) = digits m W a i

/-- `j` times `add r, eax`. -/
theorem addRep_ok {s : State} {r : Reg} (hr : r ≠ .eax) {X V4 : Nat} (hx : s.gpr r = BitVec.ofNat 32 X)
    (ha : s.gpr .eax = BitVec.ofNat 32 V4) (j : Nat) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr r = BitVec.ofNat 32 (X + j * V4) → t.gpr .eax = BitVec.ofNat 32 V4 → Sk [r] s t →
      WP isa (.block rest) t Q) :
    WP isa (.block (List.replicate j (.alu .add r (.reg .eax)) ++ rest)) s Q := by
  induction j generalizing s X with
  | zero => exact k s (by rw [hx, Nat.zero_mul, Nat.add_zero]) ha (Sk.refl _ _)
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append]
    refine wp_addX rfl fun t u _ m x => ih (X := X + V4) (by rw [u.gpr, hx, ha, ofNat_add3])
      (by rw [u.other _ (Ne.symm hr), ha]) fun t' e a K => k t' (by rw [e]; congr 1; rw [Nat.succ_mul]; omega_arith) a
        ((Sk.of_upd [r] u m x (by simp)).trans K (by simp))

/-- `ldW r d j`: `r = S + 24 + d + j (4 N)` and `eax = 4 N`. -/
theorem ldW_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S : Nat} (P : Params s W L V 12)
    (hS : (V pS).toNat = (W.toNat + S) % 2 ^ 32) (hN : (V pN4).toNat = 4 * N) {r : Reg} (hr : r ≠ .eax)
    (hsp : r ≠ .esp) (d j : Nat) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr r = BitVec.ofNat 32 (W.toNat + (S + 24 + d) + j * (4 * N)) →
      t.gpr .eax = BitVec.ofNat 32 (4 * N) → Sk [r, .eax] s t → WP isa (.block rest) t Q) :
    WP isa (.block (ldW r d j ++ rest)) s Q := by
  simp only [ldW, List.cons_append, List.append_assoc, offW]
  refine wp_movX (P.read pS (by decide)) fun t1 u1 m1 x1 => wp_addX rfl fun t2 u2 _ m2 x2 => ?_
  obtain K2 : Sk [r, .eax] s t2 := (Sk.of_upd [r, .eax] u1 m1 x1 (by simp)).trans (Sk.of_upd [r, .eax] u2 m2 x2 (by simp)) (by simp)
  obtain e2 : t2.gpr r = BitVec.ofNat 32 (W.toNat + (S + 24 + d)) := by
    rw [u2.gpr, u1.gpr, pv_ofNat hS]; show _ + BitVec.ofNat 32 (24 + d) = _; rw [ofNat_add3]; congr 1; omega_arith
  refine wp_movX (P.readSk K2 (i := pN4) (by decide) (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨Ne.symm hsp, by decide⟩)) fun t3 u3 m3 x3 => ?_
  obtain K3 : Sk [r, .eax] s t3 := K2.trans (Sk.of_upd [r, .eax] u3 m3 x3 (by simp)) (by simp)
  obtain a3 : t3.gpr .eax = BitVec.ofNat 32 (4 * N) := by rw [u3.gpr]; exact ofNat_of_toNat hN
  obtain e3 : t3.gpr r = BitVec.ofNat 32 (W.toNat + (S + 24 + d)) := by rw [u3.other _ hr, e2]
  exact addRep_ok hr e3 a3 j fun t e a K => k t e a (K3.trans K (by simp))

/-- `dot` over a number stored in reverse (its word `N - 1 - i` at `xp` is
`f_i` for `i0 ≤ i < e`) and one at `y`: the column's `Σ f_i Y_(k-i)`, `i0 ≤ i < e`. -/
theorem dotRev_ok {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k xp y e i0 P H n0 : Nat}
    {f : Nat → Nat} (C : ColEnv t W L V N k) (K : Sk [.eax, .ebx, .esi, .edi, .ebp] s t)
    (hx : PtrAt t W .esi (xp + 4 * (N - e))) (hy : PtrAt t W .edi (y + 4 * (k + 1 - e)))
    (hbp : t.gpr .ebp = BitVec.ofNat 32 (4 * (e - i0))) (he : e ≤ N) (hek : e ≤ k + 1) (hi : i0 ≤ e)
    (hf : ∀ i, i0 ≤ i → i < e → w32 s.mem W (xp + 4 * (N - 1 - i)) = f i)
    (xr : e = i0 ∨ xp + 4 * N ≤ L) (yr : e = i0 ∨ y + 4 * (k + 1 - i0) ≤ L) (hH : H + (N + 4) * 2 ^ 32 < 2 ^ 64)
    (A : Acc (t.xmm .xmm0) (t.xmm .xmm1) P H n0) :
    WP isa dot t fun u =>
      Acc (u.xmm .xmm0) (u.xmm .xmm1) (P + csum f (digits s.mem W y) k i0 (e - i0))
        (H + dhigh s.mem W (xp + 4 * (N - e)) (y + 4 * (k + 1 - e)) (e - i0)) (n0 + (e - i0)) ∧
      Keeps [.eax, .ebx, .esi, .edi, .ebp] s u ∧ u.mem = s.mem ∧ u.mcdt = s.mcdt ∧
      u.xmm .xmm6 = s.xmm .xmm6 ∧ u.gpr .ebx = t.gpr .ebx := by
  have hN := C.hN
  refine WP.mono (dotAcc_ok C hx hy hbp (by omega_arith) (by omega_arith) (by omega_arith)
    (Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega_arith)) _) hH) A)
    fun u ⟨Au, Ku, mu, cu, u6⟩ => ?_
  rw [K.mem, dsum_rev s.mem W xp y f he hek hi hf] at Au
  exact ⟨Au, (K.keep.mono (by decide)).trans (Ku.mono (by decide)), by rw [mu, K.mem], by rw [cu, K.mcdt],
    by rw [u6, K.xmm], Ku.1 _ (by decide)⟩

/-- What the products of `A` and `B` leave: their coefficient in the sums,
with at most `N + 1` low words, and what stays. -/
structure InPost (s : State) (N P : Nat) (u : State) : Prop where
  acc : ∃ H n, Acc (u.xmm .xmm0) (u.xmm .xmm1) P H n ∧ n ≤ N + 1 ∧ H ≤ (N + 1) * 2 ^ 32
  keep : Keeps [.eax, .ebx, .esi, .edi, .ebp] s u
  mem : u.mem = s.mem
  mcdt : u.mcdt = s.mcdt
  x6 : u.xmm .xmm6 = s.xmm .xmm6

theorem dhigh_le' (m : Mem) (W : Addr) (x y n : Nat) : dhigh m W x y n ≤ n * 2 ^ 32 :=
  Nat.le_trans (dhigh_le m W x y n) (Nat.mul_le_mul_left _ (by omega_arith))

/-- The products of `A` and `B` while `k < N`. -/
theorem mulLo_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S mo inv o a b : Nat}
    (C : ColEnv s W L V N k) (PV : PVals V W N S mo inv o a b) (hkN : k < N) (hb : b + 4 * N ≤ L)
    (hs : S + 8 * N + 28 ≤ L) (RA : RevA s.mem W N S a) (A : Acc (s.xmm .xmm0) (s.xmm .xmm1) 0 0 0) :
    WP isa (input false false) s
      (InPost s N (Column.coeff (digits s.mem W a) (digits s.mem W b) N k)) := by
  have hN := C.hN
  have hn := C.ws.nowrap
  simp only [input, ld, List.cons_append, List.nil_append, List.append_assoc]
  refine WP.seq (wp_movX rfl fun t1 u1 m1 x1 => wp_addX rfl fun t2 u2 _ m2 x2 => ?_)
  obtain K2 : Sk [.eax, .ebx, .esi, .edi, .ebp] s t2 := (Sk.of_upd [.eax, .ebx, .esi, .edi, .ebp] u1 m1 x1).trans (Sk.of_upd [.eax, .ebx, .esi, .edi, .ebp] u2 m2 x2)
  obtain b2 : t2.gpr .ebp = BitVec.ofNat 32 (4 * (k + 1)) := by
    rw [u2.gpr, u1.gpr, C.ecx]; show _ + BitVec.ofNat 32 4 = _; rw [ofNat_add3]; congr 1
  refine ldW_ok (C.prm.of_sk K2) PV.s PV.n4 (r := .esi) (by decide) (by decide) 0 2 fun t3 e3 a3 K3 => ?_
  refine wp_subX rfl fun t4 u4 _ m4 x4 => wp_movX ((C.prm.of_sk (K2.trans K3)).readSk (Sk.of_upd [.esi] u4 m4 x4)
    (i := pB) (by decide)) fun t5 u5 m5 x5 => WP.block_nil ?_
  obtain K5 : Sk [.eax, .ebx, .esi, .edi, .ebp] s t5 :=
    ((K2.trans K3).trans (Sk.of_upd [.eax, .ebx, .esi, .edi, .ebp] u4 m4 x4)).trans (Sk.of_upd [.eax, .ebx, .esi, .edi, .ebp] u5 m5 x5)
  obtain C5 := C.of_sk K5
  obtain esi5 : PtrAt t5 W .esi (S + 24 + 4 * N + 4 * (N - (k + 1))) := by
    rw [ptr_iff, u5.other _ (by decide), u4.gpr, e3, K3.keep.1 _ (by decide), b2, sub_ofNat (by omega_arith)]
    congr 1; omega_arith
  obtain edi5 : PtrAt t5 W .edi (b + 4 * (k + 1 - (k + 1))) := by
    rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero]; exact ptr_of_param u5.gpr PV.b
  obtain ebp5 : t5.gpr .ebp = BitVec.ofNat 32 (4 * (k + 1 - 0)) := by
    rw [u5.other _ (by decide), u4.other _ (by decide), K3.keep.1 _ (by decide), b2, Nat.sub_zero]
  refine WP.mono (dotRev_ok (f := digits s.mem W a) (P := 0) (H := 0) (n0 := 0) C5 K5 esi5 edi5 ebp5 (by omega_arith)
    (by omega_arith) (by omega_arith) (fun i _ hi => RA i (by omega_arith)) (.inr (by omega_arith)) (.inr (by omega_arith)) (by omega_arith)
    (by rw [K5.xmm]; exact A)) fun u ⟨Au, Ku, mu, cu, u6, _⟩ => ⟨?_, Ku, mu, cu, u6⟩
  obtain e := csum_product (digits s.mem W a) (digits s.mem W b) (N := N) (k := k)
  rw [show k + 1 - N = 0 by omega_arith, show min (k + 1) N = k + 1 by omega_arith] at e
  rw [Nat.zero_add, Nat.zero_add, e] at Au
  exact ⟨_, _, Au, by omega_arith, Nat.le_trans (dhigh_le' _ _ _ _ _) (Nat.mul_le_mul_right _ (by omega_arith))⟩

/-- `lenHigh`: `ebp = 4 (2 N - 1 - k)` and `eax = 4 N`. -/
theorem lenHigh_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k : Nat} (C : ColEnv s W L V N k)
    (hkN : N ≤ k) {rest : List Instr} {Q : State → Prop}
    (h : ∀ t, t.gpr .ebp = BitVec.ofNat 32 (4 * (2 * N - 1 - k)) → t.gpr .eax = BitVec.ofNat 32 (4 * N) →
      Sk [.eax, .ebp] s t → WP isa (.block rest) t Q) :
    WP isa (.block (lenHigh ++ rest)) s Q := by
  have hk := C.hk
  have hN := C.hN
  simp only [lenHigh, List.cons_append, List.nil_append]
  refine wp_movX (C.prm.read pN4 (by decide)) fun t1 u1 m1 x1 => wp_movX rfl fun t2 u2 m2 x2 =>
    wp_addX rfl fun t3 u3 _ m3 x3 => wp_subX rfl fun t4 u4 _ m4 x4 => wp_subX rfl fun t5 u5 _ m5 x5 => ?_
  obtain K5 : Sk [.eax, .ebp] s t5 := ((((Sk.of_upd [.eax, .ebp] u1 m1 x1).trans (Sk.of_upd [.eax, .ebp] u2 m2 x2)).trans
    (Sk.of_upd [.eax, .ebp] u3 m3 x3)).trans (Sk.of_upd [.eax, .ebp] u4 m4 x4)).trans (Sk.of_upd [.eax, .ebp] u5 m5 x5)
  obtain a1 : t1.gpr .eax = BitVec.ofNat 32 (4 * N) := by rw [u1.gpr]; exact ofNat_of_toNat C.n4
  obtain c1 : t1.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [u1.other _ (by decide)]; exact C.ecx
  refine h t5 ?_ (by simp (disch := decide) only [u5.other, u4.other, u3.other, u2.other, a1]) K5
  simp (disch := decide) only [u5.gpr, u4.gpr, u4.other, u3.gpr, u3.other, u2.gpr, u2.other, a1, c1,
    ofNat_add3]
  show BitVec.ofNat 32 (4 * N + 4 * N) - BitVec.ofNat 32 4 - _ = _
  rw [sub_ofNat (by omega_arith), sub_ofNat (by omega_arith)]; congr 1; omega_arith

/-- The products of `A` and `B` from `k = N` on. -/
theorem mulHi_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S mo inv o a b : Nat}
    (C : ColEnv s W L V N k) (PV : PVals V W N S mo inv o a b) (hkN : N ≤ k) (hb : b + 4 * N ≤ L)
    (hs : S + 8 * N + 28 ≤ L) (RA : RevA s.mem W N S a) (A : Acc (s.xmm .xmm0) (s.xmm .xmm1) 0 0 0) :
    WP isa (input false true) s
      (InPost s N (Column.coeff (digits s.mem W a) (digits s.mem W b) N k)) := by
  have hN := C.hN
  have hk := C.hk
  have hn := C.ws.nowrap
  simp only [input, ld, List.cons_append, List.nil_append, List.append_assoc]
  refine WP.seq (lenHigh_ok C hkN fun t1 b1 a1 K1 => ?_)
  obtain K1' := K1.mono [.eax, .ebx, .esi, .edi, .ebp]
  refine ldW_ok (C.prm.of_sk K1) PV.s PV.n4 (r := .esi) (by decide) (by decide) 0 1 fun t2 e2 a2 K2 => ?_
  obtain K2' := K1'.trans K2
  refine wp_movX ((C.prm.of_sk K2').read pB (by decide)) fun t3 u3 m3 x3 => wp_addX rfl fun t4 u4 _ m4 x4 =>
    wp_addX rfl fun t5 u5 _ m5 x5 => wp_subX rfl fun t6 u6 _ m6 x6 => WP.block_nil ?_
  obtain K6 : Sk [.eax, .ebx, .esi, .edi, .ebp] s t6 := (((K2'.trans (Sk.of_upd [.edi] u3 m3 x3)).trans
    (Sk.of_upd [.edi] u4 m4 x4)).trans (Sk.of_upd [.edi] u5 m5 x5)).trans (Sk.of_upd [.edi] u6 m6 x6)
  obtain C6 := C.of_sk K6
  obtain c2 : t2.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [K2.keep.1 _ (by decide), K1.keep.1 _ (by decide), C.ecx]
  obtain esi6 : PtrAt t6 W .esi (S + 24 + 4 * N + 4 * (N - N)) := by
    rw [ptr_iff]; simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, e2]
    congr 1; omega_arith
  obtain edi6 : PtrAt t6 W .edi (b + 4 * (k + 1 - N)) := by
    rw [ptr_iff]; simp (disch := decide) only [u6.gpr, u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr,
      u3.other, a2, c2, pv_ofNat PV.b]
    show BitVec.ofNat 32 _ + _ + BitVec.ofNat 32 4 - _ = _
    rw [ofNat_add3, ofNat_add3, sub_ofNat (by omega_arith)]; congr 1; omega_arith
  obtain ebp6 : t6.gpr .ebp = BitVec.ofNat 32 (4 * (N - (k + 1 - N))) := by
    simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other]
    rw [K2.keep.1 _ (by decide), b1]; congr 1; omega_arith
  refine WP.mono (dotRev_ok (f := digits s.mem W a) (P := 0) (H := 0) (n0 := 0) C6 K6 esi6 edi6 ebp6 (by omega_arith)
    (by omega_arith) (by omega_arith) (fun i _ hi => RA i (by omega_arith)) (.inr (by omega_arith)) (.inr (by omega_arith)) (by omega_arith)
    (by rw [K6.xmm]; exact A)) fun u ⟨Au, Ku, mu, cu, u6, _⟩ => ⟨?_, Ku, mu, cu, u6⟩
  obtain e := csum_product (digits s.mem W a) (digits s.mem W b) (N := N) (k := k)
  rw [show min (k + 1) N = N by omega_arith] at e
  rw [Nat.zero_add, Nat.zero_add, e] at Au
  exact ⟨_, _, Au, by omega_arith, Nat.le_trans (dhigh_le' _ _ _ _ _) (Nat.mul_le_mul_right _ (by omega_arith))⟩

/-- A square's sum doubled, then the diagonal's product: from the products
above the diagonal, with `ebx = 4 ⌊(k + 1) / 2⌋`. -/
theorem sqTail_ok {u : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k a H n : Nat}
    (C : ColEnv u W L V N k) (hA : (V pA).toNat = (W.toNat + a) % 2 ^ 32) (ha : a + 4 * N ≤ L)
    (bu : u.gpr .ebx = BitVec.ofNat 32 (4 * ((k + 1) / 2))) (hH : 2 * H + 2 ^ 32 < 2 ^ 64)
    (A' : Acc (u.xmm .xmm0) (u.xmm .xmm1) (Column.crossCoeff (digits u.mem W a) N k) H n) :
    WP isa (.seq (.block [.xop (.bin .paddq .xmm0 .xmm0), .xop (.bin .paddq .xmm1 .xmm1)]) diag) u fun w =>
      ∃ H' n', Acc (w.xmm .xmm0) (w.xmm .xmm1) (Column.coeff (digits u.mem W a) (digits u.mem W a) N k) H' n' ∧
        n' ≤ 2 * n + 1 ∧ H' ≤ 2 * H + 2 ^ 32 ∧ Keeps [.eax, .esi] u w ∧ w.mem = u.mem ∧ w.mcdt = u.mcdt ∧
        w.xmm .xmm6 = u.xmm .xmm6 := by
  have hk := C.hk
  have hN := C.hN
  have hn := C.ws.nowrap
  refine WP.seq (WP.of_runBlock ⟨_, double_run u, ?_⟩)
  obtain Ad := A'.double (by omega_arith)
  let v := (u.setXmm .xmm0 (XBinOp.eval .paddq (u.xmm .xmm0) (u.xmm .xmm0))).setXmm .xmm1
    (XBinOp.eval .paddq (u.xmm .xmm1) (u.xmm .xmm1))
  obtain Cv : ColEnv v W L V N k := C.of_keeps (rs := []) ⟨fun _ _ => rfl, rfl, rfl⟩ rfl rfl
  have x0v : v.xmm .xmm0 = XBinOp.eval .paddq (u.xmm .xmm0) (u.xmm .xmm0) := rfl
  have x1v : v.xmm .xmm1 = XBinOp.eval .paddq (u.xmm .xmm1) (u.xmm .xmm1) := rfl
  have x6v : v.xmm .xmm6 = u.xmm .xmm6 := rfl
  rw [← x0v, ← x1v] at Ad
  have vm : v.mem = u.mem := rfl
  have vc : v.mcdt = u.mcdt := rfl
  obtain hcross : 2 * Column.crossCoeff (digits u.mem W a) N k + Column.diagCoeff (digits u.mem W a) N k =
      Column.coeff (digits u.mem W a) (digits u.mem W a) N k := (Column.coeff_square _ _ _).symm
  rw [Column.diagCoeff_value] at hcross
  unfold diag
  refine WP.seq (wp_movX rfl fun w1 y1 n1 z1 => wp_addX rfl fun w2 y2 _ n2 z2 =>
    wp_cmpX rfl fun w3 f3 _ zf3 n3 z3 => WP.block_nil ?_)
  obtain e2 : w2.gpr .eax = BitVec.ofNat 32 (8 * ((k + 1) / 2)) := by
    rw [y2.gpr, y1.gpr, show v.gpr .ebx = u.gpr .ebx from rfl, bu, ← BitVec.ofNat_add]; congr 1; omega_arith
  obtain c2 : w2.gpr .ecx = BitVec.ofNat 32 (4 * k) := by
    rw [y2.other _ (by decide), y1.other _ (by decide)]; exact Cv.ecx
  obtain K3 : Sk [.eax, .esi] v w3 := ((Sk.of_upd [.eax, .esi] y1 n1 z1).trans (Sk.of_upd [.eax] y2 n2 z2)).trans
    (Sk.of_fupd f3 n3 z3 [.eax])
  obtain Kvs : Keeps [.eax, .esi] u v := ⟨fun _ _ => rfl, rfl, rfl⟩
  by_cases hev : k % 2 = 0
  · refine WP.ite true (by
        show w3.zf = some true
        rw [zf3, e2, c2, sub_beq (by omega_arith) (by omega_arith), decide_eq_true (by omega_arith)])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.cons_append, List.cons_append, List.cons_append]
    obtain C3 := Cv.of_sk K3
    refine wp_movX (C3.prm.read pA (by decide)) fun w4 y4 n4 z4 => wp_addX rfl fun w5 y5 _ n5 z5 => ?_
    obtain K5 : Sk [.eax, .esi] v w5 := (K3.trans (Sk.of_upd [.esi] y4 n4 z4)).trans (Sk.of_upd [.esi] y5 n5 z5)
    obtain p5 : PtrAt w5 (W := W) .esi (a + 4 * (k / 2)) := by
      have := (V pA).isLt
      rw [PtrAt, y5.gpr, y4.gpr, y4.other _ (by decide), f3.gpr, y2.other _ (by decide), y1.other _ (by decide),
        show v.gpr .ebx = u.gpr .ebx from rfl, bu, BitVec.toNat_add, hA, toNat_ofNat_lt (by omega_arith)]
      omega_arith
    obtain hw5 := C.ws.of_keeps (Kvs.trans (K5.keep.mono (by decide)))
    refine wp_movX (readSrc_ptr hw5 p5 (d := 0) (by omega_arith)) fun w6 y6 n6 z6 => ?_
    obtain K6 : Sk [.eax, .esi] v w6 := K5.trans (Sk.of_upd [.eax] y6 n6 z6)
    obtain ⟨w7, run, g7, m7, rd7, wr7, mc7, s6, a0, a1⟩ := sq_run w6 (by rw [K6.mcdt]; exact Cv.mcdt)
    obtain Af := Ad.single (u := w6.gpr .eax) (v := w6.gpr .eax) (by omega_arith)
    rw [← K6.xmm, ← a0, ← a1] at Af
    obtain hq : (w6.gpr .eax).toNat * (w6.gpr .eax).toNat / 2 ^ 32 < 2 ^ 32 :=
      (Nat.div_lt_iff_lt_mul (by decide)).2 (by have := word_mul_lt (w6.gpr .eax) (w6.gpr .eax); omega_arith)
    refine WP.of_runBlock ⟨w7, run, _, _, Af.of_eq' ?_, by omega_arith, by omega_arith, ?_, ?_, ?_, ?_⟩
    · rw [← hcross, ite_eq_left ⟨hev, by omega_arith⟩, y6.gpr, K5.mem, vm]
      simp only [digits, w32, Nat.add_zero]
    · exact (Kvs.trans (K6.keep.mono (by decide))).trans ⟨fun r _ => by rw [g7], rd7, wr7⟩
    · rw [m7, K6.mem, vm]
    · rw [mc7, K6.mcdt, vc]
    · rw [s6, K6.xmm, x6v]
  · refine WP.ite false (by
        show w3.zf = some false
        rw [zf3, e2, c2, sub_beq (by omega_arith) (by omega_arith), decide_eq_false (by omega_arith)])
      (fun h => absurd h (by decide)) (fun _ => WP.block_nil ?_)
    have Ao := Ad
    rw [← K3.xmm] at Ao
    refine ⟨_, _, Ao.of_eq' ?_, by omega_arith, by omega_arith, Kvs.trans (K3.keep.mono (by decide)), by rw [K3.mem, vm],
      by rw [K3.mcdt, vc], by rw [K3.xmm, x6v]⟩
    rw [← hcross, ite_eq_right (by omega_arith), Nat.add_zero]

/-- A square's count of products above the diagonal: `ebp = 4 (e - (k + 1 - N))`
for `ebx = 4 e`, `e = ⌊(k + 1) / 2⌋`. -/
theorem sqLen_ok {t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k : Nat} (C : ColEnv t W L V N k)
    (hi : Bool) (hhi : hi = true ↔ N ≤ k) (bx : t.gpr .ebx = BitVec.ofNat 32 (4 * ((k + 1) / 2)))
    {rest : List Instr} {Q : State → Prop}
    (h : ∀ u, u.gpr .ebp = BitVec.ofNat 32 (4 * ((k + 1) / 2 - (k + 1 - N))) → Sk [.eax, .ebp] t u →
      WP isa (.block rest) u Q) :
    WP isa (.block ((if hi then [.mov .eax (.mem (kp pN4)), .mov .ebp (.reg .ebx), .alu .add .ebp (.reg .eax),
      .alu .sub .ebp (.reg .ecx), .alu .sub .ebp (.imm 4)] else [.mov .ebp (.reg .ebx)]) ++ rest)) t Q := by
  have hk := C.hk
  have hN := C.hN
  cases hi with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
    refine wp_movX rfl fun u1 v1 m1 x1 => h u1 ?_ (Sk.of_upd [.eax, .ebp] v1 m1 x1)
    rw [v1.gpr, bx]; congr 1; have : ¬ N ≤ k := fun h => absurd (hhi.mpr h) (by decide); omega_arith
  | true =>
    simp only [↓reduceIte, List.cons_append, List.nil_append]
    obtain hkN := hhi.mp rfl
    refine wp_movX (C.prm.read pN4 (by decide)) fun u1 v1 m1 x1 => wp_movX rfl fun u2 v2 m2 x2 =>
      wp_addX rfl fun u3 v3 _ m3 x3 => wp_subX rfl fun u4 v4 _ m4 x4 => wp_subX rfl fun u5 v5 _ m5 x5 => ?_
    refine h u5 ?_ ((((((Sk.of_upd [.eax, .ebp] v1 m1 x1).trans (Sk.of_upd [.eax, .ebp] v2 m2 x2)).trans
      (Sk.of_upd [.eax, .ebp] v3 m3 x3)).trans (Sk.of_upd [.eax, .ebp] v4 m4 x4)).trans (Sk.of_upd [.eax, .ebp] v5 m5 x5)))
    obtain a1 : u1.gpr .eax = BitVec.ofNat 32 (4 * N) := by rw [v1.gpr]; exact ofNat_of_toNat C.n4
    simp (disch := decide) only [v5.gpr, v4.gpr, v3.gpr, v3.other, v2.gpr, v2.other, v1.other, a1, bx,
      C.ecx, ofNat_add3]
    show BitVec.ofNat 32 _ - BitVec.ofNat 32 (4 * k) - BitVec.ofNat 32 4 = _
    rw [sub_ofNat (by omega_arith), sub_ofNat (by omega_arith)]; congr 1; omega_arith

/-- A square's products: those above the diagonal, doubled, and the diagonal's. -/
theorem sq_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S mo inv o a b : Nat}
    (C : ColEnv s W L V N k) (PV : PVals V W N S mo inv o a b) (hi : Bool) (hhi : hi = true ↔ N ≤ k)
    (ha : a + 4 * N ≤ L) (hs : S + 8 * N + 28 ≤ L) (RA : RevA s.mem W N S a)
    (A : Acc (s.xmm .xmm0) (s.xmm .xmm1) 0 0 0) :
    WP isa (input true hi) s (InPost s N (Column.coeff (digits s.mem W a) (digits s.mem W a) N k)) := by
  have hN := C.hN
  have hk := C.hk
  have hn := C.ws.nowrap
  simp only [input, seqs, endHalf, ld, List.cons_append, List.append_assoc]
  refine WP.seq (wp_movX rfl fun t1 u1 m1 x1 => wp_addX rfl fun t2 u2 _ m2 x2 =>
    wp_shrX (by decide) fun t3 u3 m3 x3 => wp_addX rfl fun t4 u4 _ m4 x4 => wp_addX rfl fun t5 u5 _ m5 x5 => ?_)
  obtain K5 : Sk [.eax, .ebx, .esi, .edi, .ebp] s t5 := ((((Sk.of_upd [.eax, .ebx, .esi, .edi, .ebp] u1 m1 x1).trans
    (Sk.of_upd [.ebx] u2 m2 x2)).trans (Sk.of_upd [.ebx] u3 m3 x3)).trans (Sk.of_upd [.ebx] u4 m4 x4)).trans
    (Sk.of_upd [.ebx] u5 m5 x5)
  obtain C5 := C.of_sk K5
  obtain b5 : t5.gpr .ebx = BitVec.ofNat 32 (4 * ((k + 1) / 2)) := by
    rw [u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr, C.ecx]; exact half_val (by omega_arith)
  refine sqLen_ok C5 hi hhi b5 fun t6 bp6 K6 => ?_
  obtain K6' := K5.trans (K6.mono [.eax, .ebx, .esi, .edi, .ebp])
  refine ldW_ok (C.prm.of_sk K6') PV.s PV.n4 (r := .esi) (by decide) (by decide) 0 2 fun t7 e7 a7 K7 => ?_
  obtain K7' := K6'.trans (K7.mono [.eax, .ebx, .esi, .edi, .ebp])
  refine wp_subX rfl fun t8 u8 _ m8 x8 => wp_movX ((C.prm.of_sk K7').readSk (Sk.of_upd [.esi] u8 m8 x8)
    (i := pA) (by decide)) fun t9 u9 m9 x9 => wp_addX rfl fun t10 u10 _ m10 x10 =>
    wp_addX rfl fun t11 u11 _ m11 x11 => wp_subX rfl fun t12 u12 _ m12 x12 => WP.block_nil ?_
  obtain K12 : Sk [.eax, .ebx, .esi, .edi, .ebp] s t12 := ((((K7'.trans (Sk.of_upd [.esi] u8 m8 x8)).trans
    (Sk.of_upd [.edi] u9 m9 x9)).trans (Sk.of_upd [.edi] u10 m10 x10)).trans (Sk.of_upd [.edi] u11 m11 x11)).trans
    (Sk.of_upd [.edi] u12 m12 x12)
  obtain C12 := C.of_sk K12
  obtain b7 : t7.gpr .ebx = BitVec.ofNat 32 (4 * ((k + 1) / 2)) := by
    rw [K7.keep.1 _ (by decide), K6.keep.1 _ (by decide), b5]
  obtain c7 : t7.gpr .ecx = BitVec.ofNat 32 (4 * k) := by
    rw [K7.keep.1 _ (by decide), K6.keep.1 _ (by decide)]; exact C5.ecx
  obtain b12 : t12.gpr .ebx = BitVec.ofNat 32 (4 * ((k + 1) / 2)) := by
    simp (disch := decide) only [u12.other, u11.other, u10.other, u9.other, u8.other, b7]
  obtain esi12 : PtrAt t12 W .esi (S + 24 + 4 * N + 4 * (N - (k + 1) / 2)) := by
    rw [ptr_iff]; simp (disch := decide) only [u12.other, u11.other, u10.other, u9.other, u8.gpr, e7, b7]
    rw [sub_ofNat (by omega_arith)]; congr 1; omega_arith
  obtain edi12 : PtrAt t12 W .edi (a + 4 * (k + 1 - (k + 1) / 2)) := by
    have := (V pA).isLt
    rw [ptr_iff]; simp (disch := decide) only [u12.gpr, u11.gpr, u11.other, u10.gpr, u10.other, u9.gpr, u9.other,
      u8.other, b7, c7, pv_ofNat PV.a]
    show BitVec.ofNat 32 _ + _ + BitVec.ofNat 32 4 - _ = _
    rw [ofNat_add3, ofNat_add3, sub_ofNat (by omega_arith)]; congr 1; omega_arith
  obtain ebp12 : t12.gpr .ebp = BitVec.ofNat 32 (4 * ((k + 1) / 2 - (k + 1 - N))) := by
    simp (disch := decide) only [u12.other, u11.other, u10.other, u9.other, u8.other]
    rw [K7.keep.1 _ (by decide), bp6]
  refine WP.seq (WP.mono (dotRev_ok (f := digits s.mem W a) (P := 0) (H := 0) (n0 := 0) C12 K12 esi12 edi12 ebp12
    (by omega_arith) (by omega_arith) (by omega_arith) (fun i _ hi => RA i (by omega_arith)) (.inr (by omega_arith)) (.inr (by omega_arith))
    (by omega_arith) (by rw [K12.xmm]; exact A)) fun u ⟨Au, Ku, mu, cu, u6, bxu⟩ => ?_)
  rw [Nat.zero_add, Nat.zero_add, Nat.zero_add, csum_cross _ hk] at Au
  obtain Cu := C.of_keeps (rs := [.eax, .ebx, .esi, .edi, .ebp]) Ku mu cu
  obtain bu : u.gpr .ebx = BitVec.ofNat 32 (4 * ((k + 1) / 2)) := by rw [bxu, b12]
  rw [← mu] at Au
  obtain hl := dhigh_le' u.mem W (S + 24 + 4 * N + 4 * (N - (k + 1) / 2)) (a + 4 * (k + 1 - (k + 1) / 2))
    ((k + 1) / 2 - (k + 1 - N))
  refine WP.mono (sqTail_ok Cu PV.a ha bu (by omega_arith) Au) fun w ⟨H', n', Aw, hn', hH', Kw, mw, cw, w6⟩ => ?_
  rw [mu] at Aw
  exact ⟨⟨H', n', Aw, by omega_arith, by omega_arith⟩, Ku.trans (Kw.mono (by decide)), by rw [mw, mu],
    by rw [cw, cu], by rw [w6, u6]⟩

/-- The products of `A` and `B`: a square's if `A` is `B`. -/
theorem input_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S mo inv o a b : Nat}
    (C : ColEnv s W L V N k) (PV : PVals V W N S mo inv o a b) (sq hi : Bool) (hsq : sq = true → a = b)
    (hhi : hi = true ↔ N ≤ k) (ha : a + 4 * N ≤ L) (hb : b + 4 * N ≤ L) (hs : S + 8 * N + 28 ≤ L)
    (RA : RevA s.mem W N S a) (A : Acc (s.xmm .xmm0) (s.xmm .xmm1) 0 0 0) :
    WP isa (input sq hi) s (InPost s N (Column.coeff (digits s.mem W a) (digits s.mem W b) N k)) := by
  cases sq with
  | true => rw [← hsq rfl]; exact sq_ok C PV hi hhi ha hs RA A
  | false =>
    cases hi with
    | false => exact mulLo_ok C PV (by have : ¬ N ≤ k := fun h => absurd (hhi.mpr h) (by decide); omega_arith) hb hs RA A
    | true => exact mulHi_ok C PV (hhi.mp rfl) hb hs RA A

/-- What the products of the quotient digits and `M` leave. -/
structure RedPost (s : State) (N P H n : Nat) (u : State) : Prop where
  acc : ∃ H' n', Acc (u.xmm .xmm0) (u.xmm .xmm1) P H' n' ∧ n' ≤ n + (N + 2) ∧ H' ≤ H + (N + 2) * 2 ^ 32
  keep : Keeps [.eax, .ebx, .esi, .edi, .ebp] s u
  mem : u.mem = s.mem
  mcdt : u.mcdt = s.mcdt
  x6 : u.xmm .xmm6 = s.xmm .xmm6

/-- The quotient digits, in reverse at `S + 24`: `Q_i` for `lo ≤ i < hi`. -/
def RevQ (m : Mem) (W : Addr) (N S : Nat) (q : Nat → Nat) (lo hi : Nat) : Prop :=
  ∀ i, lo ≤ i → i < hi → w32 m W (S + 24 + 4 * (N - 1 - i)) = q i

/-- The products of the quotient digits and `M` from `k = N` on. -/
theorem reduceHi_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S mo inv o a b P H n : Nat}
    {q : Nat → Nat} (C : ColEnv s W L V N k) (PV : PVals V W N S mo inv o a b) (hkN : N ≤ k)
    (hm : mo + 4 * N ≤ L) (hs : S + 8 * N + 28 ≤ L) (RQ : RevQ s.mem W N S q (k + 1 - N) N)
    (hH : H + (N + 4) * 2 ^ 32 < 2 ^ 64) (A : Acc (s.xmm .xmm0) (s.xmm .xmm1) P H n) :
    WP isa (reduce true) s
      (RedPost s N (P + Column.coeff (Column.prefixDigits q k) (digits s.mem W mo) N k) H n) := by
  have hN := C.hN
  have hk := C.hk
  have hn := C.ws.nowrap
  simp only [reduce, ↓reduceIte, ld, List.cons_append, List.nil_append, List.append_assoc]
  refine WP.seq (lenHigh_ok C hkN fun t1 b1 a1 K1 => ?_)
  obtain K1' := K1.mono [.eax, .ebx, .esi, .edi, .ebp]
  refine ldW_ok (C.prm.of_sk K1) PV.s PV.n4 (r := .esi) (by decide) (by decide) 0 0 fun t2 e2 a2 K2 => ?_
  obtain K2' := K1'.trans K2
  refine wp_movX ((C.prm.of_sk K2').read pM (by decide)) fun t3 u3 m3 x3 => wp_addX rfl fun t4 u4 _ m4 x4 =>
    wp_addX rfl fun t5 u5 _ m5 x5 => wp_subX rfl fun t6 u6 _ m6 x6 => WP.block_nil ?_
  obtain K6 : Sk [.eax, .ebx, .esi, .edi, .ebp] s t6 := (((K2'.trans (Sk.of_upd [.edi] u3 m3 x3)).trans
    (Sk.of_upd [.edi] u4 m4 x4)).trans (Sk.of_upd [.edi] u5 m5 x5)).trans (Sk.of_upd [.edi] u6 m6 x6)
  obtain C6 := C.of_sk K6
  obtain c2 : t2.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [K2.keep.1 _ (by decide), K1.keep.1 _ (by decide), C.ecx]
  obtain esi6 : PtrAt t6 W .esi (S + 24 + 4 * (N - N)) := by
    rw [ptr_iff]; simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, e2]
    congr 1; omega_arith
  obtain edi6 : PtrAt t6 W .edi (mo + 4 * (k + 1 - N)) := by
    rw [ptr_iff]; simp (disch := decide) only [u6.gpr, u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr,
      u3.other, a2, c2, pv_ofNat PV.mo]
    show BitVec.ofNat 32 _ + _ + BitVec.ofNat 32 4 - _ = _
    rw [ofNat_add3, ofNat_add3, sub_ofNat (by omega_arith)]; congr 1; omega_arith
  obtain ebp6 : t6.gpr .ebp = BitVec.ofNat 32 (4 * (N - (k + 1 - N))) := by
    simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other]
    rw [K2.keep.1 _ (by decide), b1]; congr 1; omega_arith
  refine WP.mono (dotRev_ok (xp := S + 24) (y := mo) (f := q) (P := P) (H := H) (n0 := n) C6 K6 esi6 edi6 ebp6 (by omega_arith) (by omega_arith) (by omega_arith)
    (fun i h1 h2 => RQ i h1 h2) (.inr (by omega_arith)) (.inr (by omega_arith)) hH
    (by rw [K6.xmm]; exact A)) fun u ⟨Au, Ku, mu, cu, u6, _⟩ => ⟨?_, Ku, mu, cu, u6⟩
  obtain e := csum_reduce q (digits s.mem W mo) (N := N) (k := k)
  rw [show min k N = N by omega_arith] at e
  rw [e] at Au
  have := dhigh_le' s.mem W (S + 24 + 4 * (N - N)) (mo + 4 * (k + 1 - N)) (N - (k + 1 - N))
  exact ⟨_, _, Au, by omega_arith, by omega_arith⟩

/-- The two latest digits in `xmm6` (doublewords 0 and 2), while `k < N`. -/
structure Window (s : State) (k : Nat) (q : Nat → Nat) : Prop where
  q1 : (dword (s.xmm .xmm6) 0).toNat = if 1 ≤ k then q (k - 1) else 0
  q2 : (dword (s.xmm .xmm6) 2).toNat = if 2 ≤ k then q (k - 2) else 0

/-- `movq xmm4, [eax + 4]; punpckldq xmm4, xmm4`: the two words at `eax + 4` in doublewords 0 and 2. -/
theorem modLoad_run (s : State) (h : InRegions (s.rd ++ s.wr) (s.ea (at_ .eax 4)) 8) :
    ∃ t, runBlock isa [.movqLoad .xmm4 (at_ .eax 4), .xop (.bin .punpckldq .xmm4 .xmm4)] s = some t ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mcdt = s.mcdt ∧
      (∀ r, r ≠ .xmm4 → t.xmm r = s.xmm r) ∧
      t.xmm .xmm4 = XBinOp.eval .punpckldq ((0 : BitVec 64) ++ s.mem.readW (s.ea (at_ .eax 4)) 64)
        ((0 : BitVec 64) ++ s.mem.readW (s.ea (at_ .eax 4)) 64) := by
  simp only [runBlock_cons, exec, State.load64, h, Option.map_some, runStep_some, XOp.exec, ↓reduceIte,
    Option.some.injEq, exists_eq_left', runBlock_nil, xmm_setXmm, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm,
    mcdt_setXmm, true_and, and_true]
  intro r hr
  simp only [hr, ↓reduceIte]

/-- `modWords`: `M_1` and `M_2` (or `0`, for `N = 2`) in doublewords 0 and 2 of `xmm4`. -/
theorem modWords_ok {t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N mo : Nat} (hw : Ws t W L)
    (P : Params t W L V 12) (hN4 : (V pN4).toNat = 4 * N) (hM : (V pM).toNat = (W.toNat + mo) % 2 ^ 32)
    (hN2 : 2 ≤ N) (hmo : mo + 4 * N ≤ L) :
    WP isa modWords t fun u =>
      (dword (u.xmm .xmm4) 0).toNat = digits t.mem W mo 1 ∧
      (dword (u.xmm .xmm4) 2).toNat = (if 3 ≤ N then digits t.mem W mo 2 else 0) ∧
      Keeps [.eax] t u ∧ u.mem = t.mem ∧ u.mcdt = t.mcdt ∧ ∀ r, r ≠ .xmm4 → u.xmm r = t.xmm r := by
  unfold modWords
  refine WP.seq (wp_movX (P.read pN4 (by decide)) fun t1 u1 m1 x1 => wp_cmpX rfl fun t2 F2 c2 _ m2 x2 => ?_)
  obtain K2 : Sk [.eax] t t2 := (Sk.of_upd [.eax] u1 m1 x1).trans (Sk.of_fupd F2 m2 x2 [.eax])
  refine wp_movC (P.readSk K2 (i := pM) (by decide)) fun t3 u3 f3 m3 x3 => WP.block_nil ?_
  obtain K3 : Sk [.eax] t t3 := K2.trans (Sk.of_upd [.eax] u3 m3 x3)
  obtain hw3 := hw.of_keeps K3.keep
  obtain a3 : PtrAt t3 W .eax mo := ptr_of_param u3.gpr hM
  obtain cf3 : t3.cf = some (decide (N < 3)) := by
    rw [f3, c2, u1.gpr, hN4]
    show some (decide (4 * N < 12)) = _
    congr 1; exact decide_eq_decide.mpr (by omega_arith)
  by_cases h3 : 3 ≤ N
  · refine WP.ite true (by show t3.cf.map (!·) = _; rw [cf3, decide_eq_false (by omega_arith)]; rfl) (fun _ => ?_)
      (fun h => absurd h (by decide))
    obtain ea3 : t3.ea (at_ .eax 4) = off W (mo + 4) := ea_ptr hw3 a3 (by omega_arith)
    obtain ⟨u, run, g, mu, rdu, wru, mcu, oth, x4⟩ :=
      modLoad_run t3 (by rw [ea3]; exact ws_read hw3 (by omega_arith))
    refine WP.of_runBlock ⟨u, run, ?_, ?_, ?_, by rw [mu, K3.mem], by rw [mcu, K3.mcdt],
      fun r hr => by rw [oth r hr, K3.xmm]⟩
    · rw [x4, dword_unpack_0, readW64_lo, ea3, K3.mem]; rfl
    · rw [x4, dword_unpack_2, readW64_hi, ea3, off_4, K3.mem, ite_eq_left h3]; rfl
    · exact K3.keep.widen (rs := []) ⟨fun r _ => by rw [g], rdu, wru⟩
  · refine WP.ite false (by show t3.cf.map (!·) = _; rw [cf3, decide_eq_true (by omega_arith)]; rfl)
      (fun h => absurd h (by decide)) (fun _ => ?_)
    refine wp_movX (readSrc_ptr hw3 a3 (d := 4) (by omega_arith)) fun t4 u4 m4 x4 =>
      wp_xopX _ fun t5 g5 m5 rd5 wr5 mc5 x5 => WP.block_nil ?_
    obtain x45 : t5.xmm .xmm4 = (0 : BitVec 96) ++ t4.gpr .eax := by
      rw [x5]; simp only [XOp.exec, xmm_setXmm, ↓reduceIte]
    refine ⟨?_, ?_, ?_, by rw [m5, u4.mem, K3.mem], by rw [mc5, m4, K3.mcdt], fun r hr => ?_⟩
    · rw [x45, dword_movd_0, u4.gpr, K3.mem]; rfl
    · rw [x45, dword_movd_2, ite_eq_right h3]; rfl
    · exact (K3.keep.widen u4.keeps).widen (rs := []) ⟨fun r _ => by rw [g5], rd5, wr5⟩
    · rw [x5]; simp only [XOp.exec, xmm_setXmm, hr, ↓reduceIte]; rw [x4, K3.xmm]

theorem csum_window (q g : Nat → Nat) {N k : Nat} (hk : k < N) (q1 q2 m1 m2 : Nat)
    (hq1 : q1 = if 1 ≤ k then q (k - 1) else 0) (hq2 : q2 = if 2 ≤ k then q (k - 2) else 0)
    (hm1 : m1 = g 1) (hm2 : m2 = if 3 ≤ N then g 2 else 0) :
    csum q g k 0 (k - 2) + (q1 * m1 + q2 * m2) = Column.coeff (Column.prefixDigits q k) g N k := by
  rw [← csum_reduce0 q g hk]
  subst hq1 hq2 hm1 hm2
  by_cases h2 : 2 ≤ k
  · rw [csum_two q g h2, ite_eq_left (by omega_arith), ite_eq_left h2, ite_eq_left (by omega_arith)]; omega_arith
  · rw [ite_eq_right h2, Nat.zero_mul, Nat.add_zero]
    rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl
    · simp [csum]
    · simp [csum]

/-- The products of the quotient digits and `M` while `k < N`: those of the
digits stored before the two latest, then those in `xmm6`. -/
theorem reduceLo_ok {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S mo inv o a b P H n : Nat}
    {q : Nat → Nat} (C : ColEnv s W L V N k) (PV : PVals V W N S mo inv o a b) (hkN : k < N)
    (hm : mo + 4 * N ≤ L) (hs : S + 8 * N + 28 ≤ L) (RQ : RevQ s.mem W N S q 0 (k - 2))
    (Wd : Window s k q) (hN2 : 2 ≤ N) (hH : H + (N + 4) * 2 ^ 32 < 2 ^ 64)
    (A : Acc (s.xmm .xmm0) (s.xmm .xmm1) P H n) :
    WP isa (reduce false) s
      (RedPost s N (P + Column.coeff (Column.prefixDigits q k) (digits s.mem W mo) N k) H n) := by
  have hN := C.hN
  have hk := C.hk
  have hn := C.ws.nowrap
  simp only [reduce, Bool.false_eq_true, ↓reduceIte, seqs, ld, List.cons_append, List.nil_append, List.append_assoc]
  refine WP.seq (wp_movX rfl fun t1 u1 m1 x1 => wp_subX rfl fun t2 u2 c2 m2 x2 => WP.block_nil ?_)
  obtain K2 : Sk [.eax, .ebx, .esi, .edi, .ebp] s t2 := (Sk.of_upd [.eax, .ebx, .esi, .edi, .ebp] u1 m1 x1).trans
    (Sk.of_upd [.ebp] u2 m2 x2)
  obtain e1 : t1.gpr .ebp = BitVec.ofNat 32 (4 * k) := by rw [u1.gpr, C.ecx]
  refine WP.seq (WP.mono (Q := fun (t : State) => t.gpr .ebp = BitVec.ofNat 32 (4 * (k - 2)) ∧
    Sk [.eax, .ebx, .esi, .edi, .ebp] s t) ?_ fun t3 ⟨b3, K3⟩ => ?_)
  · by_cases h2 : k < 2
    · refine WP.ite false (by
          show t2.cf.map (!·) = _; rw [c2, e1, toNat_ofNat_lt (by omega_arith), decide_eq_true (by show 4 * k < 8; omega_arith)]
          rfl)
        (fun h => absurd h (by decide))
        (fun _ => wp_movX rfl fun t4 u4 m4 x4 => WP.block_nil ⟨?_, K2.trans (Sk.of_upd [.ebp] u4 m4 x4)⟩)
      rw [u4.gpr, show k - 2 = 0 by omega_arith]; rfl
    · refine WP.ite true (by
          show t2.cf.map (!·) = _; rw [c2, e1, toNat_ofNat_lt (by omega_arith), decide_eq_false (by show ¬ 4 * k < 8; omega_arith)]
          rfl)
        (fun _ => WP.block_nil ⟨?_, K2⟩) (fun h => absurd h (by decide))
      rw [u2.gpr, e1]; show _ - BitVec.ofNat 32 8 = _; rw [sub_ofNat (by omega_arith)]; congr 1; omega_arith
  refine WP.seq (ldW_ok (C.prm.of_sk K3) PV.s PV.n4 (r := .esi) (by decide) (by decide) 8 1 fun t4 e4 a4 K4 => ?_)
  obtain K4' := K3.trans (K4.mono [.eax, .ebx, .esi, .edi, .ebp])
  refine wp_subX rfl fun t5 u5 _ m5 x5 => wp_movX ((C.prm.of_sk K4').readSk (Sk.of_upd [.esi] u5 m5 x5)
    (i := pM) (by decide)) fun t6 u6 m6 x6 => wp_addX rfl fun t7 u7 _ m7 x7 => WP.block_nil ?_
  obtain K7 : Sk [.eax, .ebx, .esi, .edi, .ebp] s t7 := ((K4'.trans (Sk.of_upd [.esi] u5 m5 x5)).trans
    (Sk.of_upd [.edi] u6 m6 x6)).trans (Sk.of_upd [.edi] u7 m7 x7)
  obtain C7 := C.of_sk K7
  obtain c4 : t4.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [K4.keep.1 _ (by decide), K3.keep.1 _ (by decide), C.ecx]
  obtain esi7 : PtrAt t7 W .esi (S + 32 + 4 * N - 4 * k) := by
    rw [ptr_iff]; simp (disch := decide) only [u7.other, u6.other, u5.gpr, e4, c4]
    rw [sub_ofNat (by omega_arith)]; congr 1; omega_arith
  obtain edi7 : PtrAt t7 W .edi (mo + 12) := by
    rw [ptr_iff, u7.gpr, u6.gpr, pv_ofNat PV.mo]; show _ + BitVec.ofNat 32 12 = _; rw [ofNat_add3]; congr 1
  obtain ebp7 : t7.gpr .ebp = BitVec.ofNat 32 (4 * (k - 2)) := by
    simp (disch := decide) only [u7.other, u6.other, u5.other]; rw [K4.keep.1 _ (by decide), b3]
  -- The digits before the two latest.
  obtain hdot : WP isa dot t7 fun u =>
      Acc (u.xmm .xmm0) (u.xmm .xmm1) (P + csum q (digits s.mem W mo) k 0 (k - 2))
        (H + dhigh s.mem W (S + 32 + 4 * N - 4 * k) (mo + 12) (k - 2)) (n + (k - 2)) ∧
      Keeps [.eax, .ebx, .esi, .edi, .ebp] s u ∧ u.mem = s.mem ∧ u.mcdt = s.mcdt ∧
      u.xmm .xmm6 = s.xmm .xmm6 := by
    by_cases h2 : 2 ≤ k
    · have e7 : S + 32 + 4 * N - 4 * k = S + 24 + 4 * (N - (k - 2)) := by omega_arith
      obtain f7 : mo + 4 * (k + 1 - (k - 2)) = mo + 12 := by omega_arith
      obtain esi7' : PtrAt t7 W .esi (S + 24 + 4 * (N - (k - 2))) := by rw [← e7]; exact esi7
      obtain edi7' : PtrAt t7 W .edi (mo + 4 * (k + 1 - (k - 2))) := by rw [f7]; exact edi7
      refine WP.mono (dotRev_ok (xp := S + 24) (y := mo) (f := q) (i0 := 0) (P := P) (H := H) (n0 := n) C7 K7
        esi7' edi7' (by rw [ebp7, Nat.sub_zero]) (by omega_arith) (by omega_arith) (by omega_arith)
        (fun i _ h => RQ i (Nat.zero_le _) h) (.inr (by omega_arith)) (.inr (by omega_arith)) hH
        (by rw [K7.xmm]; exact A)) fun u ⟨Au, Ku, mu, cu, u6, _⟩ => ⟨?_, Ku, mu, cu, u6⟩
      rw [Nat.sub_zero, ← e7, f7] at Au; exact Au
    · refine WP.mono (dotAcc_ok (n := 0) (P := P) (H := H) (n0 := n) C7 esi7 edi7
        (by rw [ebp7, show k - 2 = 0 by omega_arith]) (.inl rfl) (.inl rfl)
        (Nat.zero_le _) (Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_right _
          (Nat.add_le_add_right (Nat.zero_le N) 4)) _) hH) (by rw [K7.xmm]; exact A)) fun u ⟨Au, Ku, mu, cu, u6⟩ => ?_
      rw [show k - 2 = 0 by omega_arith]
      refine ⟨by simpa only [dsum, dhigh, csum, rsum, NatSum.zero, Nat.add_zero] using Au, (K7.keep.mono (by decide)).trans (Ku.mono (by decide)), by rw [mu, K7.mem], by rw [cu, K7.mcdt],
        by rw [u6, K7.xmm]⟩
  refine WP.seq (WP.mono hdot fun u ⟨Au, Ku, mu, cu, u6⟩ => ?_)
  -- `M_1` and `M_2`, then the two latest digits' products.
  obtain Pu : Params u W L V 12 :=
    C.prm.keep (by rw [mu]; exact Outs.refl _ _ _) (Ku.1 _ (by decide)) Ku.2.1 Ku.2.2
  refine WP.seq (WP.mono (modWords_ok (C.ws.of_keeps Ku) Pu PV.n4 PV.mo hN2 hm)
    fun v ⟨v0, v2, Kv, mv, cv, xv⟩ => ?_)
  obtain ⟨w, run, g, mw, rdw, wrw, mcw, w6, a0, a1⟩ := window_run v (by rw [cv, cu]; exact C.mcdt)
  obtain hl := dhigh_le' s.mem W (S + 32 + 4 * N - 4 * k) (mo + 12) (k - 2)
  rw [← xv .xmm0 (by decide), ← xv .xmm1 (by decide)] at Au
  obtain Aw := Au.mul (v.xmm .xmm6) (v.xmm .xmm4) (by omega_arith)
  rw [← a0, ← a1, xv .xmm6 (by decide), u6, Nat.add_assoc,
    csum_window q (digits s.mem W mo) hkN _ _ _ _ Wd.q1 Wd.q2 (by rw [v0, mu]) (by rw [v2, mu])] at Aw
  refine WP.of_runBlock ⟨w, run, ⟨_, _, Aw, by omega_arith, ?_⟩,
    (Ku.widen Kv).widen (rs := []) ⟨fun r _ => by rw [g], rdw, wrw⟩, by rw [mw, mv, mu], by rw [mcw, cv, cu],
    by rw [w6, xv .xmm6 (by decide), u6]⟩
  have := Nat.div_lt_iff_lt_mul (k := 2 ^ 32) (x := (dword (s.xmm .xmm6) 0).toNat * (dword (v.xmm .xmm4) 0).toNat)
    (y := 2 ^ 32) (by decide) |>.2 (by have := word_mul_lt (dword (s.xmm .xmm6) 0) (dword (v.xmm .xmm4) 0); omega_arith)
  have := Nat.div_lt_iff_lt_mul (k := 2 ^ 32) (x := (dword (s.xmm .xmm6) 2).toNat * (dword (v.xmm .xmm4) 2).toNat)
    (y := 2 ^ 32) (by decide) |>.2 (by have := word_mul_lt (dword (s.xmm .xmm6) 2) (dword (v.xmm .xmm4) 2); omega_arith)
  omega_arith

end VG.Proof.Mont.X86.Sse2

end

end


/-! # A column's sums folded

`fold` adds each sum's two lanes, stores the column's sum modulo `2⁶⁴` at
`S` and its high words' sum `H` at `S + 8`, and adds the carry at `S + 16`:
`edx:eax = (P + c) mod 2⁶⁴` (`fold_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.X86.RegUpd VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt

/-! ## Scalar instructions, keeping `mcdt` and the XMM registers -/

section
variable {s : State} {is : List Instr} {Q : State → Prop}

theorem wp_adcX {d : Reg} {src : Src} {v : BitVec 32} {c : Bool} (h : readSrc s src = some v)
    (hc : s.cf = some c)
    (k : ∀ t, Upd s t d (s.gpr d + v + (BitVec.ofBool c).setWidth 32) →
      t.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat + c.toNat)) → t.mcdt = s.mcdt → t.xmm = s.xmm →
      WP isa (.block is) t Q) :
    WP isa (.block (.alu .adc d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some, hc, Option.map_some]; rfl)
    (k _ (Upd.flags _ _ _ _ _ _) rfl rfl rfl)

theorem wp_storeX {r : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hw : InRegions s.wr a 4)
    (k : ∀ t, Mupd s t (s.mem.writeW a (s.gpr r)) → t.mcdt = s.mcdt → t.xmm = s.xmm → WP isa (.block is) t Q) :
    WP isa (.block (.store m r :: is)) s Q :=
  cons (s' := { s with mem := s.mem.writeW a (s.gpr r) }) (by simp only [exec, ha, State.store32, hw, ite_true])
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl)

theorem wp_movqStoreX {x : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hw : InRegions s.wr a 8)
    (k : ∀ t, Mupd s t (s.mem.writeW a (qword (s.xmm x) 0)) → t.mcdt = s.mcdt → t.xmm = s.xmm →
      WP isa (.block is) t Q) :
    WP isa (.block (.movqStore m x :: is)) s Q :=
  cons (s' := { s with mem := s.mem.writeW a (qword (s.xmm x) 0) })
    (by simp only [exec, ha, State.store64, hw, ite_true]; rfl) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl)

theorem wp_mulX {r : Reg} (k : ∀ t, MulUpd s t r → t.mcdt = s.mcdt → t.xmm = s.xmm → WP isa (.block is) t Q) :
    WP isa (.block (.mul r :: is)) s Q := by
  refine cons (s' := execMul r s) rfl (k _ ⟨?_, ?_, fun q h1 h2 => ?_, rfl, rfl, rfl⟩ rfl rfl)
  · simp only [execMul, State.setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [execMul, State.setReg, ite_true]
  · simp only [execMul, State.setReg, State.setFlags, h1, h2, ite_false]

end

/-! ## Words of the scratch -/

/-- An 8-byte store's two words. -/
theorem w32_write64 (m : Mem) (W : Addr) (d : Nat) (v : BitVec 64) :
    w32 (m.writeW (off W d) v) W d + 2 ^ 32 * w32 (m.writeW (off W d) v) W (d + 4) = v.toNat := by
  rw [← word_eq_w32, word, Mem.readW_writeW_self64]


theorem fold_lane (x : BitVec 128) :
    qword (XBinOp.eval .paddq x (XShiftOp.eval .psrldq x 8)) 0 = qword x 0 + qword x 1 := by
  rw [qword_paddq _ _ (by decide), qword_psrldq_0]

/-- The sums' lanes added: `fold`'s SSE instructions. -/
theorem lanes_run (s : State) :
    ∃ t, runBlock isa [.xop (.bin .movdqa .xmm2 .xmm0), .xop (.shift .psrldq .xmm2 8),
      .xop (.bin .paddq .xmm0 .xmm2), .xop (.bin .movdqa .xmm2 .xmm1), .xop (.shift .psrldq .xmm2 8),
      .xop (.bin .paddq .xmm1 .xmm2)] s = some t ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mcdt = s.mcdt ∧
      t.xmm .xmm6 = s.xmm .xmm6 ∧
      qword (t.xmm .xmm0) 0 = qword (s.xmm .xmm0) 0 + qword (s.xmm .xmm0) 1 ∧
      qword (t.xmm .xmm1) 0 = qword (s.xmm .xmm1) 0 + qword (s.xmm .xmm1) 1 := by
  simp only [runBlock_cons, exec, runStep_some, runBlock_nil, XOp.exec, Option.some.injEq, exists_eq_left',
    xmm_setXmm, reduceCtorEq, ↓reduceIte, movdqa_eval, fold_lane, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm,
    mcdt_setXmm]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- `add` then `adc` of two-word numbers. -/
theorem add64_words (x0 x1 y0 y1 : BitVec 32) :
    (x0 + y0).toNat + 2 ^ 32 * (x1 + y1 + (BitVec.ofBool (decide (2 ^ 32 ≤ x0.toNat + y0.toNat))).setWidth 32).toNat =
      (x0.toNat + 2 ^ 32 * x1.toNat + (y0.toNat + 2 ^ 32 * y1.toNat)) % 2 ^ 64 := by
  rw [add3_toNat, BitVec.toNat_add]
  have := x0.isLt
  have := x1.isLt
  have := y0.isLt
  have := y1.isLt
  by_cases h : 2 ^ 32 ≤ x0.toNat + y0.toNat
  · simp only [h, decide_true, Bool.toNat_true]; omega_arith
  · simp only [h, decide_false, Bool.toNat_false]; omega_arith

/-- `fold`: the lanes added and stored, the column's sum `P` modulo `2⁶⁴` at
`S` and `H` at `S + 8`, and `edx:eax = (P + c) mod 2⁶⁴` for the carry `c`
at `S + 16`. -/
theorem fold_ok {t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S P H n c : Nat}
    (C : ColEnv t W L V N k) (hS : (V pS).toNat = (W.toNat + S) % 2 ^ 32) (hs : S + 24 ≤ L)
    (A : Acc (t.xmm .xmm0) (t.xmm .xmm1) P H n) (hH : H < 2 ^ 64)
    (hc : w32 t.mem W (S + 16) + 2 ^ 32 * w32 t.mem W (S + 20) = c) :
    WP isa (.block fold) t fun u =>
      (u.gpr .eax).toNat + 2 ^ 32 * (u.gpr .edx).toNat = (P + c) % 2 ^ 64 ∧ PtrAt u W .ebx S ∧
      w32 u.mem W (S + 8) + 2 ^ 32 * w32 u.mem W (S + 12) = H ∧
      w32 u.mem W (S + 16) + 2 ^ 32 * w32 u.mem W (S + 20) = c ∧
      Outs W [(S, 16)] t.mem u.mem ∧ Keeps [.eax, .ebx, .edx] t u ∧ u.mcdt = t.mcdt ∧
      u.xmm .xmm6 = t.xmm .xmm6 := by
  have hn := C.ws.nowrap
  obtain ⟨v, run, g, m, rd, wr, mc, v6, q0, q1⟩ := lanes_run t
  rw [show fold = [.xop (.bin .movdqa .xmm2 .xmm0), .xop (.shift .psrldq .xmm2 8),
      .xop (.bin .paddq .xmm0 .xmm2), .xop (.bin .movdqa .xmm2 .xmm1), .xop (.shift .psrldq .xmm2 8),
      .xop (.bin .paddq .xmm1 .xmm2)] ++ [.mov .ebx (.mem (kp pS)), .movqStore (at_ .ebx 0) .xmm0,
      .movqStore (at_ .ebx 8) .xmm1, .mov .eax (.mem (at_ .ebx 0)), .alu .add .eax (.mem (at_ .ebx 16)),
      .mov .edx (.mem (at_ .ebx 4)), .alu .adc .edx (.mem (at_ .ebx 20))] from rfl]
  refine WP.block_append (WP.of_runBlock ⟨v, run, ?_⟩)
  obtain Kv : Keeps [] t v := ⟨fun r _ => by rw [g], rd, wr⟩
  obtain Cv := C.of_keeps Kv m mc
  refine wp_movX (Cv.prm.read pS (by decide)) fun t1 u1 m1 x1 => ?_
  obtain p1 : PtrAt t1 W .ebx S := ptr_of_param u1.gpr hS
  obtain hw1 : Ws t1 W L := Cv.ws.of_keeps u1.keeps
  refine wp_movqStoreX (by rw [ea_ptr hw1 p1 (by omega_arith), Nat.add_zero]) (ws_write hw1 (y := S) (n := 8) (by omega_arith))
    fun t2 M2 m2 x2 => ?_
  obtain p2 : PtrAt t2 W .ebx S := by rw [PtrAt, M2.gpr]; exact p1
  obtain hw2 : Ws t2 W L := hw1.of_wr M2.wr
  refine wp_movqStoreX (ea_ptr hw2 p2 (by omega_arith)) (ws_write hw2 (y := S + 8) (n := 8) (by omega_arith))
    fun t3 M3 m3 x3 => ?_
  obtain p3 : PtrAt t3 W .ebx S := by rw [PtrAt, M3.gpr]; exact p2
  obtain hw3 : Ws t3 W L := hw2.of_wr M3.wr
  refine wp_movX (readSrc_ptr hw3 p3 (d := 0) (by omega_arith)) fun t4 u4 m4 x4 => ?_
  obtain p4 : PtrAt t4 W .ebx S := by rw [PtrAt, u4.other _ (by decide)]; exact p3
  obtain hw4 : Ws t4 W L := hw3.of_keeps u4.keeps
  refine wp_addX (readSrc_ptr hw4 p4 (d := 16) (by omega_arith)) fun t5 u5 c5 m5 x5 => ?_
  obtain p5 : PtrAt t5 W .ebx S := by rw [PtrAt, u5.other _ (by decide)]; exact p4
  obtain hw5 : Ws t5 W L := hw4.of_keeps u5.keeps
  refine wp_movC (readSrc_ptr hw5 p5 (d := 4) (by omega_arith)) fun t6 u6 f6 m6 x6 => ?_
  obtain p6 : PtrAt t6 W .ebx S := by rw [PtrAt, u6.other _ (by decide)]; exact p5
  obtain hw6 : Ws t6 W L := hw5.of_keeps u6.keeps
  refine wp_adcX (readSrc_ptr hw6 p6 (d := 20) (by omega_arith)) (by rw [f6, c5])
    fun t7 u7 c7 m7 x7 => WP.block_nil ?_
  obtain hP : qword (v.xmm .xmm0) 0 = BitVec.ofNat 64 P := by rw [q0, A.sums.low]
  obtain hHv : (qword (v.xmm .xmm1) 0).toNat = H := by
    rw [q1, BitVec.toNat_add, A.sums.high, Nat.mod_eq_of_lt hH]
  obtain mem2 : t2.mem = t.mem.writeW (off W S) (BitVec.ofNat 64 P) := by
    rw [M2.mem, x1, hP, u1.mem, m]
  obtain mem3 : t3.mem = t2.mem.writeW (off W (S + 8)) (qword (v.xmm .xmm1) 0) := by rw [M3.mem, x2, x1]
  obtain O2 : Outside W S 8 t.mem t2.mem := by rw [mem2]; exact writeW_outside _ _ _ (by omega_arith)
  obtain O3 : Outside W (S + 8) 8 t2.mem t3.mem := by rw [mem3]; exact writeW_outside _ _ _ (by omega_arith)
  obtain mem7 : t7.mem = t3.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem]
  obtain lo : w32 t3.mem W S + 2 ^ 32 * w32 t3.mem W (S + 4) = P % 2 ^ 64 := by
    rw [O3.w32 (by omega_arith) (by omega_arith), O3.w32 (by omega_arith) (by omega_arith), mem2, w32_write64, BitVec.toNat_ofNat]
  obtain hi : w32 t3.mem W (S + 8) + 2 ^ 32 * w32 t3.mem W (S + 12) = H := by
    rw [mem3, w32_write64, hHv]
  obtain cc : w32 t3.mem W (S + 16) + 2 ^ 32 * w32 t3.mem W (S + 20) = c := by
    rw [O3.w32 (by omega_arith) (by omega_arith), O3.w32 (by omega_arith) (by omega_arith), O2.w32 (by omega_arith) (by omega_arith),
      O2.w32 (by omega_arith) (by omega_arith), hc]
  refine ⟨?_, ?_, by rw [mem7]; exact hi, by rw [mem7]; exact cc, ?_, ?_, by rw [m7, m6, m5, m4, m3, m2, m1, mc],
    by rw [x7, x6, x5, x4, x3, x2, x1, v6]⟩
  · rw [u7.other _ (by decide), u7.gpr, u6.gpr, u6.other _ (by decide), u5.gpr, u4.gpr, add64_words]
    simp only [u6.mem, u5.mem, u4.mem, Nat.add_zero] at lo cc ⊢
    simp only [w32] at lo cc
    rw [lo, cc]
    omega_arith
  · rw [PtrAt, u7.other _ (by decide)]; exact p6
  · rw [mem7]
    exact (Outs.of_outside (O2.mono (by omega_arith) (by omega_arith)) (List.mem_singleton_self _)).trans
      (Outs.of_outside (O3.mono (by omega_arith) (by omega_arith)) (List.mem_singleton_self _))
  · refine ⟨fun r hr => ?_, by rw [u7.rd, u6.rd, u5.rd, u4.rd, M3.rd, M2.rd, u1.rd, rd],
      by rw [u7.wr, u6.wr, u5.wr, u4.wr, M3.wr, M2.wr, u1.wr, wr]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u7.other _ hr.2.2, u6.other _ hr.2.2, u5.other _ hr.1, u4.other _ hr.1, M3.gpr, M2.gpr, u1.other _ hr.2.1, g]

/-! ## The column's digit -/

/-- `adc` of a word, its carry from an `add`. -/
theorem add_adc (x0 y0 x1 y1 : BitVec 32) :
    (x0 + y0).toNat + 2 ^ 32 * (x1 + y1 + (BitVec.ofBool (decide (2 ^ 32 ≤ x0.toNat + y0.toNat))).setWidth 32).toNat =
      (x0.toNat + y0.toNat + 2 ^ 32 * (x1.toNat + y1.toNat)) % 2 ^ 64 := by
  rw [add64_words]; congr 1; omega_arith

/-- `punpcklqdq`'s doublewords 0 and 2: those of the low quadwords of its operands. -/
theorem dword_punpcklqdq_0 (a b : BitVec 128) : dword (XBinOp.eval .punpcklqdq a b) 0 = dword a 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_dword, getLsbD_dword]
  show (decide (i < 32) && (qword b 0 ++ qword a 0).getLsbD (32 * 0 + i)) = _
  rw [BitVec.getLsbD_append, getLsbD_qword]
  simp only [Nat.mul_zero, Nat.zero_add, show i < 64 by omega_arith, decide_true, Bool.true_and, ↓reduceIte]
theorem dword_punpcklqdq_2 (a b : BitVec 128) : dword (XBinOp.eval .punpcklqdq a b) 2 = dword b 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_dword, getLsbD_dword]
  show (decide (i < 32) && (qword b 0 ++ qword a 0).getLsbD (32 * 2 + i)) = _
  rw [BitVec.getLsbD_append, getLsbD_qword]
  simp only [show ¬ 32 * 2 + i < 64 by omega_arith, ↓reduceIte, show 32 * 2 + i - 64 = i by omega_arith, getLsbD_qword,
    Nat.mul_zero, Nat.zero_add, show i < 64 by omega_arith, decide_true, Bool.true_and]

/-- The digit into `xmm6`, the latest of the window. -/
theorem win_run (s : State) :
    ∃ t, runBlock isa [.xop (.movd .xmm1 .eax), .xop (.bin .punpcklqdq .xmm1 .xmm6), .xop (.bin .movdqa .xmm6 .xmm1)]
        s = some t ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mcdt = s.mcdt ∧ t.cf = s.cf ∧
      t.xmm .xmm6 = XBinOp.eval .punpcklqdq ((0 : BitVec 96) ++ s.gpr .eax) (s.xmm .xmm6) := by
  simp only [runBlock_cons, exec, runStep_some, runBlock_nil, XOp.exec, Option.some.injEq, exists_eq_left',
    xmm_setXmm, reduceCtorEq, ↓reduceIte, movdqa_eval, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm,
    mcdt_setXmm, cf_setXmm]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- `k < N`: the digit `q = Z_lo (-M⁻¹) mod 2³²` stored at word `N - 1 - k`
and into `xmm6` (doubleword 0, the previous one moving to doubleword 2) through `xmm1`, `q M_0`
added to `Z` (`edx` its high word) and its high word to `H` at `S + 8`. -/
theorem digit_ok {t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S mo inv Z H : Nat}
    (hw : Ws t W L) (P : Params t W L V 12) (hcx : t.gpr .ecx = BitVec.ofNat 32 (4 * k)) (hkN : k < N)
    (hN4 : (V pN4).toNat = 4 * N)
    (hM : (V pM).toNat = (W.toNat + mo) % 2 ^ 32) (hI : (V pInv).toNat = (W.toNat + inv) % 2 ^ 32)
    (hs : S + 24 + 4 * N ≤ L) (hm : mo + 4 ≤ L) (hi : inv + 4 ≤ L)
    (sep : mo + 4 ≤ S + 24 + 4 * (N - 1 - k) ∨ S + 24 + 4 * (N - 1 - k) + 4 ≤ mo)
    (hb : PtrAt t W .ebx S) (hz : (t.gpr .eax).toNat + 2 ^ 32 * (t.gpr .edx).toNat = Z)
    (hH : w32 t.mem W (S + 8) + 2 ^ 32 * w32 t.mem W (S + 12) = H) :
    WP isa (.block digit) t fun u =>
      (u.gpr .edx).toNat = (Z + (Z % 2 ^ 32 * w32 t.mem W inv) % 2 ^ 32 * w32 t.mem W mo) % 2 ^ 64 / 2 ^ 32 ∧
      w32 u.mem W (S + 24 + 4 * (N - 1 - k)) = (Z % 2 ^ 32 * w32 t.mem W inv) % 2 ^ 32 ∧
      w32 u.mem W (S + 8) + 2 ^ 32 * w32 u.mem W (S + 12) =
        (H + (Z % 2 ^ 32 * w32 t.mem W inv) % 2 ^ 32 * w32 t.mem W mo / 2 ^ 32) % 2 ^ 64 ∧
      Outs W [(S + 8, 8), (S + 24 + 4 * (N - 1 - k), 4)] t.mem u.mem ∧
      Keeps [.eax, .edx, .esi, .edi] t u ∧ u.mcdt = t.mcdt ∧
      (dword (u.xmm .xmm6) 0).toNat = (Z % 2 ^ 32 * w32 t.mem W inv) % 2 ^ 32 ∧
      dword (u.xmm .xmm6) 2 = dword (t.xmm .xmm6) 0 := by
  have hn := hw.nowrap
  rw [show digit = [.mov .esi (.reg .edx), .mov .edi (.reg .eax),
    .mov .edx (.mem (kp pInv)), .mov .edx (.mem (at_ .edx 0)), .mul .edx,
    .mov .edx (.mem (kp pN4)), .alu .add .edx (.reg .ebx), .alu .sub .edx (.reg .ecx),
    .store (at_ .edx 20) .eax] ++ [.xop (.movd .xmm1 .eax), .xop (.bin .punpcklqdq .xmm1 .xmm6),
      .xop (.bin .movdqa .xmm6 .xmm1)] ++
    [.mov .edx (.mem (kp pM)), .mov .edx (.mem (at_ .edx 0)), .mul .edx,
    .alu .add .eax (.reg .edi), .alu .adc .esi (.reg .edx),
    .mov .eax (.mem (at_ .ebx 8)), .alu .add .eax (.reg .edx), .store (at_ .ebx 8) .eax,
    .mov .eax (.mem (at_ .ebx 12)), .alu .adc .eax (.imm 0), .store (at_ .ebx 12) .eax,
    .mov .edx (.reg .esi)] from rfl, List.append_assoc]
  refine WP.block_append ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_movX rfl fun t1 u1 m1 x1 => wp_movX rfl fun t2 u2 m2 x2 => ?_
  obtain K2 : Sk [.eax, .edx, .esi, .edi] t t2 :=
    (Sk.of_upd [.eax, .edx, .esi, .edi] u1 m1 x1).trans (Sk.of_upd [.edi] u2 m2 x2)
  refine wp_movX (P.readSk K2 (i := pInv) (by decide)) fun t3 u3 m3 x3 => ?_
  obtain K3 := K2.trans (Sk.of_upd [.edx] u3 m3 x3)
  obtain hw3 := hw.of_keeps K3.keep
  refine wp_movX (readSrc_ptr hw3 (ptr_of_param u3.gpr hI) (d := 0) (by omega_arith)) fun t4 u4 m4 x4 => ?_
  obtain K4 := K3.trans (Sk.of_upd [.edx] u4 m4 x4)
  refine wp_mulX fun t5 u5 m5 x5 => ?_
  obtain K5 : Sk [.eax, .edx, .esi, .edi] t t5 := K4.trans ⟨u5.keeps, u5.mem, m5, x5⟩
  refine wp_movX (P.readSk K5 (i := pN4) (by decide)) fun t6 u6 m6 x6 => wp_addX rfl fun t6b u6b _ m6b x6b =>
    wp_subX rfl fun t7 u7 _ m7 x7 => ?_
  obtain K7 := ((K5.trans (Sk.of_upd [.edx] u6 m6 x6)).trans (Sk.of_upd [.edx] u6b m6b x6b)).trans
    (Sk.of_upd [.edx] u7 m7 x7)
  obtain hw7 := hw.of_keeps K7.keep
  obtain p7 : PtrAt t7 W .edx (S + 4 * N - 4 * k) := by
    obtain ebx5 : t5.gpr .ebx = BitVec.ofNat 32 (W.toNat + S) := by
      rw [K5.keep.1 _ (by decide)]; exact ptr_iff.mp hb
    obtain ecx5 : t5.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [K5.keep.1 _ (by decide), hcx]
    rw [ptr_iff, u7.gpr, u6b.gpr, u6.gpr, u6b.other _ (by decide), u6.other _ (by decide), u6.other _ (by decide),
      ebx5, ecx5, ofNat_of_toNat hN4, ofNat_add3, sub_ofNat (by omega_arith)]
    congr 1; omega_arith
  obtain ea8 : t7.ea (at_ .edx 20) = off W (S + 24 + 4 * (N - 1 - k)) := by
    rw [ea_ptr hw7 p7 (by omega_arith)]; congr 1; omega_arith
  refine wp_storeX ea8 (ws_write hw7 (y := S + 24 + 4 * (N - 1 - k)) (n := 4) (by omega_arith))
    fun t8 M8 m8 x8 => WP.block_nil ?_
  obtain O8 : Outside W (S + 24 + 4 * (N - 1 - k)) 4 t.mem t8.mem := by
    rw [M8.mem, K7.mem]; exact writeW32_outside _ _ _ (by omega_arith)
  obtain Ot8 : Outs W [(0, L)] t.mem t8.mem := Outs.of_outside (O8.mono (by omega_arith) (by omega_arith)) (List.mem_singleton_self _)
  obtain K8k : Keeps [.eax, .edx, .esi, .edi] t t8 := K7.keep.trans (M8.keeps _)
  obtain P8 : Params t8 W L V 12 := P.keep Ot8 (K8k.1 _ (by decide)) K8k.2.1 K8k.2.2
  -- The window.
  obtain ⟨w, wrun, gw, mw, rdw, wrw, mcw, cfw, w6⟩ := win_run t8
  refine WP.block_append (WP.of_runBlock ⟨w, wrun, ?_⟩)
  obtain Kw : Keeps [.eax, .edx, .esi, .edi] t w := K8k.trans ⟨fun r _ => by rw [gw], rdw, wrw⟩
  obtain Pw : Params w W L V 12 := P8.keep (by rw [mw]; exact Outs.refl _ _ _) (by rw [gw]) rdw wrw
  obtain hww := hw.of_keeps Kw
  refine wp_movX (Pw.read pM (by decide)) fun t9 u9 m9 x9 => ?_
  obtain hw9 := hww.of_keeps u9.keeps
  refine wp_movX (readSrc_ptr hw9 (ptr_of_param u9.gpr hM) (d := 0) (by omega_arith)) fun t10 u10 m10 x10 => ?_
  refine wp_mulX fun t11 u11 m11 x11 => wp_addX rfl fun t12 u12 c12 m12 x12 => ?_
  refine wp_adcX rfl c12 fun t13 u13 _ m13 x13 => ?_
  obtain K13 : Keeps [.eax, .edx, .esi, .edi] t t13 :=
    ((((Kw.widen u9.keeps).widen u10.keeps).widen u11.keeps).widen u12.keeps).widen u13.keeps
  obtain hw13 := hw.of_keeps K13
  obtain b13 : PtrAt t13 W .ebx S := by rw [PtrAt, K13.1 _ (by decide)]; exact hb
  obtain mem13 : t13.mem = t8.mem := by rw [u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, mw]
  refine wp_movC (readSrc_ptr hw13 b13 (d := 8) (by omega_arith)) fun t14 u14 f14 m14 x14 =>
    wp_addX rfl fun t15 u15 c15 m15 x15 => ?_
  obtain K15 : Keeps [.eax, .edx, .esi, .edi] t t15 := (K13.widen u14.keeps).widen u15.keeps
  obtain hw15 := hw.of_keeps K15
  obtain b15 : PtrAt t15 W .ebx S := by rw [PtrAt, K15.1 _ (by decide)]; exact hb
  refine wp_storeX (ea_ptr hw15 b15 (d := 8) (by omega_arith)) (ws_write hw15 (y := S + 8) (n := 4) (by omega_arith))
    fun t16 M16 m16 x16 => ?_
  obtain hw16 := hw15.of_wr M16.wr
  obtain b16 : PtrAt t16 W .ebx S := by rw [PtrAt, M16.gpr]; exact b15
  refine wp_movC (readSrc_ptr hw16 b16 (d := 12) (by omega_arith)) fun t17 u17 f17 m17 x17 =>
    wp_adcX rfl (by rw [f17, M16.cf, c15]) fun t18 u18 _ m18 x18 => ?_
  obtain K18 : Keeps [.eax, .edx, .esi, .edi] t t18 := ((K15.widen (M16.keeps [])).widen u17.keeps).widen u18.keeps
  obtain hw18 := hw.of_keeps K18
  obtain b18 : PtrAt t18 W .ebx S := by rw [PtrAt, K18.1 _ (by decide)]; exact hb
  refine wp_storeX (ea_ptr hw18 b18 (d := 12) (by omega_arith)) (ws_write hw18 (y := S + 12) (n := 4) (by omega_arith))
    fun t19 M19 m19 x19 => wp_movX rfl fun t20 u20 m20 x20 => WP.block_nil ?_
  -- The values.
  obtain ezl : (t.gpr .eax).toNat = Z % 2 ^ 32 := by have := (t.gpr .eax).isLt; omega_arith
  obtain iv : (t4.gpr .edx).toNat = w32 t.mem W inv := by
    rw [u4.gpr, K3.mem, Nat.add_zero]
  obtain q5 : (t5.gpr .eax).toNat = (Z % 2 ^ 32 * w32 t.mem W inv) % 2 ^ 32 := by
    rw [u5.eax, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide),
      BitVec.toNat_ofNat, ezl, iv]
  obtain m0 : (t10.gpr .edx).toNat = w32 t.mem W mo := by
    rw [u10.gpr, u9.mem, mw, M8.mem]
    simp only [Nat.add_zero]
    have := O8.w32 (d := mo) (by omega_arith) (by omega_arith)
    rw [M8.mem] at this
    simp only [w32] at this
    rw [this]
  obtain e8 : t8.gpr .eax = t5.gpr .eax := by
    rw [M8.gpr, u7.other _ (by decide), u6b.other _ (by decide), u6.other _ (by decide)]
  obtain e11 : t10.gpr .eax = t5.gpr .eax := by
    rw [u10.other _ (by decide), u9.other _ (by decide), gw, e8]
  obtain mw' := mul_words (t10.gpr .eax) (t10.gpr .edx)
  rw [← u11.eax, ← u11.edx] at mw'
  obtain zl12 : t11.gpr .edi = t.gpr .eax := by
    rw [u11.other _ (by decide) (by decide), u10.other _ (by decide), u9.other _ (by decide), gw, M8.gpr,
      u7.other _ (by decide), u6b.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide) (by decide),
      u4.other _ (by decide), u3.other _ (by decide), u2.gpr, u1.other _ (by decide)]
  obtain zh12 : t12.gpr .esi = t.gpr .edx := by
    rw [u12.other _ (by decide), u11.other _ (by decide) (by decide), u10.other _ (by decide),
      u9.other _ (by decide), gw, M8.gpr, u7.other _ (by decide), u6b.other _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide) (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.gpr]
  obtain hi12 : t12.gpr .edx = t11.gpr .edx := u12.other _ (by decide)
  obtain sum := add_adc (t11.gpr .eax) (t11.gpr .edi) (t12.gpr .esi) (t12.gpr .edx)
  rw [← u12.gpr, ← u13.gpr] at sum
  rw [zl12, zh12, hi12] at sum
  rw [e11] at mw'
  have q10 : (t10.gpr .edx).toNat = w32 t.mem W mo := m0
  rw [q5, q10] at mw'
  -- Memory.
  obtain mem8 : t8.mem = t.mem.writeW (off W (S + 24 + 4 * (N - 1 - k))) (t5.gpr .eax) := by
    rw [M8.mem, K7.mem, u7.other _ (by decide), u6b.other _ (by decide), u6.other _ (by decide)]
  obtain mem16 : t16.mem = t8.mem.writeW (off W (S + 8)) (t15.gpr .eax) := by
    rw [M16.mem, u15.mem, u14.mem, mem13]
  obtain mem20 : t20.mem = t16.mem.writeW (off W (S + 12)) (t18.gpr .eax) := by
    rw [u20.mem, M19.mem, u18.mem, u17.mem]
  obtain esi20 : t20.gpr .edx = t13.gpr .esi := by
    rw [u20.gpr, M19.gpr, u18.other _ (by decide), u17.other _ (by decide), M16.gpr, u15.other _ (by decide),
      u14.other _ (by decide)]
  obtain hlo : (t14.gpr .eax).toNat = w32 t.mem W (S + 8) := by
    rw [u14.gpr, mem13, mem8]
    exact w32_write_ne (size := L) (o := S + 24 + 4 * (N - 1 - k)) (d := S + 8) hn (by omega_arith) (by omega_arith)
      (by omega_arith) _
  obtain hhi : (t17.gpr .eax).toNat = w32 t.mem W (S + 12) := by
    rw [u17.gpr, mem16, mem8]
    exact (w32_write_ne (size := L) (o := S + 8) (d := S + 12) hn (by omega_arith) (by omega_arith) (by omega_arith) _).trans
      (w32_write_ne (size := L) (o := S + 24 + 4 * (N - 1 - k)) (d := S + 12) hn (by omega_arith) (by omega_arith)
        (by omega_arith) _)
  obtain e14 : t14.gpr .edx = t11.gpr .edx := by
    rw [u14.other _ (by decide), u13.other _ (by decide), hi12]
  obtain hsum := add_adc (t14.gpr .eax) (t14.gpr .edx) (t17.gpr .eax) 0
  rw [← u15.gpr, ← u18.gpr, hlo, hhi, e14] at hsum
  obtain hz13 := (t12.gpr .eax).isLt
  obtain x20 : t20.xmm = w.xmm := by
    rw [x20, x19, x18, x17, x16, x15, x14, x13, x12, x11, x10, x9]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [esi20]
    have := mw'.1
    omega_arith
  · rw [mem20, w32_write_ne (size := L) (o := S + 12) (d := S + 24 + 4 * (N - 1 - k)) hn (by omega_arith)
      (by omega_arith) (by omega_arith),
      mem16, w32_write_ne (size := L) (o := S + 8) (d := S + 24 + 4 * (N - 1 - k)) hn (by omega_arith) (by omega_arith)
        (by omega_arith), mem8, w32_write_self, q5]
  · rw [mem20, w32_write_ne (size := L) (o := S + 12) (d := S + 8) hn (by omega_arith) (by omega_arith) (by omega_arith),
      w32_write_self, mem16, w32_write_self]
    have := mw'.1
    have z0 : (0 : BitVec 32).toNat = 0 := rfl
    rw [z0, Nat.add_zero] at hsum
    omega_arith
  · rw [mem20, mem16]
    obtain O16 : Outside W (S + 8) 4 t8.mem (t8.mem.writeW (off W (S + 8)) (t15.gpr .eax)) :=
      writeW32_outside _ _ _ (by omega_arith)
    obtain O20 : Outside W (S + 12) 4 (t8.mem.writeW (off W (S + 8)) (t15.gpr .eax))
        ((t8.mem.writeW (off W (S + 8)) (t15.gpr .eax)).writeW (off W (S + 12)) (t18.gpr .eax)) :=
      writeW32_outside _ _ _ (by omega_arith)
    exact ((Outs.of_outside O8 (by simp)).trans
      (Outs.of_outside (O16.mono (o' := S + 8) (n' := 8) (by omega_arith) (by omega_arith)) (by simp))).trans
      (Outs.of_outside (O20.mono (o' := S + 8) (n' := 8) (by omega_arith) (by omega_arith)) (by simp))
  · exact (K18.widen (M19.keeps [])).widen u20.keeps
  · rw [m20, m19, m18, m17, m16, m15, m14, m13, m12, m11, m10, m9, mcw, m8, m7, m6b, m6, m5, m4, m3, m2, m1]
  · rw [x20, w6, dword_punpcklqdq_0, dword_movd_0, e8, q5]
  · rw [x20, w6, dword_punpcklqdq_2, x8, x7, x6b, x6, x5, x4, x3, x2, x1]

/-- `k ≥ N`: `Z_lo` stored at word `2 N - 1 - k`, over the dead digit `Q_(k-N)`. -/
theorem word_ok {t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S : Nat} (hw : Ws t W L)
    (P : Params t W L V 12) (hN4 : (V pN4).toNat = 4 * N)
    (hcx : t.gpr .ecx = BitVec.ofNat 32 (4 * k)) (hk : k < 2 * N) (hs : S + 24 + 8 * N ≤ L)
    (hb : PtrAt t W .ebx S) :
    WP isa (.block VG.Impl.Mont.X86.Sse2.word) t fun u =>
      w32 u.mem W (S + 24 + 4 * (2 * N - 1 - k)) = (t.gpr .eax).toNat ∧
      Outs W [(S + 24 + 4 * (2 * N - 1 - k), 4)] t.mem u.mem ∧
      Keeps [.esi] t u ∧ u.mcdt = t.mcdt ∧ u.xmm = t.xmm := by
  have hn := hw.nowrap
  unfold VG.Impl.Mont.X86.Sse2.word
  simp only [offW]
  refine wp_movX (P.read pN4 (by decide)) fun t1 u1 m1 x1 => wp_addX rfl fun t2 u2 _ m2 x2 =>
    wp_addX rfl fun t3 u3 _ m3 x3 => wp_subX rfl fun t4 u4 _ m4 x4 => ?_
  obtain K4 : Keeps [.esi] t t4 := ((u1.keeps.widen u2.keeps).widen u3.keeps).widen u4.keeps
  obtain hw4 := hw.of_keeps K4
  obtain p4 : PtrAt t4 W .esi (S + 8 * N - 4 * k) := by
    obtain ebx0 : t.gpr .ebx = BitVec.ofNat 32 (W.toNat + S) := ptr_iff.mp hb
    rw [ptr_iff]
    simp (disch := decide) only [u4.gpr, u3.gpr, u2.gpr, u1.gpr, u3.other, u2.other, u1.other, ebx0, hcx,
      ofNat_of_toNat hN4]
    rw [ofNat_add3, ofNat_add3, sub_ofNat (by omega_arith)]
    congr 1; omega_arith
  obtain ea : t4.ea (at_ .esi 20) = off W (S + 24 + 4 * (2 * N - 1 - k)) := by
    rw [ea_ptr hw4 p4 (by omega_arith)]; congr 1; omega_arith
  refine wp_storeX ea (ws_write hw4 (y := S + 24 + 4 * (2 * N - 1 - k)) (n := 4) (by omega_arith))
    fun t5 M5 m5 x5 => WP.block_nil ⟨?_, ?_, K4.widen (M5.keeps []), by rw [m5, m4, m3, m2, m1],
      by rw [x5, x4, x3, x2, x1]⟩
  · rw [M5.mem, w32_write_self, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide)]
  · rw [M5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    exact Outs.of_outside (writeW32_outside _ _ _ (by omega_arith)) (by simp)

/-- The carry stored: its low word `edx`, its high word `H_hi + [edx < H_lo]`. -/
theorem carry_ok {t : State} {W : Addr} {L : Nat} {S : Nat} (hw : Ws t W L) (hs : S + 24 ≤ L)
    (hb : PtrAt t W .ebx S) :
    WP isa (.block carry) t fun u =>
      w32 u.mem W (S + 16) = (t.gpr .edx).toNat ∧
      w32 u.mem W (S + 20) = (w32 t.mem W (S + 12) +
        (decide ((t.gpr .edx).toNat < w32 t.mem W (S + 8))).toNat) % 2 ^ 32 ∧
      Outs W [(S + 16, 8)] t.mem u.mem ∧ Keeps [.eax] t u ∧ u.mcdt = t.mcdt ∧ u.xmm = t.xmm := by
  have hn := hw.nowrap
  unfold carry
  refine wp_storeX (ea_ptr hw hb (d := 16) (by omega_arith)) (ws_write hw (y := S + 16) (n := 4) (by omega_arith))
    fun t1 M1 m1 x1 => ?_
  obtain hw1 := hw.of_wr M1.wr
  obtain b1 : PtrAt t1 W .ebx S := by rw [PtrAt, M1.gpr]; exact hb
  refine wp_cmpX (readSrc_ptr hw1 b1 (d := 8) (by omega_arith)) fun t2 f2 c2 _ m2 x2 => ?_
  obtain b2 : PtrAt t2 W .ebx S := by rw [PtrAt, f2.gpr]; exact b1
  obtain hw2 := hw1.of_wr f2.wr
  refine wp_movC (readSrc_ptr hw2 b2 (d := 12) (by omega_arith)) fun t3 u3 f3 m3 x3 =>
    wp_adcX rfl (by rw [f3, c2]) fun t4 u4 _ m4 x4 => ?_
  obtain K4 : Keeps [.eax] t t4 := (((M1.keeps [.eax]).widen (f2.keeps [])).widen u3.keeps).widen u4.keeps
  obtain hw4 := hw.of_keeps K4
  obtain b4 : PtrAt t4 W .ebx S := by rw [PtrAt, K4.1 _ (by decide)]; exact hb
  refine wp_storeX (ea_ptr hw4 b4 (d := 20) (by omega_arith)) (ws_write hw4 (y := S + 20) (n := 4) (by omega_arith))
    fun t5 M5 m5 x5 => WP.block_nil ?_
  obtain K5 : Keeps [.eax] t t5 := K4.widen (M5.keeps [])
  obtain O1 : Outside W (S + 16) 4 t.mem t1.mem := by rw [M1.mem]; exact writeW32_outside _ _ _ (by omega_arith)
  obtain mem5 : t5.mem = t1.mem.writeW (off W (S + 20)) (t4.gpr .eax) := by
    rw [M5.mem, u4.mem, u3.mem, f2.mem]
  obtain O5 : Outside W (S + 20) 4 t1.mem t5.mem := by rw [mem5]; exact writeW32_outside _ _ _ (by omega_arith)
  refine ⟨?_, ?_, ?_, K5, by rw [m5, m4, m3, m2, m1], by rw [x5, x4, x3, x2, x1]⟩
  · rw [mem5, w32_write_ne (size := L) (o := S + 20) (d := S + 16) hn (by omega_arith) (by omega_arith) (by omega_arith),
      M1.mem, w32_write_self]
  · have r12 : (t1.mem.readW (off W (S + 12)) 32).toNat = w32 t.mem W (S + 12) := by
      rw [M1.mem]; exact w32_write_ne (size := L) (o := S + 16) (d := S + 12) hn (by omega_arith) (by omega_arith) (by omega_arith) _
    obtain r8 : (t1.mem.readW (off W (S + 8)) 32).toNat = w32 t.mem W (S + 8) := by
      rw [M1.mem]; exact w32_write_ne (size := L) (o := S + 16) (d := S + 8) hn (by omega_arith) (by omega_arith) (by omega_arith) _
    rw [mem5, w32_write_self, u4.gpr, add3_toNat, u3.gpr, f2.mem,
      show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, r12, r8, M1.gpr]
  · exact (Outs.of_outside (O1.mono (o' := S + 16) (n' := 8) (by omega_arith) (by omega_arith)) (by simp)).trans
      (Outs.of_outside (O5.mono (o' := S + 16) (n' := 8) (by omega_arith) (by omega_arith)) (by simp))

/-- `ecx` up a word; ZF after the last column of the phase. -/
theorem step_ok {t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k : Nat} (P : Params t W L V 12)
    (hN : (V pN4).toNat = 4 * N) (hcx : t.gpr .ecx = BitVec.ofNat 32 (4 * k)) (hk : k < 2 * N)
    (hN28 : N < 2 ^ 29) (hi : Bool) :
    WP isa (.block (([.alu .add .ecx (.imm 4), .mov .eax (.mem (kp pN4))] : List Instr) ++
      ((if hi then ([.alu .add .eax (.reg .eax)] : List Instr) else []) ++ ([.alu .cmp .ecx (.reg .eax)] : List Instr)))) t fun u =>
      u.gpr .ecx = BitVec.ofNat 32 (4 * (k + 1)) ∧ u.zf = some (decide (k + 1 = if hi then 2 * N else N)) ∧
      Keeps [.eax, .ecx] t u ∧ u.mem = t.mem ∧ u.mcdt = t.mcdt ∧ u.xmm = t.xmm := by
  obtain hv := (V pN4).isLt
  refine wp_addX rfl fun t6 u6 _ m6 x6 => wp_movX (P.readSk (Sk.of_upd [.ecx] u6 m6 x6) (i := pN4) (by decide))
    fun t7 u7 m7 x7 => ?_
  obtain ecx7 : t7.gpr .ecx = BitVec.ofNat 32 (4 * (k + 1)) := by
    rw [u7.other _ (by decide), u6.gpr, hcx]
    apply ofNat_of_toNat
    rw [BitVec.toNat_add, toNat_ofNat_lt (by omega_arith), show (4 : BitVec 32).toNat = 4 from rfl]
    omega_arith
  obtain K7 : Keeps [.eax, .ecx] t t7 := (u6.keeps.mono (by decide)).widen u7.keeps
  cases hi with
  | false =>
    refine wp_cmpX rfl fun t9 f9 _ z9 m9 x9 => WP.block_nil ⟨by rw [f9.gpr, ecx7], ?_, K7.widen (f9.keeps []),
      by rw [f9.mem, u7.mem, u6.mem], by rw [m9, m7, m6], by rw [x9, x7, x6]⟩
    rw [z9, ecx7, u7.gpr, ofNat_of_toNat hN, sub_beq (by omega_arith) (by omega_arith)]
    exact congrArg some (decide_eq_decide.mpr (by simp only [Bool.false_eq_true, ↓reduceIte]; omega_arith))
  | true =>
    refine wp_addX rfl fun t8 u8 _ m8 x8 => wp_cmpX rfl fun t9 f9 _ z9 m9 x9 => WP.block_nil ⟨?_, ?_,
      (K7.widen u8.keeps).widen (f9.keeps []), by rw [f9.mem, u8.mem, u7.mem, u6.mem], by rw [m9, m8, m7, m6],
      by rw [x9, x8, x7, x6]⟩
    · rw [f9.gpr, u8.other _ (by decide), ecx7]
    · rw [z9, u8.other _ (by decide), ecx7, u8.gpr, u7.gpr, ofNat_of_toNat hN, ← BitVec.ofNat_add,
        sub_beq (by omega_arith) (by omega_arith)]
      exact congrArg some (decide_eq_decide.mpr (by simp only [↓reduceIte]; omega_arith))

end VG.Proof.Mont.X86.Sse2

end

end

/-! ### `Mont.X86.Sse2.CarryMath`, which only this module used -/

section

/-! # A column's carry, from its sums

For a column `V = 2³² H + L + c` (the products' high words `H`, their low
words `L` and the incoming carry `c`, with `L + c < 2⁶⁴`), the word
`Z_hi` of `V mod 2⁶⁴` and the comparison `Z_hi < H mod 2³²` give the
outgoing carry `V / 2³²` (`carry_eq`). The quotient digit cancels the
column's low word (`cancel_digit`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2

theorem carry_eq (H L c : Nat) (hL : L + c < 2 ^ 64) (hV : (2 ^ 32 * H + L + c) / 2 ^ 32 < 2 ^ 64) :
    (2 ^ 32 * H + L + c) % 2 ^ 64 / 2 ^ 32 + 2 ^ 32 * ((H / 2 ^ 32 +
      (decide ((2 ^ 32 * H + L + c) % 2 ^ 64 / 2 ^ 32 < H % 2 ^ 32)).toNat) % 2 ^ 32) =
      (2 ^ 32 * H + L + c) / 2 ^ 32 := by
  obtain e1 : (2 ^ 32 * H + L + c) / 2 ^ 32 = H + (L + c) / 2 ^ 32 := by omega_using []
  obtain e2 : (2 ^ 32 * H + L + c) % 2 ^ 64 / 2 ^ 32 = (H + (L + c) / 2 ^ 32) % 2 ^ 32 := by
    rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by decide, Nat.mod_mul_right_div_self, e1]
  obtain hu : (L + c) / 2 ^ 32 < 2 ^ 32 := by omega_using [hL]
  rw [e1] at hV ⊢
  rw [e2]
  by_cases h : (H + (L + c) / 2 ^ 32) % 2 ^ 32 < H % 2 ^ 32
  · simp only [h, decide_true, Bool.toNat_true]; omega_using [hL, hV, h]
  · simp only [h, decide_false, Bool.toNat_false]; omega_using [hL, hV, h]

/-- `carry_eq` for the column's sum `P` and high words' sum `H`. -/
theorem col_carry {P H c Zh : Nat} (hle : 2 ^ 32 * H ≤ P) (hL : P - 2 ^ 32 * H + c < 2 ^ 64)
    (hV : (P + c) / 2 ^ 32 < 2 ^ 64) (hZ : Zh = (P + c) % 2 ^ 64 / 2 ^ 32) :
    Zh + 2 ^ 32 * ((H / 2 ^ 32 + (decide (Zh < H % 2 ^ 32)).toNat) % 2 ^ 32) = (P + c) / 2 ^ 32 := by
  obtain e : 2 ^ 32 * H + (P - 2 ^ 32 * H) + c = P + c := by omega_using [hle]
  have := carry_eq H (P - 2 ^ 32 * H) c hL (by rw [e]; exact hV)
  rw [e] at this
  rw [hZ]; exact this

/-- The quotient digit `q = x (-m⁻¹) mod r` cancels `x`'s low word. -/
theorem cancel_digit (r x m i : Nat) (hi : (m * i + 1) % r = 0) : (x + ((x % r * i) % r) * m) % r = 0 := by
  rw [Nat.add_mod, Nat.mod_mul_mod, Nat.add_mod_mod]
  obtain e : x % r + (x % r * i) * m = (x % r) * (m * i + 1) := by grind
  rw [e, Nat.mul_mod, hi, Nat.mul_zero, Nat.zero_mod]

/-- Two words of a number below `2⁶⁴`. -/
theorem words_split {x y h : Nat} (hx : x < 2 ^ 32) (e : x + 2 ^ 32 * y = h) : x = h % 2 ^ 32 ∧ y = h / 2 ^ 32 := by
  omega_using [hx, e]

/-- The bounds of a column with its quotient digit's product `qm`: no sum
overflows, and the next carry is again at most `(2 N + 2) 2³²`. -/
theorem column_bounds {AB QM H c qm N : Nat} (hN : N < 2 ^ 29) (hP : AB ≤ N * (2 ^ 32 - 1) * (2 ^ 32 - 1))
    (hQ : QM ≤ N * (2 ^ 32 - 1) * (2 ^ 32 - 1)) (fl : 2 ^ 32 * H ≤ AB + QM)
    (fw : AB + QM - 2 ^ 32 * H ≤ (2 * N + 3) * (2 ^ 32 - 1)) (hc : c ≤ (2 * N + 2) * 2 ^ 32)
    (hqm : qm ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1)) :
    H + qm / 2 ^ 32 < 2 ^ 64 ∧ 2 ^ 32 * (H + qm / 2 ^ 32) ≤ AB + QM + qm ∧
      AB + QM + qm - 2 ^ 32 * (H + qm / 2 ^ 32) + c < 2 ^ 64 ∧ (AB + QM + qm + c) / 2 ^ 32 < 2 ^ 64 ∧
      (AB + QM + qm + c) / 2 ^ 32 ≤ (2 * N + 2) * 2 ^ 32 := by
  have := Nat.div_add_mod qm (2 ^ 32)
  have := Nat.mod_lt qm (show 0 < 2 ^ 32 by decide)
  refine ⟨by omega_using [hN, hP, hQ, fl, hqm], by omega_using [fl], by omega_using [hN, fw, hc], by omega_using [hN, hP, hQ, hc, hqm], by omega_using [hP, hQ, hc, hqm]⟩

/-- A column sum without a digit (`qm = 0`). -/
theorem column_bounds0 {AB QM H c N : Nat} (hN : N < 2 ^ 29) (hP : AB ≤ N * (2 ^ 32 - 1) * (2 ^ 32 - 1))
    (hQ : QM ≤ N * (2 ^ 32 - 1) * (2 ^ 32 - 1)) (fl : 2 ^ 32 * H ≤ AB + QM)
    (fw : AB + QM - 2 ^ 32 * H ≤ (2 * N + 3) * (2 ^ 32 - 1)) (hc : c ≤ (2 * N + 2) * 2 ^ 32) :
    H < 2 ^ 64 ∧ AB + QM - 2 ^ 32 * H + c < 2 ^ 64 ∧ (AB + QM + c) / 2 ^ 32 < 2 ^ 64 ∧
      (AB + QM + c) / 2 ^ 32 ≤ (2 * N + 2) * 2 ^ 32 := by
  refine ⟨by omega_using [hN, hP, hQ, fl], by omega_using [hN, fw, hc], by omega_using [hN, hP, hQ, hc], by omega_using [hP, hQ, hc]⟩

/-- After the columns: `R (T + R c) = A B + Q M` with `A, Q < R` and `B < M ≤ R`
puts `T + R c` below `2 M`, and `c` below 2. -/
theorem final_bound {R A B M Q T c : Nat} (alt : A < R) (blt : B < M) (mle : M ≤ R) (qlt : Q < R)
    (eq : R * (T + R * c) = A * B + Q * M) : T + R * c < 2 * M ∧ c < 2 := by
  obtain rpos : 0 < R := by omega_using [alt]
  obtain a : A * B < R * M := Nat.mul_lt_mul_of_lt_of_le alt (Nat.le_of_lt blt) (by omega_using [blt])
  obtain q : Q * M ≤ R * M := Nat.mul_le_mul_right _ (Nat.le_of_lt qlt)
  obtain bound : R * (T + R * c) < R * (2 * M) := by
    rw [eq, show R * (2 * M) = R * M + R * M by rw [Nat.two_mul, Nat.mul_add]]; omega_using [a, q]
  obtain tlt := (Nat.mul_lt_mul_left rpos).mp bound
  refine ⟨tlt, ?_⟩
  have : R * c < R * 2 := by
    have : R * c ≤ T + R * c := Nat.le_add_left _ _
    have : 2 * M ≤ R * 2 := by rw [Nat.mul_comm R]; omega_using [mle]
    omega_using [mle, tlt]
  exact (Nat.mul_lt_mul_left rpos).mp this

/-- The result `O = (T + R c) mod M` is `A B R⁻¹` modulo `M`. -/
theorem final_mod {R A B M Q X : Nat} (eq : R * X = A * B + Q * M) : X % M * R % M = A * B % M := by
  rw [Nat.mod_mul_mod, Nat.mul_comm, eq, Nat.add_mul_mod_self_right]

end VG.Proof.Mont.X86.Sse2

end

end


/-! # The columns

`ColsI`: after the columns `j < k`, from the state `s0` the columns started
in, the carry `c` (at `S + 16`), the quotient digits `q` and the result's
words (`rvalT`), both in reverse at `S + 24`, the result's word `j`
replacing the digit `q_j`, dead, satisfy

`2^(32 k) c + 2^(32 N) T = Σ_(i+j<k) A_i B_j 2^(32 (i+j)) + Σ_(i+j<k) q_i M_j 2^(32 (i+j))`,

`A'` (`A` in reverse) is at `S + 24 + 4 N`, the two latest digits are in
`xmm6` while `k < N`, and only the function's scratch has changed. A column
keeps it (`column_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.X86.RegUpd VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt

/-- The numbers' offsets in the working space of `L` bytes: `A`, `B`, `M`
and the result `O` of `N ≥ 2` words, `-M⁻¹ mod 2³²` at `inv`, the scratch of
`8 N + 28` bytes at `S`, apart from the others, and `O` apart from `M` and
`inv`. -/
structure Lay (L N S mo inv o a b : Nat) : Prop where
  hN : 0 < N
  hN2 : 2 ≤ N
  hN28 : N < 2 ^ 29
  a_le : a + 4 * N ≤ L
  b_le : b + 4 * N ≤ L
  mo_le : mo + 4 * N ≤ L
  inv_le : inv + 4 ≤ L
  o_le : o + 4 * N ≤ L
  s_le : S + 8 * N + 28 ≤ L
  sa : a + 4 * N ≤ S ∨ S + 8 * N + 28 ≤ a
  sb : b + 4 * N ≤ S ∨ S + 8 * N + 28 ≤ b
  smo : mo + 4 * N ≤ S ∨ S + 8 * N + 28 ≤ mo
  sinv : inv + 4 ≤ S ∨ S + 8 * N + 28 ≤ inv
  so : o + 4 * N ≤ S ∨ S + 8 * N + 28 ≤ o

/-- The result's words stored so far, word `j` at word `N - 1 - j` of `S + 24`. -/
def rvalT (m : Mem) (W : Addr) (N S : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => rvalT m W N S n + 2 ^ (32 * n) * w32 m W (S + 24 + 4 * (N - 1 - n))

theorem rvalT_congr {m m' : Mem} {W : Addr} {N S : Nat} :
    ∀ {n : Nat}, (∀ j < n, w32 m' W (S + 24 + 4 * (N - 1 - j)) = w32 m W (S + 24 + 4 * (N - 1 - j))) →
      rvalT m' W N S n = rvalT m W N S n
  | 0, _ => rfl
  | n + 1, h => by
    rw [rvalT, rvalT, rvalT_congr fun j hj => h j (by omega_arith), h n (by omega_arith)]

/-- After the columns `j < k`. -/
structure ColsI (s0 : State) (W : Addr) (L : Nat) (V : Nat → BitVec 32) (N S mo a b k c : Nat) (q : Nat → Nat)
    (t : State) : Prop where
  ws : Ws t W L
  prm : Params t W L V 12
  out : Outs W [(S, 8 * N + 28)] s0.mem t.mem
  ecx : t.gpr .ecx = BitVec.ofNat 32 (4 * k)
  mcdt : t.mcdt = s0.mcdt
  carry : w32 t.mem W (S + 16) + 2 ^ 32 * w32 t.mem W (S + 20) = c
  bound : c ≤ (2 * N + 2) * 2 ^ 32
  revA : ∀ i < N, w32 t.mem W (S + 24 + 4 * N + 4 * (N - 1 - i)) = digits s0.mem W a i
  qlt : ∀ j, q j ≤ 2 ^ 32 - 1
  qs : RevQ t.mem W N S q (k - N) (min k N)
  win : k < N → Window t k q
  eq : (2 ^ 32) ^ k * c + (2 ^ 32) ^ N * rvalT t.mem W N S (k - N) =
    Column.partSum (2 ^ 32) (digits s0.mem W a) (digits s0.mem W b) N k +
    Column.partSum (2 ^ 32) (Column.prefixDigits q k) (digits s0.mem W mo) N k
  keep : Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s0 t

theorem digits_lt (m : Mem) (W : Addr) (x i : Nat) : digits m W x i ≤ 2 ^ 32 - 1 := by
  have := (m.readW (off W (x + 4 * i)) 32).isLt; simp only [digits, w32]; omega_arith

theorem coeff_le (m : Mem) (W : Addr) (y : Nat) {N k : Nat} (q : Nat → Nat) (hq : ∀ i, q i ≤ 2 ^ 32 - 1) :
    Column.coeff q (digits m W y) N k ≤ N * (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
  Column.coeff_bound (fun i _ => hq i) (fun _ _ => digits_lt _ _ _ _)

/-- A word apart from every range that changed. -/
theorem Outs.w32 {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    {d : Nat} (hd : ∀ r ∈ rs, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    w32 m' base d = w32 m base d := by
  have := h.val32 (k := 1) (by simpa using hd) (by simpa using hd')
  simpa [val32] using this

/-- The scratch's changes keep a number apart from it. -/
theorem digits_out {m m' : Mem} {W : Addr} {L N S x : Nat} (hn : W.toNat + L ≤ 2 ^ 32)
    (O : Outs W [(S, 8 * N + 28)] m m') (hx : x + 4 * N ≤ L) (sep : x + 4 * N ≤ S ∨ S + 8 * N + 28 ≤ x) :
    ∀ i < N, digits m' W x i = digits m W x i := fun i hi =>
  Outs.w32 O (by simp only [List.mem_singleton, forall_eq]; omega_arith) (by omega_arith)

theorem outs_widen {base : Addr} {rs rs' : List (Nat × Nat)} {m₁ m₂ : Mem} (h : Outs base rs m₁ m₂)
    (hr : ∀ y : Nat, (∀ r ∈ rs', y < r.1 ∨ r.1 + r.2 ≤ y) → ∀ r ∈ rs, y < r.1 ∨ r.1 + r.2 ≤ y) :
    Outs base rs' m₁ m₂ :=
  fun x hx => h x (hr _ hx)

/-- Changes within ranges each inside one of `rs'`. -/
theorem outs_sub {base : Addr} {rs rs' : List (Nat × Nat)} {m₁ m₂ : Mem} (h : Outs base rs m₁ m₂)
    (hr : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Outs base rs' m₁ m₂ :=
  outs_widen h fun y hy r h' => by
    obtain ⟨r', hr', h1, h2⟩ := hr r h'
    have := hy r' hr'
    omega_arith

theorem outs_sub1 {base : Addr} {rs' : List (Nat × Nat)} {m₁ m₂ : Mem} {a n : Nat} (h : Outs base [(a, n)] m₁ m₂)
    {r : Nat × Nat} (hr : r ∈ rs') (h1 : r.1 ≤ a) (h2 : a + n ≤ r.1 + r.2) : Outs base rs' m₁ m₂ :=
  outs_sub h fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact ⟨r, hr, h1, h2⟩

theorem outs_sub2 {base : Addr} {rs' : List (Nat × Nat)} {m₁ m₂ : Mem} {a n b p : Nat}
    (h : Outs base [(a, n), (b, p)] m₁ m₂) {r q : Nat × Nat} (hr : r ∈ rs') (h1 : r.1 ≤ a) (h2 : a + n ≤ r.1 + r.2)
    (hq : q ∈ rs') (h3 : q.1 ≤ b) (h4 : b + p ≤ q.1 + q.2) : Outs base rs' m₁ m₂ :=
  outs_sub h fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨r, hr, h1, h2⟩
    · exact ⟨q, hq, h3, h4⟩

theorem coeff_congr {a b a' b' : Nat → Nat} {N k : Nat} (ha : ∀ i < N, a i = a' i) (hb : ∀ i < N, b i = b' i) :
    Column.coeff a b N k = Column.coeff a' b' N k := by
  unfold Column.coeff
  apply NatSum.congr
  intro i hi
  apply NatSum.congr
  intro j hj
  rw [ha i hi, hb j hj]

/-- The word a column stores: the digit's while `k < N`, else the result's. -/
def slot (N k : Nat) : Nat := if k < N then N - 1 - k else 2 * N - 1 - k

/-- The invariant after column `k`, from the column's word (`residue`, zero
while `k < N`, then stored over the dead digit `q_(k-N)`), its quotient digit
`qk` (stored while `k < N`, then zero), the digits `q'` (`q` with `q'_k = qk`
while `k < N`) and the carry `c'`, with `residue + 2³² c'` the column's sum. -/
theorem cols_next {s0 t u : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b k c : Nat}
    {q q' : Nat → Nat} (Ly : Lay L N S mo inv o a b) (I : ColsI s0 W L V N S mo a b k c q t) (hk : k < 2 * N)
    (ws : Ws u W L) (prm : Params u W L V 12) (ecx : u.gpr .ecx = BitVec.ofNat 32 (4 * (k + 1)))
    (mc : u.mcdt = s0.mcdt) (K : Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] t u)
    (O : Outs W [(S, 24), (S + 24 + 4 * slot N k, 4)] t.mem u.mem)
    {qk residue c' : Nat} (hw : w32 u.mem W (S + 24 + 4 * slot N k) = if k < N then qk else residue)
    (hq' : ∀ j, j ≠ k → q' j = q j) (hqk : k < N → q' k = qk) (hqz : N ≤ k → q' = q ∧ qk = 0)
    (hqlt : qk ≤ 2 ^ 32 - 1) (hres0 : k < N → residue = 0)
    (hcar : w32 u.mem W (S + 16) + 2 ^ 32 * w32 u.mem W (S + 20) = c')
    (heq : residue + 2 ^ 32 * c' = c + Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k +
      Column.coeff (Column.prefixDigits q k) (digits s0.mem W mo) N k + qk * digits s0.mem W mo 0)
    (hb : c' ≤ (2 * N + 2) * 2 ^ 32) (win : k + 1 < N → Window u (k + 1) q') :
    ColsI s0 W L V N S mo a b (k + 1) c' q' u := by
  have hn := ws.nowrap
  have hs := Ly.s_le
  obtain hsl : slot N k < N := by unfold slot; split <;> omega_arith
  obtain Ow : Outs W [(S, 8 * N + 28)] t.mem u.mem := outs_widen O fun y hy r hr => by
    have := hy _ (List.mem_singleton_self _)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only at this ⊢ <;> omega_arith
  -- The digits.
  have qkk : ∀ j, j ≠ k → q' j = q j := hq'
  obtain qs : Column.partSum (2 ^ 32) (Column.prefixDigits q' (k + 1)) (digits s0.mem W mo) N (k + 1) =
      Column.partSum (2 ^ 32) (Column.prefixDigits q k) (digits s0.mem W mo) N k +
        (Column.coeff (Column.prefixDigits q k) (digits s0.mem W mo) N k + qk * digits s0.mem W mo 0) *
          (2 ^ 32) ^ k :=
    Column.qPart_step (2 ^ 32) q q' (digits s0.mem W mo) N k qk (fun i _ hik => hq' i (by omega_arith)) hqk
      (fun h => (hqz h).2)
  -- The result's words.
  obtain keepSlot : ∀ j, j ≠ slot N k → j < N → w32 u.mem W (S + 24 + 4 * j) = w32 t.mem W (S + 24 + 4 * j) :=
    fun j hj hjN => Outs.w32 O (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith) (by omega_arith)
  obtain out : (2 ^ 32) ^ N * rvalT u.mem W N S (k + 1 - N) =
      (2 ^ 32) ^ N * rvalT t.mem W N S (k - N) + (2 ^ 32) ^ k * residue := by
    by_cases hkN : k < N
    · rw [show k + 1 - N = 0 by omega_arith, show k - N = 0 by omega_arith, hres0 hkN]; simp [rvalT]
    · have hs' : slot N k = N - 1 - (k - N) := by unfold slot; rw [ite_eq_right hkN]; omega_arith
      rw [show k + 1 - N = (k - N) + 1 by omega_arith, rvalT, ← hs', hw, ite_eq_right hkN,
        rvalT_congr fun j hj => keepSlot _ (by rw [hs']; omega_arith) (by omega_arith),
        Nat.mul_add, ← Nat.mul_assoc, ← VG.Proof.Mont.X86.Square.pow32 (k - N), ← Nat.pow_add,
        show N + (k - N) = k by omega_arith]
  refine ⟨ws, prm, I.out.trans Ow, ecx, mc, hcar, hb, fun i hi => ?_, fun j => ?_, fun j h1 h2 => ?_, win, ?_,
    I.keep.trans K⟩
  · rw [Outs.w32 O (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith)
      (by omega_arith)]
    exact I.revA i hi
  · by_cases hj : j = k
    · subst hj
      by_cases hkN : j < N
      · rw [hqk hkN]; exact hqlt
      · rw [(hqz (by omega_arith)).1]; exact I.qlt j
    · rw [hq' j hj]; exact I.qlt j
  · -- The digits still stored.
    by_cases hkN : k < N
    · by_cases hj : j = k
      · subst hj
        obtain hs' : slot N j = N - 1 - j := by unfold slot; rw [ite_eq_left hkN]
        rw [← hs', hw, ite_eq_left hkN, hqk hkN]
      · rw [keepSlot _ (by unfold slot; rw [ite_eq_left hkN]; omega_arith) (by omega_arith), hq' j hj]
        exact I.qs j (by omega_arith) (by omega_arith)
    · rw [keepSlot _ (by unfold slot; rw [ite_eq_right hkN]; omega_arith) (by omega_arith), (hqz (by omega_arith)).1]
      exact I.qs j (by omega_arith) (by omega_arith)
  · exact VG.Proof.Mont.X86.Square.advance (2 ^ 32) N k c c' residue _ _ _ _ _ _ _ _ _ I.eq
      (by rw [heq]) out (Column.partSum_succ _ _ _ _ _) qs

theorem pxor_run (s : State) :
    runBlock isa clear s =
      some ((s.setXmm .xmm0 (XBinOp.eval .pxor (s.xmm .xmm0) (s.xmm .xmm0))).setXmm .xmm1
        (XBinOp.eval .pxor (s.xmm .xmm1) (s.xmm .xmm1))) := by
  simp only [clear, runBlock_cons, exec, runStep_some, XOp.exec, xmm_setXmm, reduceCtorEq, ↓reduceIte, runBlock_nil]

/-- `clear`: the sums of no products, and nothing else changed. -/
theorem pxor_ex (s : State) :
    ∃ u, runBlock isa clear s = some u ∧
      u.gpr = s.gpr ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.mcdt = s.mcdt ∧
      u.xmm .xmm6 = s.xmm .xmm6 ∧ Acc (u.xmm .xmm0) (u.xmm .xmm1) 0 0 0 :=
  ⟨_, pxor_run s, rfl, rfl, rfl, rfl, rfl, rfl,
    by simp only [xmm_setXmm, reduceCtorEq, ↓reduceIte]; exact Acc.zero⟩

/-- What the column has after `fold`: `edx:eax = (P + c) mod 2⁶⁴` for the
column's sum `P` of the products, the sum `H` of their high words at `S + 8`,
`P - 2³² H` at most `2 N + 3` low words. -/
structure Folded (s0 t : State) (W : Addr) (L : Nat) (V : Nat → BitVec 32) (N S mo a b k c : Nat) (q : Nat → Nat)
    (H : Nat) (u : State) : Prop where
  ws : Ws u W L
  prm : Params u W L V 12
  z : (u.gpr .eax).toNat + 2 ^ 32 * (u.gpr .edx).toNat =
    (Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k +
      Column.coeff (Column.prefixDigits q k) (digits s0.mem W mo) N k + c) % 2 ^ 64
  ebx : PtrAt u W .ebx S
  ecx : u.gpr .ecx = BitVec.ofNat 32 (4 * k)
  hw : w32 u.mem W (S + 8) + 2 ^ 32 * w32 u.mem W (S + 12) = H
  carry : w32 u.mem W (S + 16) + 2 ^ 32 * w32 u.mem W (S + 20) = c
  le : 2 ^ 32 * H ≤ Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k +
      Column.coeff (Column.prefixDigits q k) (digits s0.mem W mo) N k
  low : Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k +
      Column.coeff (Column.prefixDigits q k) (digits s0.mem W mo) N k - 2 ^ 32 * H ≤
      (2 * N + 3) * (2 ^ 32 - 1)
  out : Outs W [(S, 16)] t.mem u.mem
  keep : Keeps [.eax, .ebx, .edx, .esi, .edi, .ebp] t u
  mcdt : u.mcdt = t.mcdt
  x6 : u.xmm .xmm6 = t.xmm .xmm6

/-- The column's products, then `fold`. -/
theorem sums_ok {s0 t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b k c : Nat}
    {q : Nat → Nat} (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b) (hm0 : 0 < s0.mcdt)
    (I : ColsI s0 W L V N S mo a b k c q t) (hk : k < 2 * N) (sq hi : Bool) (hsq : sq = true → a = b)
    (hhi : hi = true ↔ N ≤ k) {rest : Prog isa} {Q : State → Prop}
    (K : ∀ u H, Folded s0 t W L V N S mo a b k c q H u → WP isa rest u Q) :
    WP isa (.seq (.block clear) (.seq (input sq hi) (.seq (reduce hi) (.seq (.block fold) rest)))) t Q := by
  have hn := I.ws.nowrap
  have hN := Ly.hN
  have hN28 := Ly.hN28
  have hs := Ly.s_le
  obtain ⟨t0, run0, g0, m0, rd0, wr0, mc0, x60, A0⟩ := pxor_ex t
  refine WP.seq (WP.of_runBlock ⟨t0, run0, ?_⟩)
  obtain K0 : Keeps [] t t0 := ⟨fun r _ => by rw [g0], rd0, wr0⟩
  obtain C0 : ColEnv t0 W L V N k := ⟨I.ws.of_keeps K0, I.prm.keep (by rw [m0]; exact Outs.refl _ _ _) (by rw [g0])
    rd0 wr0, PV.n4, hk, hN28, by rw [g0]; exact I.ecx, by rw [mc0, I.mcdt]; exact hm0⟩
  -- The numbers, as they were.
  obtain aT := digits_out hn I.out Ly.a_le Ly.sa
  obtain bT := digits_out hn I.out Ly.b_le Ly.sb
  obtain moT := digits_out hn I.out Ly.mo_le Ly.smo
  obtain RA : RevA t0.mem W N S a := fun i hi => by rw [m0, I.revA i hi, aT i hi]
  refine WP.seq (WP.mono (input_ok C0 PV sq hi hsq hhi Ly.a_le Ly.b_le hs RA A0) fun t1 P1 => ?_)
  obtain ⟨H1, n1, A1, hn1, hH1⟩ := P1.acc
  obtain C1 := C0.of_keeps P1.keep P1.mem P1.mcdt
  obtain mem1 : t1.mem = t.mem := by rw [P1.mem, m0]
  obtain eAB : Column.coeff (digits t0.mem W a) (digits t0.mem W b) N k =
      Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k := by rw [m0]; exact coeff_congr aT bT
  rw [eAB] at A1
  obtain hQ : ∀ {lo hi'}, lo ≥ k - N → hi' ≤ min k N → RevQ t1.mem W N S q lo hi' := fun h1 h2 j hj1 hj2 => by
    rw [mem1]; exact I.qs j (by omega_arith) (by omega_arith)
  obtain eM : ∀ k', Column.coeff (Column.prefixDigits q k') (digits t1.mem W mo) N k' =
      Column.coeff (Column.prefixDigits q k') (digits s0.mem W mo) N k' := fun _ => by
    rw [mem1]; exact coeff_congr (fun _ _ => rfl) moT
  obtain post2 : ∀ t2, RedPost t1 N (Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k +
      Column.coeff (Column.prefixDigits q k) (digits t1.mem W mo) N k) H1 n1 t2 →
      WP isa (.seq (.block fold) rest) t2 Q := fun t2 R2 => by
    obtain ⟨H2, n2, A2, hn2, hH2⟩ := R2.acc
    rw [eM] at A2
    obtain C2 := C1.of_keeps R2.keep R2.mem R2.mcdt
    obtain mem2 : t2.mem = t.mem := by rw [R2.mem, mem1]
    obtain hc2 : w32 t2.mem W (S + 16) + 2 ^ 32 * w32 t2.mem W (S + 20) = c := by rw [mem2]; exact I.carry
    refine WP.seq (WP.mono (fold_ok C2 PV.s (by omega_arith) A2 (by omega_arith) hc2)
      fun t3 ⟨z3, b3, h3, c3, O3, K3, mc3, x63⟩ => K t3 H2 ?_)
    obtain Kt3 : Keeps [.eax, .ebx, .edx, .esi, .edi, .ebp] t t3 :=
      ((((K0.mono (by decide)).trans (P1.keep.mono (by decide))).trans (R2.keep.mono (by decide))).trans
        (K3.mono (by decide)))
    obtain O3' : Outs W [(0, L)] t2.mem t3.mem := outs_widen O3 fun y hy r hr => by
      have := hy _ (List.mem_singleton_self _)
      simp only [List.mem_singleton] at hr; subst hr; simp only at this ⊢; omega_arith
    have := A2.le
    have := A2.low
    exact ⟨C2.ws.of_keeps K3, C2.prm.keep O3' (K3.1 _ (by decide)) K3.2.1 K3.2.2, z3, b3,
      by rw [K3.1 _ (by decide)]; exact C2.ecx, h3, c3, A2.le,
      Nat.le_trans A2.low (Nat.mul_le_mul_right _ (by omega_arith)), by rw [← mem2]; exact O3, Kt3,
      by rw [mc3, R2.mcdt, P1.mcdt, mc0], by rw [x63, R2.x6, P1.x6, x60]⟩
  cases hi with
  | true =>
    obtain hkN := hhi.mp rfl
    exact WP.seq (WP.mono (reduceHi_ok C1 PV hkN Ly.mo_le hs (hQ (by omega_arith) (by omega_arith)) (by omega_arith) A1) post2)
  | false =>
    obtain hkN : k < N := by have : ¬ N ≤ k := fun h => absurd (hhi.mpr h) (by decide); omega_arith
    obtain Wd : Window t1 k q := by
      obtain Wt := I.win hkN
      exact ⟨by rw [P1.x6, x60]; exact Wt.q1, by rw [P1.x6, x60]; exact Wt.q2⟩
    exact WP.seq (WP.mono (reduceLo_ok C1 PV hkN Ly.mo_le hs (hQ (by omega_arith) (by omega_arith)) Wd Ly.hN2 (by omega_arith) A1) post2)

/-- What a column's last block takes from `fold`'s state: the memory as at
the column's start but the sums, the modulus and the inverse as they were. -/
theorem folded_facts {s0 t t4 : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b k c : Nat}
    {q : Nat → Nat} {H : Nat} (Ly : Lay L N S mo inv o a b) (I : ColsI s0 W L V N S mo a b k c q t)
    (F : Folded s0 t W L V N S mo a b k c q H t4) :
    Outs W [(S, 8 * N + 28)] s0.mem t4.mem ∧ w32 t4.mem W inv = w32 s0.mem W inv ∧
      w32 t4.mem W mo = digits s0.mem W mo 0 ∧ (∀ i < N, digits t4.mem W mo i = digits s0.mem W mo i) := by
  have hn := I.ws.nowrap
  have hN := Ly.hN
  obtain O5 : Outs W [(S, 8 * N + 28)] s0.mem t4.mem :=
    I.out.trans (outs_widen F.out fun y hy r hr => by
      have := hy _ (List.mem_singleton_self _)
      simp only [List.mem_singleton] at hr; subst hr; simp only at this ⊢; omega_arith)
  refine ⟨O5, Outs.w32 O5 (by have := Ly.sinv; simp only [List.mem_singleton, forall_eq]; omega_arith)
      (by have := Ly.inv_le; omega_arith), ?_, digits_out hn O5 Ly.mo_le Ly.smo⟩
  rw [digits, Nat.mul_zero, Nat.add_zero]
  exact Outs.w32 O5 (by have := Ly.smo; simp only [List.mem_singleton, forall_eq]; omega_arith)
    (by have := Ly.mo_le; omega_arith)

/-- A column's last block while `k < N`: the digit stored and into the window,
the carry stored, `ecx` up a word. -/
theorem digitBlock_ok {t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S mo inv Z H : Nat}
    (hw : Ws t W L) (P : Params t W L V 12) (hcx : t.gpr .ecx = BitVec.ofNat 32 (4 * k)) (hkN : k < N)
    (hN4 : (V pN4).toNat = 4 * N) (hN28 : N < 2 ^ 29)
    (hM : (V pM).toNat = (W.toNat + mo) % 2 ^ 32) (hI : (V pInv).toNat = (W.toNat + inv) % 2 ^ 32)
    (hs : S + 24 + 4 * N ≤ L) (hm : mo + 4 ≤ L) (hi : inv + 4 ≤ L)
    (sep : mo + 4 ≤ S + 24 + 4 * (N - 1 - k) ∨ S + 24 + 4 * (N - 1 - k) + 4 ≤ mo)
    (hb : PtrAt t W .ebx S) (hz : (t.gpr .eax).toNat + 2 ^ 32 * (t.gpr .edx).toNat = Z)
    (hH : w32 t.mem W (S + 8) + 2 ^ 32 * w32 t.mem W (S + 12) = H) :
    WP isa (.block (digit ++ (carry ++ (([.alu .add .ecx (.imm 4), .mov .eax (.mem (kp pN4))] : List Instr) ++
      ((if false then ([.alu .add .eax (.reg .eax)] : List Instr) else []) ++ ([.alu .cmp .ecx (.reg .eax)] : List Instr)))))) t fun u =>
      ∃ Hl Hh, Hl < 2 ^ 32 ∧ Hl + 2 ^ 32 * Hh =
          (H + (Z % 2 ^ 32 * w32 t.mem W inv) % 2 ^ 32 * w32 t.mem W mo / 2 ^ 32) % 2 ^ 64 ∧
        w32 u.mem W (S + 16) =
          (Z + (Z % 2 ^ 32 * w32 t.mem W inv) % 2 ^ 32 * w32 t.mem W mo) % 2 ^ 64 / 2 ^ 32 ∧
        w32 u.mem W (S + 20) = (Hh + (decide ((Z + (Z % 2 ^ 32 * w32 t.mem W inv) % 2 ^ 32 * w32 t.mem W mo) %
          2 ^ 64 / 2 ^ 32 < Hl)).toNat) % 2 ^ 32 ∧
        w32 u.mem W (S + 24 + 4 * (N - 1 - k)) = (Z % 2 ^ 32 * w32 t.mem W inv) % 2 ^ 32 ∧
        Outs W [(S + 8, 16), (S + 24 + 4 * (N - 1 - k), 4)] t.mem u.mem ∧
        Ws u W L ∧ Params u W L V 12 ∧ u.gpr .ecx = BitVec.ofNat 32 (4 * (k + 1)) ∧
        u.zf = some (decide (k + 1 = N)) ∧ Keeps [.eax, .ecx, .edx, .esi, .edi] t u ∧ u.mcdt = t.mcdt ∧
        (dword (u.xmm .xmm6) 0).toNat = (Z % 2 ^ 32 * w32 t.mem W inv) % 2 ^ 32 ∧
        dword (u.xmm .xmm6) 2 = dword (t.xmm .xmm6) 0 := by
  have hn := hw.nowrap
  obtain hk : k < 2 * N := by omega_arith
  refine WP.block_append (WP.mono (digit_ok hw P hcx hkN hN4 hM hI hs hm hi sep hb hz hH)
    fun t6 ⟨d6, q6, hh6, O6, K6, mc6, w60, w62⟩ => ?_)
  obtain hw6 := hw.of_keeps K6
  obtain O6' : Outs W [(0, L)] t.mem t6.mem := outs_sub2 O6 (List.mem_singleton_self _) (Nat.zero_le _)
    (by simp only; omega_arith) (List.mem_singleton_self _) (Nat.zero_le _) (by simp only; omega_arith)
  obtain P6 : Params t6 W L V 12 := P.keep O6' (K6.1 _ (by decide)) K6.2.1 K6.2.2
  obtain b6 : PtrAt t6 W .ebx S := by rw [PtrAt, K6.1 _ (by decide)]; exact hb
  obtain ecx6 : t6.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [K6.1 _ (by decide)]; exact hcx
  refine WP.block_append (WP.mono (carry_ok hw6 (by omega_arith) b6) fun t7 ⟨cl, ch, O7, K7, mc7, x7⟩ => ?_)
  obtain hw7 := hw6.of_keeps K7
  obtain O7' : Outs W [(0, L)] t6.mem t7.mem := outs_sub1 O7 (List.mem_singleton_self _) (Nat.zero_le _)
    (by simp only; omega_arith)
  obtain P7 : Params t7 W L V 12 := P6.keep O7' (K7.1 _ (by decide)) K7.2.1 K7.2.2
  obtain ecx7 : t7.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [K7.1 _ (by decide)]; exact ecx6
  refine WP.mono (step_ok P7 hN4 ecx7 hk hN28 false) fun u ⟨ecxu, zfu, Ku, mu, mcu, xu⟩ => ?_
  obtain ⟨e8, e12⟩ := words_split (t6.mem.readW (off W (S + 8)) 32).isLt hh6
  refine ⟨_, _, (t6.mem.readW (off W (S + 8)) 32).isLt, hh6, ?_, ?_, ?_, ?_, hw7.of_keeps Ku,
    P7.keep (by rw [mu]; exact Outs.refl _ _ _) (Ku.1 _ (by decide)) Ku.2.1 Ku.2.2, ecxu,
    by rw [zfu]; simp, ((K6.mono (by decide)).trans (K7.mono (by decide))).trans (Ku.mono (by decide)),
    by rw [mcu, mc7, mc6], by rw [xu, x7]; exact w60, by rw [xu, x7]; exact w62⟩
  · rw [mu, cl, d6]
  · rw [mu, ch, d6]
  · rw [mu, Outs.w32 O7 (by simp only [List.mem_singleton, forall_eq]; omega_arith) (by omega_arith), q6]
  · rw [mu]
    refine (outs_sub2 O6 (r := (S + 8, 16)) (List.mem_cons_self ..) (Nat.le_refl _) (by simp only; omega_arith)
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (Nat.le_refl _) (Nat.le_refl _)).trans
      (outs_sub1 O7 (List.mem_cons_self ..) (by simp only; omega_arith) (by simp only; omega_arith))

/-- A column while `k < N`: its digit stored and into the window. -/
theorem columnLo_ok {s0 t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b k c : Nat}
    {q : Nat → Nat} (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b)
    (hinv : (w32 s0.mem W mo * w32 s0.mem W inv + 1) % 2 ^ 32 = 0) (hm0 : 0 < s0.mcdt)
    (I : ColsI s0 W L V N S mo a b k c q t) (hkN : k < N) (sq : Bool) (hsq : sq = true → a = b) :
    WP isa (column sq false) t fun u =>
      ∃ c' q', ColsI s0 W L V N S mo a b (k + 1) c' q' u ∧ u.zf = some (decide (k + 1 = N)) := by
  have hn := I.ws.nowrap
  have hN := Ly.hN
  have hN28 := Ly.hN28
  have hs := Ly.s_le
  have hcb := I.bound
  obtain hk : k < 2 * N := by omega_arith
  unfold column
  simp only [seqs]
  rw [show (if false = true then VG.Impl.Mont.X86.Sse2.word else digit) = digit from rfl]
  simp only [List.append_assoc]
  refine sums_ok Ly PV hm0 I hk sq false hsq (by simp; omega_arith) fun t4 H F => ?_
  obtain ⟨O4, iv4, m04, mo4⟩ := folded_facts Ly I F
  refine WP.mono (digitBlock_ok F.ws F.prm F.ecx hkN PV.n4 hN28 PV.mo PV.inv (by omega_arith)
    (by have := Ly.mo_le; omega_arith) Ly.inv_le (by have := Ly.smo; omega_arith) F.ebx F.z F.hw)
    fun u ⟨Hl, Hh, hHl, hHw, cl, ch, qw, Ou4, wsu, Pu, ecxu, zfu, Ku, mcu, w60, w62⟩ => ?_
  rw [iv4, m04] at hHw cl ch
  rw [iv4] at qw w60
  obtain hsl : slot N k = N - 1 - k := by unfold slot; rw [ite_eq_left hkN]
  obtain Ou : Outs W [(S, 24), (S + 24 + 4 * slot N k, 4)] t.mem u.mem := by
    rw [hsl]
    refine (outs_sub1 F.out (List.mem_cons_self ..) (Nat.le_refl _) (by simp only; omega_arith)).trans
      (outs_sub2 Ou4 (List.mem_cons_self ..) (by simp only; omega_arith) (by simp only; omega_arith)
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (Nat.le_refl _) (Nat.le_refl _))
  obtain hP := coeff_le s0.mem W b (N := N) (k := k) (digits s0.mem W a) (digits_lt _ _ _)
  obtain hQ := coeff_le s0.mem W mo (N := N) (k := k) (Column.prefixDigits q k) (fun i => by
      unfold Column.prefixDigits; split
      · exact I.qlt i
      · omega_arith)
  have fl := F.le
  have fw := F.low
  generalize hAB : Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k = AB at fl fw hP hHw cl ch qw w60
  generalize hQM : Column.coeff (Column.prefixDigits q k) (digits s0.mem W mo) N k = QM at fl fw hQ hHw cl ch qw w60
  obtain hM0 := digits_lt s0.mem W mo 0
  generalize hq : ((AB + QM + c) % 2 ^ 64 % 2 ^ 32 * w32 s0.mem W inv) % 2 ^ 32 = qk at hHw cl ch qw w60
  obtain hq32 : qk < 2 ^ 32 := by rw [← hq]; exact Nat.mod_lt _ (by decide)
  obtain hqm : qk * digits s0.mem W mo 0 ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega_arith) hM0
  obtain h0 : digits s0.mem W mo 0 = w32 s0.mem W mo := by simp only [digits, Nat.mul_zero, Nat.add_zero]
  obtain cancel := cancel_digit (2 ^ 32) (AB + QM + c) (digits s0.mem W mo 0) (w32 s0.mem W inv)
    (by rw [h0]; exact hinv)
  have hq' := hq
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)] at hq'
  rw [hq'] at cancel
  generalize hqmv : qk * digits s0.mem W mo 0 = qm at hHw cl ch hqm cancel
  obtain ⟨b1, b2, b3, b4, b5'⟩ := column_bounds hN28 hP hQ fl fw hcb hqm
  rw [Nat.mod_eq_of_lt b1] at hHw
  obtain ⟨e8, e12⟩ := words_split hHl hHw
  rw [Nat.mod_add_mod] at cl ch
  obtain e : AB + QM + c + qm = AB + QM + qm + c := Nat.add_right_comm _ _ _
  rw [e] at cl ch
  obtain cc := col_carry (P := AB + QM + qm) (H := H + qm / 2 ^ 32) (c := c)
    (Zh := (AB + QM + qm + c) % 2 ^ 64 / 2 ^ 32) b2 b3 b4 rfl
  refine ⟨(AB + QM + qm + c) / 2 ^ 32, fun j => if j = k then qk else q j,
    cols_next (qk := qk) (residue := 0) Ly I hk wsu Pu ecxu (by rw [mcu, F.mcdt, I.mcdt])
      ((F.keep.mono (by decide)).trans (Ku.mono (by decide))) Ou ?_
      (fun j hj => by simp only [hj, ↓reduceIte]) (fun _ => by simp)
      (fun h => absurd h (by omega_using [h, hkN])) (by omega_using [hq32]) (fun _ => rfl) ?_ ?_ b5' ?_, zfu⟩
  · rw [hsl, qw, ite_eq_left hkN]
  · rw [cl, ch, e8, e12]
    exact cc
  · rw [hAB, hQM, hqmv]
    omega_using [cancel]
  · intro hk1
    obtain Wt := I.win hkN
    refine ⟨?_, ?_⟩
    · rw [w60, ite_eq_left (by omega_using [] : 1 ≤ k + 1), show k + 1 - 1 = k by omega_using []]; simp
    · rw [w62, F.x6, Wt.q1]
      by_cases h1 : 1 ≤ k
      · rw [ite_eq_left h1, ite_eq_left (by omega_using [h1] : 2 ≤ k + 1), show k + 1 - 2 = k - 1 by omega_using [h1],
          ite_eq_right (by omega_using [h1] : k - 1 ≠ k)]
      · rw [ite_eq_right h1, ite_eq_right (by omega_using [h1])]

/-- A column's last block from `k = N` on: the result's word stored over the
dead digit, the carry stored, `ecx` up a word. -/
theorem wordBlock_ok {t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S : Nat}
    (hw : Ws t W L) (P : Params t W L V 12) (hcx : t.gpr .ecx = BitVec.ofNat 32 (4 * k)) (hk : k < 2 * N)
    (hN4 : (V pN4).toNat = 4 * N) (hN28 : N < 2 ^ 29) (hs : S + 24 + 8 * N ≤ L) (hb : PtrAt t W .ebx S) :
    WP isa (.block (VG.Impl.Mont.X86.Sse2.word ++ (carry ++ (([.alu .add .ecx (.imm 4), .mov .eax (.mem (kp pN4))] : List Instr) ++
      ((if true then ([.alu .add .eax (.reg .eax)] : List Instr) else []) ++ ([.alu .cmp .ecx (.reg .eax)] : List Instr)))))) t fun u =>
      w32 u.mem W (S + 16) = (t.gpr .edx).toNat ∧
      w32 u.mem W (S + 20) = (w32 t.mem W (S + 12) +
        (decide ((t.gpr .edx).toNat < w32 t.mem W (S + 8))).toNat) % 2 ^ 32 ∧
      w32 u.mem W (S + 24 + 4 * (2 * N - 1 - k)) = (t.gpr .eax).toNat ∧
      Outs W [(S + 16, 8), (S + 24 + 4 * (2 * N - 1 - k), 4)] t.mem u.mem ∧
      Ws u W L ∧ Params u W L V 12 ∧ u.gpr .ecx = BitVec.ofNat 32 (4 * (k + 1)) ∧
      u.zf = some (decide (k + 1 = 2 * N)) ∧ Keeps [.eax, .ecx, .esi] t u ∧ u.mcdt = t.mcdt := by
  have hn := hw.nowrap
  refine WP.block_append (WP.mono (word_ok hw P hN4 hcx hk hs hb) fun t6 ⟨w6, O6, K6, mc6, x6⟩ => ?_)
  obtain hw6 := hw.of_keeps K6
  obtain O6' : Outs W [(0, L)] t.mem t6.mem := outs_sub1 O6 (List.mem_singleton_self _) (Nat.zero_le _)
    (by simp only; omega_arith)
  obtain P6 : Params t6 W L V 12 := P.keep O6' (K6.1 _ (by decide)) K6.2.1 K6.2.2
  obtain b6 : PtrAt t6 W .ebx S := by rw [PtrAt, K6.1 _ (by decide)]; exact hb
  obtain ecx6 : t6.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [K6.1 _ (by decide)]; exact hcx
  obtain r8 : w32 t6.mem W (S + 8) = w32 t.mem W (S + 8) :=
    Outs.w32 O6 (by simp only [List.mem_singleton, forall_eq]; omega_arith) (by omega_arith)
  obtain r12 : w32 t6.mem W (S + 12) = w32 t.mem W (S + 12) :=
    Outs.w32 O6 (by simp only [List.mem_singleton, forall_eq]; omega_arith) (by omega_arith)
  obtain edx6 : t6.gpr .edx = t.gpr .edx := K6.1 _ (by decide)
  refine WP.block_append (WP.mono (carry_ok hw6 (by omega_arith) b6) fun t7 ⟨cl, ch, O7, K7, mc7, x7⟩ => ?_)
  obtain hw7 := hw6.of_keeps K7
  obtain O7' : Outs W [(0, L)] t6.mem t7.mem := outs_sub1 O7 (List.mem_singleton_self _) (Nat.zero_le _)
    (by simp only; omega_arith)
  obtain P7 : Params t7 W L V 12 := P6.keep O7' (K7.1 _ (by decide)) K7.2.1 K7.2.2
  obtain ecx7 : t7.gpr .ecx = BitVec.ofNat 32 (4 * k) := by rw [K7.1 _ (by decide)]; exact ecx6
  refine WP.mono (step_ok P7 hN4 ecx7 hk hN28 true) fun u ⟨ecxu, zfu, Ku, mu, mcu, xu⟩ => ?_
  refine ⟨by rw [mu, cl, edx6], by rw [mu, ch, r8, r12, edx6], ?_, ?_, hw7.of_keeps Ku,
    P7.keep (by rw [mu]; exact Outs.refl _ _ _) (Ku.1 _ (by decide)) Ku.2.1 Ku.2.2, ecxu,
    by rw [zfu]; simp, ((K6.mono (by decide)).trans (K7.mono (by decide))).trans (Ku.mono (by decide)),
    by rw [mcu, mc7, mc6]⟩
  · rw [mu, Outs.w32 O7 (by simp only [List.mem_singleton, forall_eq]; omega_arith) (by omega_arith), w6]
  · rw [mu]
    exact (outs_sub1 O6 (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (Nat.le_refl _) (Nat.le_refl _)).trans
      (outs_sub1 O7 (List.mem_cons_self ..) (Nat.le_refl _) (Nat.le_refl _))

/-- A column from `k = N` on: its word of the result stored. -/
theorem columnHi_ok {s0 t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b k c : Nat}
    {q : Nat → Nat} (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b) (hm0 : 0 < s0.mcdt)
    (I : ColsI s0 W L V N S mo a b k c q t) (hkN : N ≤ k) (hk : k < 2 * N) (sq : Bool) (hsq : sq = true → a = b) :
    WP isa (column sq true) t fun u =>
      ∃ c' q', ColsI s0 W L V N S mo a b (k + 1) c' q' u ∧ u.zf = some (decide (k + 1 = 2 * N)) := by
  have hn := I.ws.nowrap
  have hN := Ly.hN
  have hN28 := Ly.hN28
  have hs := Ly.s_le
  have hcb := I.bound
  unfold column
  simp only [seqs]
  simp only [↓reduceIte, List.append_assoc]
  refine sums_ok Ly PV hm0 I hk sq true hsq (by simp; omega_arith) fun t4 H F => ?_
  refine WP.mono (wordBlock_ok F.ws F.prm F.ecx hk PV.n4 hN28 (by omega_arith) F.ebx)
    fun u ⟨cl, ch, ww, Ou4, wsu, Pu, ecxu, zfu, Ku, mcu⟩ => ?_
  obtain hsl : slot N k = 2 * N - 1 - k := by unfold slot; rw [ite_eq_right (by omega_using [hkN])]
  obtain Ou : Outs W [(S, 24), (S + 24 + 4 * slot N k, 4)] t.mem u.mem := by
    rw [hsl]
    refine (outs_sub1 F.out (List.mem_cons_self ..) (Nat.le_refl _) (by simp only; omega_arith)).trans
      (outs_sub2 Ou4 (List.mem_cons_self ..) (by simp only; omega_arith) (by simp only; omega_arith)
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (Nat.le_refl _) (Nat.le_refl _))
  obtain hP := coeff_le s0.mem W b (N := N) (k := k) (digits s0.mem W a) (digits_lt _ _ _)
  obtain hQ := coeff_le s0.mem W mo (N := N) (k := k) (Column.prefixDigits q k) (fun i => by
      unfold Column.prefixDigits; split
      · exact I.qlt i
      · omega_arith)
  have fl := F.le
  have fw := F.low
  have fz := F.z
  have hH := F.hw
  generalize hAB : Column.coeff (digits s0.mem W a) (digits s0.mem W b) N k = AB at fl fw fz hP
  generalize hQM : Column.coeff (Column.prefixDigits q k) (digits s0.mem W mo) N k = QM at fl fw fz hQ
  obtain ⟨b1, b2, b3, b4⟩ := column_bounds0 hN28 hP hQ fl fw hcb
  obtain ⟨e8, e12⟩ := words_split (t4.mem.readW (off W (S + 8)) 32).isLt hH
  obtain hlo := (t4.gpr .eax).isLt
  obtain ⟨zl, zh⟩ := words_split hlo fz
  obtain cc := col_carry (P := AB + QM) (H := H) (c := c) fl b2 b3 zh
  refine ⟨(AB + QM + c) / 2 ^ 32, q,
    cols_next (qk := 0) (residue := (AB + QM + c) % 2 ^ 32) Ly I hk wsu Pu ecxu (by rw [mcu, F.mcdt, I.mcdt])
      ((F.keep.mono (by decide)).trans (Ku.mono (by decide))) Ou ?_ (fun _ _ => rfl)
      (fun h => absurd h (by omega_using [h, hkN])) (fun _ => ⟨rfl, rfl⟩) (Nat.zero_le _)
      (fun h => absurd h (by omega_using [h, hkN])) ?_ ?_ b4 (fun h => absurd h (by omega_using [h, hkN])), zfu⟩
  · rw [hsl, ww, ite_eq_right (by omega_using [hkN]), zl, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)]
  · rw [cl, ch, show w32 t4.mem W (S + 8) = _ from e8, show w32 t4.mem W (S + 12) = _ from e12]
    exact cc
  · rw [hAB, hQM, Nat.zero_mul, Nat.add_zero]
    omega_using []

/-- A column keeps the invariant. -/
theorem column_ok {s0 t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N S mo inv o a b k c : Nat}
    {q : Nat → Nat} (Ly : Lay L N S mo inv o a b) (PV : PVals V W N S mo inv o a b)
    (hinv : (w32 s0.mem W mo * w32 s0.mem W inv + 1) % 2 ^ 32 = 0) (hm0 : 0 < s0.mcdt)
    (I : ColsI s0 W L V N S mo a b k c q t) (hk : k < 2 * N) (sq hi : Bool) (hsq : sq = true → a = b)
    (hhi : hi = true ↔ N ≤ k) :
    WP isa (column sq hi) t fun u =>
      ∃ c' q', ColsI s0 W L V N S mo a b (k + 1) c' q' u ∧
        u.zf = some (decide (k + 1 = if hi then 2 * N else N)) := by
  cases hi with
  | false =>
    obtain hkN : k < N := by have : ¬ N ≤ k := fun h => absurd (hhi.mpr h) (by decide); omega_arith
    exact columnLo_ok Ly PV hinv hm0 I hkN sq hsq
  | true => exact columnHi_ok Ly PV hm0 I (hhi.mp rfl) hk sq hsq

end VG.Proof.Mont.X86.Sse2
