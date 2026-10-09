import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Vec
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Lemmas

/-!
# RSA with AVX512_IFMA on x86-64, any size: moving numbers between the layouts

`to52` (`to52_ok`) reads `W` 64-bit words and
writes the `4 R` 52-bit limbs of their value in the stride layout (zero
for the limbs above the words); `to64` (`to64_ok`) the reverse, into
`W + 1` words.
-/

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside off_off ofs_off writeW_outside wv)
open VG.Impl.Rsa.X86_64.CrtIfma
open VG.Proof.Bignum.X86_64.AmmSym (shl_eq' drop_hi div_split or_shr_shl mod52_of_mod64 wv_one
  limbN limbN_lt lval_limbN pow2_le cj cj_bit testBit_lval getLsbD_foldl_or foldl_congr')

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

theorem conv_bounds (hl : LayOk l) : 1 ≤ l.W ∧ 64 * l.W ≤ 52 * l.L ∧ l.L ≤ 40 ∧ 64 * l.W + 2 ≤ 52 * l.L ∧
    128 * l.W ≤ 416 * l.R := by
  rcases hl with rfl | rfl | rfl <;> decide

theorem and_mask' (x : BitVec 64) : x &&& mask52 = BitVec.ofNat 64 (x.toNat % 2 ^ 52) := AmmSym.and_mask' x

/-- The words from word `w` on, a number. -/
theorem wv_div {m : Mem} {A : Addr} {W w : Nat} (hw : w < W) :
    wv m A 0 W / 2 ^ (64 * w) = (word m A (8 * w)).toNat + 2 ^ 64 * wv m A (8 * w + 8) (W - 1 - w) := by
  have e := VG.Proof.Bignum.wv_add m A 0 w (W - w)
  rw [show w + (W - w) = W by omega] at e
  have e1 := VG.Proof.Bignum.wv_add m A (0 + 8 * w) 1 (W - 1 - w)
  rw [show 1 + (W - 1 - w) = W - w by omega] at e1
  rw [e, e1, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (VG.Proof.Bignum.wv_lt m A 0 w), Nat.zero_add]
  simp only [VG.Proof.Bignum.wv, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.mul_one,
    Nat.add_zero]

/-- Limb `j` of `to52`. -/
def l52 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (j : Nat) : List Instr :=
  let b := 52 * j
  let w := b / 64
  let s := b % 64
  if l.W ≤ w then [.mov32 .rax (.imm 0), .store (at_ .r11 (l.off j)) .rax] else
  ([.mov .rax (.mem (at_ .rsi (8 * w)))] : List Instr) ++
  (if s = 0 then [] else [.shift .shr .rax s]) ++
  (if 12 < s ∧ w + 1 < l.W then
    ([.mov .rcx (.mem (at_ .rsi (8 * (w + 1))))] : List Instr) ++ shl .rcx (64 - s) ++
      ([.alu .or .rax (.reg .rcx)] : List Instr)
  else []) ++
  ([.alu .and .rax (.reg .r12), .store (at_ .r11 (l.off j)) .rax] : List Instr)

theorem to52_eq : to52 l = (List.range l.L).flatMap (l52 l) := rfl

/-- The value of a limb within one word (`s ≤ 12`) or in the last (`w = W - 1`). -/
theorem limbN_one {m : Mem} {A : Addr} {W j : Nat} (hw : 52 * j / 64 < W)
    (h : 52 * j % 64 ≤ 12 ∨ 52 * j / 64 = W - 1) :
    limbN (wv m A 0 W) j = (word m A (8 * (52 * j / 64))).toNat / 2 ^ (52 * j % 64) % 2 ^ 52 := by
  unfold limbN
  rw [show 52 * j = 64 * (52 * j / 64) + 52 * j % 64 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
    show (64 * (52 * j / 64) + 52 * j % 64) / 64 = 52 * j / 64 by omega,
    show (64 * (52 * j / 64) + 52 * j % 64) % 64 = 52 * j % 64 by omega, wv_div hw, div_split _ _ _ (by omega)]
  rcases h with h | h
  · exact drop_hi _ _ _ (by omega)
  · rw [show W - 1 - 52 * j / 64 = 0 by omega]; simp [VG.Proof.Bignum.wv]

/-- The value of a limb across two words. -/
theorem limbN_two {m : Mem} {A : Addr} {W j : Nat} (h : 12 < 52 * j % 64) (h' : 52 * j / 64 + 1 < W) :
    limbN (wv m A 0 W) j = ((word m A (8 * (52 * j / 64))).toNat / 2 ^ (52 * j % 64) +
      (word m A (8 * (52 * j / 64 + 1))).toNat * 2 ^ (64 - 52 * j % 64) % 2 ^ 64) % 2 ^ 52 := by
  have hw : 52 * j / 64 < W := by omega
  unfold limbN
  rw [show 52 * j = 64 * (52 * j / 64) + 52 * j % 64 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
    show (64 * (52 * j / 64) + 52 * j % 64) / 64 = 52 * j / 64 by omega,
    show (64 * (52 * j / 64) + 52 * j % 64) % 64 = 52 * j % 64 by omega, wv_div hw, div_split _ _ _ (by omega),
    wv_one (by omega), mod52_of_mod64, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add, ← Nat.add_assoc,
    show 8 * (52 * j / 64) + 8 = 8 * (52 * j / 64 + 1) by omega, Nat.mul_comm (2 ^ (64 - _))]
  exact drop_hi _ _ _ (by omega)

/-- A limb above the words is zero. -/
theorem limbN_zero {m : Mem} {A : Addr} {W j : Nat} (h : W ≤ 52 * j / 64) : limbN (wv m A 0 W) j = 0 := by
  unfold limbN
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (VG.Proof.Bignum.wv_lt m A 0 W) (pow2_le (by omega)))]

theorem l52_writes (j : Nat) : VG.Proof.MlKem.X86_64.writesOnly [.rax, .rcx, .rbp] (.block (l52 l j)) = true := by
  unfold l52
  dsimp only
  split
  · rfl
  · split <;> split <;> rfl

/-- Limb `j` of the `W` words at `rsi = A` into `r11 + off j`. -/
theorem l52_ok {s : State} {A C : Addr} {j : Nat} (hA : s.gpr .rsi = A) (hC : s.gpr .r11 = C)
    (h12 : s.gpr .r12 = mask52) (hrd : ∀ i < l.W, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * i)) 8)
    (hwr : InRegions s.wr (C + BitVec.ofNat 64 (l.off j)) 8) :
    WP isa (.block (l52 l j)) s fun s' =>
      s'.mem = s.mem.writeW (off C (l.off j)) (BitVec.ofNat 64 (limbN (wv s.mem A 0 l.W) j)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rbp] s s' ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rcx, .rbp] (Q := fun s' =>
    s'.mem = s.mem.writeW (off C (l.off j)) (BitVec.ofNat 64 (limbN (wv s.mem A 0 l.W) j)) ∧
      s'.mxcsr = s.mxcsr) ?_ (l52_writes j)) fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩
  by_cases hz : l.W ≤ 52 * j / 64
  · simp only [l52, hz, ite_true]
    xrun [eaG', hC, hwr]
    refine ⟨congrArg (Mem.writeW _ _) ?_, rfl⟩
    rw [limbN_zero hz]; rfl
  have hw : 52 * j / 64 < l.W := by omega
  have r0 := hrd _ hw
  by_cases h0 : 52 * j % 64 = 0
  · have hC' : (12 < 0 ∧ 52 * j / 64 + 1 < l.W) = False := eq_false (by omega)
    simp only [l52, hz, ite_false, h0, ite_true, hC', List.append_nil, List.cons_append, List.nil_append]
    xrun [eaG', hA, hC, h12, r0, hwr]
    refine ⟨congrArg (Mem.writeW _ _) ?_, rfl⟩
    rw [and_mask', limbN_one hw (.inl (by omega)), h0, Nat.pow_zero, Nat.div_one]
  · have hsc : (1 ≤ 52 * j % 64 ∧ 52 * j % 64 ≤ 63) = True := eq_true ⟨by omega, by omega⟩
    by_cases hC2 : 12 < 52 * j % 64 ∧ 52 * j / 64 + 1 < l.W
    · have r1 := hrd _ hC2.2
      have hmc : (1 ≤ 64 - (64 - 52 * j % 64) ∧ 64 - (64 - 52 * j % 64) ≤ 63) = True :=
        eq_true ⟨by omega, by omega⟩
      simp only [l52, hz, h0, ite_false, hC2, and_self, ite_true, shl, List.cons_append, List.nil_append]
      xrun [eaG', hA, hC, h12, r0, r1, hwr, hsc, hmc]
      refine ⟨congrArg (Mem.writeW _ _) ?_, rfl⟩
      rw [shl_eq' _ (by omega) (by omega), and_mask', or_shr_shl _ _ (by omega) (by omega), limbN_two hC2.1 hC2.2]
    · simp only [l52, hz, h0, ite_false, hC2, List.append_nil, List.cons_append, List.nil_append]
      xrun [eaG', hA, hC, h12, r0, hwr, hsc]
      refine ⟨congrArg (Mem.writeW _ _) ?_, rfl⟩
      rw [and_mask', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, limbN_one hw (by omega)]

/-- The `W` words at `rsi = A` into `4 R` limbs at `r11 = C`. -/
theorem to52_ok (hl : LayOk l) {s : State} {A C : Addr} (hA : s.gpr .rsi = A) (hC : s.gpr .r11 = C)
    (h12 : s.gpr .r12 = mask52) (hrd : ∀ i < l.W, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * i)) 8)
    (hwr : ∀ j < l.L, InRegions s.wr (C + BitVec.ofNat 64 (l.off j)) 8)
    (hsep : ∀ m m' : Mem, Outside C 0 l.NB m m' → ∀ i < l.W, word m' A (8 * i) = word m A (8 * i)) :
    WP isa (.block (to52 l)) s fun s' =>
      (∀ j < l.L, word s'.mem C (l.off j) = BitVec.ofNat 64 (limbN (wv s.mem A 0 l.W) j)) ∧
      Outside C 0 l.NB s.mem s'.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rbp] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hD := hl.D_bounds
  rw [to52_eq]
  suffices h : ∀ n ≤ l.L, WP isa (.block ((List.range n).flatMap (l52 l))) s fun s' =>
      (∀ j < n, word s'.mem C (l.off j) = BitVec.ofNat 64 (limbN (wv s.mem A 0 l.W) j)) ∧
      Outside C 0 l.NB s.mem s'.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rbp] s s' ∧ s'.mxcsr = s.mxcsr from
    h l.L (Nat.le_refl _)
  intro n
  induction n with
  | zero => intro _; exact WP.block_nil ⟨fun _ h => absurd h (by omega), Outside.refl _ _ _ _,
      VG.Proof.MlKem.X86_64.Keep.refl _ _, rfl⟩
  | succ n ih =>
    intro hn
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨v, o, k, x⟩ => ?_
    have hwv : wv t.mem A 0 l.W = wv s.mem A 0 l.W := VG.Proof.Bignum.wv_congr fun i hi => by
      rw [Nat.zero_add]; exact hsep _ _ o i hi
    refine WP.mono (l52_ok (j := n) (A := A) (C := C) ((k.gpr (by decide)).trans hA)
      ((k.gpr (by decide)).trans hC) ((k.gpr (by decide)).trans h12)
      (fun i hi => by rw [k.2.1, k.2.2]; exact hrd i hi) (by rw [k.2.2]; exact hwr n (by omega)))
      fun t' ⟨m', k', x'⟩ => ⟨fun j hj => ?_, ?_, (k.trans k').mono (by decide), x'.trans x⟩
    · have := off_lt hl (j := n) (by omega)
      rw [m', hwv]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
      · have := off_lt hl (j := j) (by omega)
        have hs := off_sep hl (j := n) (q := j) (by omega) (by omega) (by omega)
        rw [(writeW_outside _ C _ (by omega)).word (by omega) (by omega)]
        exact v j hj
      · exact VG.Proof.Bignum.word_writeW_self _ _ _ _
    · have := off_lt hl (j := n) (by omega)
      rw [m']
      exact o.trans ((writeW_outside _ C _ (by omega)).mono (by omega) (by omega))

/-! ## Back to words -/

/-- The code OR'ing limb `j` into the word at bit `lo`. -/
def orj (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (lo j : Nat) : List Instr :=
  ([.mov .rcx (.mem (at_ .r11 (l.off j)))] : List Instr) ++
  (if lo ≤ 52 * j then (if 52 * j = lo then [] else shl .rcx (52 * j - lo))
    else [.shift .shr .rcx (lo - 52 * j)]) ++
  ([.alu .or .rax (.reg .rcx)] : List Instr)

theorem orj_writes (lo j : Nat) :
    VG.Proof.MlKem.X86_64.writesOnly [.rax, .rcx, .rbp] (.block (orj l lo j)) = true := by
  unfold orj
  split
  · split <;> rfl
  · rfl

/-- `rax |= cj lo j L`, for limb `j` of the word at bit `lo`. -/
theorem orj_ok {s : State} {C : Addr} {lo j : Nat} (h1 : 52 * j < lo + 64) (h2 : lo < 52 * j + 52)
    (hC : s.gpr .r11 = C) (hrd : InRegions (s.rd ++ s.wr) (C + BitVec.ofNat 64 (l.off j)) 8) :
    WP isa (.block (orj l lo j)) s fun s' =>
      s'.gpr .rax = s.gpr .rax ||| cj lo j (word s.mem C (l.off j)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rbp] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax, .rcx, .rbp] (Q := fun s' =>
    s'.gpr .rax = s.gpr .rax ||| cj lo j (word s.mem C (l.off j)) ∧ s'.mem = s.mem ∧
      s'.mxcsr = s.mxcsr) ?_ (orj_writes lo j)) fun s' ⟨⟨a, b, c⟩, k⟩ => ⟨a, k, b, c⟩
  unfold orj cj
  by_cases hlo : lo ≤ 52 * j
  · by_cases he : 52 * j = lo
    · simp only [he, Nat.le_refl, ite_true, List.cons_append, List.nil_append]
      xrun [eaG', hC, hrd]
      rfl
    · have hmc : (1 ≤ 64 - (52 * j - lo) ∧ 64 - (52 * j - lo) ≤ 63) = True := eq_true ⟨by omega, by omega⟩
      simp only [hlo, he, ite_true, ite_false, shl, List.cons_append, List.nil_append]
      xrun [eaG', hC, hrd, hmc]
      refine ⟨?_, rfl⟩
      rw [shl_eq' _ (by omega) (by omega)]
  · have hsc : (1 ≤ lo - 52 * j ∧ lo - 52 * j ≤ 63) = True := eq_true ⟨by omega, by omega⟩
    simp only [hlo, ite_false, List.cons_append, List.nil_append]
    xrun [eaG', hC, hrd, hsc]
    rfl

/-- The limbs with bits in the word at bit `lo`. -/
def js (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (lo : Nat) : List Nat := (List.range l.L).filter fun j => 52 * j < lo + 64 ∧ lo < 52 * j + 52

/-- The word at bit `lo` of a number of `4 R` limbs below `2⁵²`. -/
theorem foldl_cj {Ls : Nat → BitVec 64} (hL : ∀ j, (Ls j).toNat < 2 ^ 52) (lo : Nat) :
    (js l lo).foldl (fun a j => a ||| cj lo j (Ls j)) 0 =
      BitVec.ofNat 64 (lval (fun j => (Ls j).toNat) l.L / 2 ^ lo % 2 ^ 64) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_foldl_or, BitVec.getLsbD_ofNat, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    testBit_lval hL]
  have z : (0 : BitVec 64).getLsbD i = false := by simp
  rw [z, Bool.false_or]
  simp only [hi, decide_true, Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, js, List.mem_filter, List.mem_range, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro ⟨j, ⟨hj, h1, h2⟩, hb⟩
    rw [cj_bit h1 h2 hi] at hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨hle, hb⟩ := hb
    have hlt : lo + i - 52 * j < 52 := by
      by_contra h
      rw [AmmSym.testBit_hi (hL j) (by omega)] at hb
      exact Bool.false_ne_true hb
    refine ⟨by omega, ?_⟩
    rw [show (i + lo) / 52 = j by omega, show (i + lo) % 52 = lo + i - 52 * j by omega]
    exact hb
  · rintro ⟨hlt, hb⟩
    refine ⟨(i + lo) / 52, ⟨by omega, by omega, by omega⟩, ?_⟩
    rw [cj_bit (by omega) (by omega) hi]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, by rw [show lo + i - 52 * ((i + lo) / 52) = (i + lo) % 52 by omega]; exact hb⟩

/-- The limbs of `xs` OR'ed into `rax`. -/
theorem orList_ok {C : Addr} {lo : Nat} :
    ∀ (xs : List Nat) (s : State), (∀ j ∈ xs, 52 * j < lo + 64 ∧ lo < 52 * j + 52 ∧ j < l.L) → s.gpr .r11 = C →
      (∀ j < l.L, InRegions (s.rd ++ s.wr) (C + BitVec.ofNat 64 (l.off j)) 8) →
      WP isa (.block (xs.flatMap (orj l lo))) s fun s' =>
        s'.gpr .rax = xs.foldl (fun a j => a ||| cj lo j (word s.mem C (l.off j))) (s.gpr .rax) ∧
        VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rbp] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr
  | [], s, _, _, _ => WP.block_nil ⟨rfl, VG.Proof.MlKem.X86_64.Keep.refl _ _, rfl, rfl⟩
  | j :: xs, s, hxs, hC, hrd => by
    obtain ⟨h1, h2, hj⟩ := hxs j (List.mem_cons_self ..)
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (orj_ok h1 h2 hC (hrd j hj)) fun t ⟨a, k, m, x⟩ => ?_
    refine WP.mono (orList_ok xs t (fun j hj => hxs j (List.mem_cons_of_mem _ hj)) ((k.gpr (by decide)).trans hC)
      (fun j hj => by rw [k.2.1, k.2.2]; exact hrd j hj)) fun t' ⟨a', k', m', x'⟩ =>
        ⟨?_, (k.trans k').mono (by decide), m'.trans m, x'.trans x⟩
    rw [a', a, m, List.foldl_cons]

/-- Word `w` of `to64`. -/
def w64 (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (w : Nat) : List Instr :=
  (Instr.mov32 .rax (.imm 0) :: (js l (64 * w)).flatMap (orj l (64 * w))) ++ [.store (at_ .r8 (8 * w)) .rax]

theorem to64_eq : to64 l = (List.range (l.W + 1)).flatMap (w64 l) := rfl

/-- The limbs at `C` as numbers, zero above `4 R`. -/
def limbsAt (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (m : Mem) (C : Addr) (j : Nat) : BitVec 64 :=
  if j < l.L then word m C (l.off j) else 0

/-- Word `w` of the `4 R` limbs below `2⁵²` at `r11 = C`, into `r8 + 8 w`. -/
theorem w64_ok {s : State} {C D' : Addr} {w : Nat} (hC : s.gpr .r11 = C) (h8 : s.gpr .r8 = D')
    (hrd : ∀ j < l.L, InRegions (s.rd ++ s.wr) (C + BitVec.ofNat 64 (l.off j)) 8)
    (hwr : InRegions s.wr (D' + BitVec.ofNat 64 (8 * w)) 8)
    (hL : ∀ j < l.L, (word s.mem C (l.off j)).toNat < 2 ^ 52) :
    WP isa (.block (w64 l w)) s fun s' =>
      s'.mem = s.mem.writeW (off D' (8 * w))
        (BitVec.ofNat 64 (lval (fun j => (limbsAt l s.mem C j).toNat) l.L / 2 ^ (64 * w) % 2 ^ 64)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rbp] s s' ∧ s'.mxcsr = s.mxcsr := by
  rw [w64, List.cons_append, WP.block_cons_iff]
  refine ⟨s.setReg32 .rax 0, rfl, ?_⟩
  have g₀ : ∀ r, r ≠ .rax → (s.setReg32 .rax 0).gpr r = s.gpr r := fun r hr => by
    rw [State.setReg32, RegUpd.gpr_setReg_of_ne _ _ hr]
  rw [WP.block_append_iff]
  refine WP.mono (orList_ok (C := C) (lo := 64 * w) (js l (64 * w)) _ (fun j hj => by
      simp only [js, List.mem_filter, List.mem_range, decide_eq_true_eq] at hj; exact ⟨hj.2.1, hj.2.2, hj.1⟩)
    ((g₀ _ (by decide)).trans hC) hrd) fun t ⟨a, k, m, x⟩ => ?_
  have hlm : (js l (64 * w)).foldl (fun a j => a ||| cj (64 * w) j
      (word (s.setReg32 .rax 0).mem C (l.off j))) ((s.setReg32 .rax 0).gpr .rax) =
      BitVec.ofNat 64 (lval (fun j => (limbsAt l s.mem C j).toNat) l.L / 2 ^ (64 * w) % 2 ^ 64) := by
    rw [← foldl_cj (Ls := limbsAt l s.mem C) (fun j => by
      unfold limbsAt; split
      · exact hL j (by assumption)
      · simp) (64 * w)]
    have e0 : (s.setReg32 .rax 0).gpr .rax = 0 := by rw [State.setReg32, RegUpd.gpr_setReg_self]; rfl
    rw [e0]
    refine foldl_congr' _ fun a j hj => ?_
    simp only [js, List.mem_filter, List.mem_range] at hj
    simp only [limbsAt, hj.1, ite_true]; rfl
  have hst : InRegions t.wr (D' + BitVec.ofNat 64 (8 * w)) 8 := by rw [k.2.2]; exact hwr
  have h8t : t.gpr .r8 = D' := by rw [k.gpr (by decide), g₀ _ (by decide)]; exact h8
  rw [WP.block_cons_iff]
  refine ⟨{ t with mem := t.mem.writeW (D' + BitVec.ofNat 64 (8 * w)) (t.gpr .rax) }, by
    simp only [exec, eaG', h8t, State.store64, hst, ite_true], WP.block_nil ⟨?_, ?_, x⟩⟩
  · show t.mem.writeW _ (t.gpr .rax) = _
    rw [a, hlm, m]; rfl
  · exact ⟨fun r hr => by
      show t.gpr r = s.gpr r
      rw [k.gpr hr, g₀ _ (fun h => hr (by simp [h]))], k.2.1, k.2.2⟩

/-- The `4 R` limbs below `2⁵²` at `r11 = C` into `W + 1` words at `r8 = D'`. -/
theorem to64_ok {s : State} {C D' : Addr} (hC : s.gpr .r11 = C) (h8 : s.gpr .r8 = D')
    (hrd : ∀ j < l.L, InRegions (s.rd ++ s.wr) (C + BitVec.ofNat 64 (l.off j)) 8)
    (hwr : ∀ w < l.W + 1, InRegions s.wr (D' + BitVec.ofNat 64 (8 * w)) 8)
    (hL : ∀ j < l.L, (word s.mem C (l.off j)).toNat < 2 ^ 52)
    (hw : 8 * (l.W + 1) + 8 ≤ 2 ^ 64)
    (hsep : ∀ m m' : Mem, Outside D' 0 (8 * (l.W + 1)) m m' → ∀ j < l.L,
      word m' C (l.off j) = word m C (l.off j)) :
    WP isa (.block (to64 l)) s fun s' =>
      (∀ w < l.W + 1, word s'.mem D' (8 * w) =
        BitVec.ofNat 64 (lval (fun j => (limbsAt l s.mem C j).toNat) l.L / 2 ^ (64 * w) % 2 ^ 64)) ∧
      Outside D' 0 (8 * (l.W + 1)) s.mem s'.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rbp] s s' ∧
      s'.mxcsr = s.mxcsr := by
  rw [to64_eq]
  suffices h : ∀ n ≤ l.W + 1, WP isa (.block ((List.range n).flatMap (w64 l))) s fun s' =>
      (∀ w < n, word s'.mem D' (8 * w) =
        BitVec.ofNat 64 (lval (fun j => (limbsAt l s.mem C j).toNat) l.L / 2 ^ (64 * w) % 2 ^ 64)) ∧
      Outside D' 0 (8 * (l.W + 1)) s.mem s'.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rcx, .rbp] s s' ∧
      s'.mxcsr = s.mxcsr from
    h (l.W + 1) (Nat.le_refl _)
  intro n
  induction n with
  | zero => intro _; exact WP.block_nil ⟨fun _ h => absurd h (by omega), Outside.refl _ _ _ _,
      VG.Proof.MlKem.X86_64.Keep.refl _ _, rfl⟩
  | succ n ih =>
    intro hn
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨v, o, k, x⟩ => ?_
    have hlim : ∀ j, limbsAt l t.mem C j = limbsAt l s.mem C j := fun j => by
      unfold limbsAt; split
      · exact hsep _ _ o j (by assumption)
      · rfl
    refine WP.mono (w64_ok (w := n) ((k.gpr (by decide)).trans hC) ((k.gpr (by decide)).trans h8)
      (fun j hj => by rw [k.2.1, k.2.2]; exact hrd j hj) (by rw [k.2.2]; exact hwr n (by omega))
      (fun j hj => by rw [hsep _ _ o j hj]; exact hL j hj))
      fun t' ⟨m', k', x'⟩ => ⟨fun w hw => ?_, ?_, (k.trans k').mono (by decide), x'.trans x⟩
    · simp only [hlim] at m'
      rw [m']
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hw) with hw | rfl
      · rw [(writeW_outside _ D' _ (by omega)).word (by omega) (by omega)]
        exact v w hw
      · exact VG.Proof.Bignum.word_writeW_self _ _ _ _
    · rw [m']
      exact o.trans ((writeW_outside _ D' _ (by omega)).mono (by omega) (by omega))

/-! ## The numbers -/

theorem wv_digitsG {m : Mem} {P : Addr} {V : Nat} :
    ∀ n, (∀ w < n, word m P (8 * w) = BitVec.ofNat 64 (V / 2 ^ (64 * w) % 2 ^ 64)) → wv m P 0 n = V % 2 ^ (64 * n)
  | 0, _ => by simp [VG.Proof.Bignum.wv, Nat.mod_one]
  | n + 1, h => by
    rw [VG.Proof.Bignum.wv, wv_digitsG n fun w hw => h w (by omega), Nat.zero_add, h n (by omega),
      BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide), Nat.mul_succ, Nat.pow_add, Nat.mod_mul]

/-- The value of the limbs `to52` writes: the number, below `2^(64 W)`. -/
theorem val_to52 (hl : LayOk l) {m : Mem} {A : Addr} : lval (limbN (wv m A 0 l.W)) l.L = wv m A 0 l.W := by
  have h1 := VG.Proof.Bignum.wv_lt m A 0 l.W
  have h2 := pow2_le (a := 64 * l.W) (b := 52 * l.L) (conv_bounds hl).2.1
  rw [lval_limbN]
  generalize 2 ^ (64 * l.W) = a at h1 h2
  generalize 2 ^ (52 * l.L) = b at h2 ⊢
  exact Nat.mod_eq_of_lt (by omega)

/-- The words `to64` writes, for a value below twice a number of `W` words. -/
theorem wv_to64_lt {m m₀ : Mem} {D' A : Addr} {d V : Nat} (hV : V < 2 * wv m₀ A d l.W)
    (h : ∀ w < l.W + 1, word m D' (8 * w) = BitVec.ofNat 64 (V / 2 ^ (64 * w) % 2 ^ 64)) :
    wv m D' 0 (l.W + 1) = V := by
  have h4 : V < 2 ^ (64 * (l.W + 1)) := by
    have := VG.Proof.Bignum.wv_lt m₀ A d l.W
    rw [Nat.mul_succ, Nat.pow_add]
    generalize 2 ^ (64 * l.W) = a at this ⊢
    have : 2 ≤ 2 ^ 64 := Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ 64 by decide)
    have := Nat.mul_le_mul_left a this
    omega
  rw [wv_digitsG (l.W + 1) h]
  exact Nat.mod_eq_of_lt h4

end VG.Proof.Bignum.X86_64.Ifma
