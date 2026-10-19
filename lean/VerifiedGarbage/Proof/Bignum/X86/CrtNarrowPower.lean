module

public import VerifiedGarbage.Impl.Bignum.X86.CrtCore
public import VerifiedGarbage.Proof.Bignum.X86.CrtFactorPower
public import VerifiedGarbage.Proof.Bignum.X86.CrtFactorFrame
public import VerifiedGarbage.Proof.Bignum.X86.CrtFrame
public import VerifiedGarbage.Proof.Bignum.X86.CheckedPreparePrime
public import VerifiedGarbage.Proof.Bignum.X86.ReduceOperand
public import VerifiedGarbage.Proof.Bignum.WordsPrefix
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Dsa.X86.RandomDraw

/-! # A factor's exponentiation at half the modulus's width

`narrowPower` computes what `factorPower` does (`factorPower_ok`) when the
factor and its exponent fit `half n` words: the input reduced modulo the
factor at the modulus's width, then raised to the exponent in a context of
`half n` words, which lies within the modulus-width context's slots.
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.Crt

/-- Changes within ranges each of which lies within one of `rs'`. -/
theorem Outs.within {base : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    (hr : ∀ q ∈ rs, ∃ r ∈ rs', r.1 ≤ q.1 ∧ q.1 + q.2 ≤ r.1 + r.2) : Outs base rs' m m' :=
  fun x hx => h x fun q hq => by
    obtain ⟨r, hr', lo, hi⟩ := hr q hq
    have := hx r hr'
    omega

/-- A change within one of `rs`. -/
theorem Outside.within {base : Addr} {o n : Nat} {rs : List (Nat × Nat)} {m m' : Mem}
    (h : Outside base o n m m') {r : Nat × Nat} (hr : r ∈ rs) (lo : r.1 ≤ o) (hi : o + n ≤ r.1 + r.2) :
    Outs base rs m m' :=
  fun x hx => h x (by have := hx r hr; omega)

theorem half_pos {n : Nat} (hn : 0 < n) : 0 < half n := by unfold half; omega

theorem half_le (n : Nat) : half n ≤ n := by unfold half; omega

/-- The narrow context lies within the modulus-width context. -/
theorem narrow_fits (n : Nat) : contextBytes (half n) ≤ contextBytes n := by
  unfold contextBytes slot stride half; omega

/-- A context's changes, as changes of the modulus-width context. -/
theorem context_frame {n output : Nat} {base : Addr} {m m' : Mem} {h : Nat} (hh : h ≤ n)
    (O : Outs base (primeSetupRanges h ++ exponentRanges h (2 * h)) m m') :
    Outs base (factorRanges n output) m m' := by
  refine Outs.within (prime_arithmetic_frame O) ?_
  intro q hq
  simp only [arithmeticRanges, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact ⟨(0, 8), by simp [factorRanges, arithmeticRanges], by omega, by omega⟩
  · refine ⟨(64, contextBytes n - 64), by simp [factorRanges, arithmeticRanges], by omega, ?_⟩
    have : contextBytes h ≤ contextBytes n := by unfold contextBytes slot stride; omega
    have : 64 ≤ contextBytes h := by unfold contextBytes slot stride; omega
    dsimp only
    omega

/-- A change within the modulus-width context's slots. -/
theorem slots_frame {n output o len : Nat} {base : Addr} {m m' : Mem}
    (O : Outside base o len m m') (lo : 64 ≤ o) (hi : o + len ≤ contextBytes n) :
    Outs base (factorRanges n output) m m' :=
  Outside.within O (r := (64, contextBytes n - 64)) (by simp [factorRanges, arithmeticRanges]) lo
    (by dsimp only; omega)

/-- Zeros of `4 n` words, then `h` words copied over their start: both the
`n`-word and the `2 n`-word values are the copied one. -/
theorem zeroCopy_ok {s : State} {base : Addr} {bytes n h src dst : Nat}
    (hs : Scr s base bytes) (hh : 0 < h) (hhn : h ≤ n) (hsrc : src + 8 * h ≤ bytes)
    (hdst : dst + 16 * n ≤ bytes) (apart : dst + 16 * n ≤ src ∨ src + 8 * h ≤ dst) :
    WP isa (.seq (zerosW dst (4 * n)) (copyArray h src dst)) s fun t =>
      wordsVal t.mem base dst n = wordsVal s.mem base src h ∧
      wordsVal t.mem base dst (2 * n) = wordsVal s.mem base src h ∧
      Outside base dst (16 * n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have nw := hs.nowrap
  refine WP.seq (WP.mono (zerosW_ok hs (by omega) (by omega)) fun u ⟨O, Z, K⟩ => ?_)
  have Src : wordsVal u.mem base src h = wordsVal s.mem base src h := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact O.val32 (by omega) (by omega)
  refine WP.mono (copyArray_ok (hs.of_keeps K (by decide)) hh hsrc (by omega) (by omega))
    fun t ⟨V, Ot, Kt⟩ => ?_
  have value (k : Nat) (lo : h ≤ k) (hi : k ≤ 2 * n) :
      wordsVal t.mem base dst k = wordsVal s.mem base src h := by
    have upper : val32 u.mem base (dst + 4 * (2 * h)) (2 * k - 2 * h) = 0 := by
      rw [show 4 * n = 2 * h + ((2 * k - 2 * h) + (4 * n - 2 * k)) by omega] at Z
      exact (VG.Proof.Bignum.val32_zero_split
        (VG.Proof.Bignum.val32_zero_split Z).2).1
    rw [wordsVal_eq_val32, show 2 * k = 2 * h + (2 * k - 2 * h) by omega, val32_append,
      Ot.val32 (d := dst + 4 * (2 * h)) (k := 2 * k - 2 * h) (by omega) (by omega),
      upper, Nat.mul_zero, Nat.add_zero, ← wordsVal_eq_val32, V, Src]
  refine ⟨value n hhn (by omega), value (2 * n) (by omega) (Nat.le_refl _), ?_,
    (K.mono (by decide)).trans Kt⟩
  have O' : Outside base dst (16 * n) s.mem u.mem := by
    simpa only [show 4 * (4 * n) = 16 * n by omega] using O
  exact O'.trans (Ot.mono (Nat.le_refl _) (by omega))

theorem reduceInput_ok {s : State} {base : Addr} {bytes n prime output : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32) (hz : size n ≤ bytes)
    (hp : 9 ≤ prime) (hp' : prime < 15) (ho : 16 ≤ output) (ho' : output < 20) :
    WP isa (reduceInput n prime output) s fun t =>
      wordsVal t.mem base (slot n output) n =
        wordsVal s.mem base (slot n inputSlot) n % safePrime (wordsVal s.mem base (slot n prime) n) ∧
      Outs base (factorRanges n output) s.mem t.mem ∧ Keeps powerClob s t := by
  have nw := hs.nowrap
  have fits := context_fits n
  have bp := slot_bound (n := n) (show prime < 20 by omega)
  have bo := slot_bound (n := n) ho'
  have bi := slot_bound (n := n) (show inputSlot < 20 by decide)
  have sp := Nat.mul_le_mul_right (stride n) hp
  have so := Nat.mul_le_mul_right (stride n) (show 9 ≤ output by omega)
  have sop := slot_sep (n := n) (show prime ≠ output by omega)
  have sip := slot_sep (n := n) (show prime ≠ inputSlot by unfold inputSlot; omega)
  have fit : size n ≤ 2 ^ 64 := by omega
  simp only [contextBytes, size, slot, stride, inputSlot] at fits bp bo bi sp so sop sip fit hz
  unfold reduceInput
  refine WP.seq (WP.mono (copyArray_ok hs hn (src := slot n prime) (dst := slot n 0)
    (by simp only [slot, stride]; omega) (by simp only [slot, stride]; omega)
    (.inr (.inl (by simp only [slot, stride]; omega)))) fun u₁ ⟨P₁, O₁, K₁⟩ => ?_)
  refine WP.seq (WP.mono (copyArray_ok (hs.of_keeps K₁ (by decide)) hn (src := slot n inputSlot)
    (dst := slot n 5) (by simp only [slot, stride, inputSlot]; omega) (by simp only [slot, stride]; omega)
    (.inr (.inl (by simp only [slot, stride, inputSlot]; omega)))) fun u₂ ⟨X₂, O₂, K₂⟩ => ?_)
  have K₁₂ := K₁.trans K₂
  refine WP.seq (WP.mono (checkedPreparePrime_ok (hs.of_keeps K₁₂ (by decide)) hn hn32
    (by simp only [contextBytes, slot, stride]; omega)) fun u₃ ⟨C₃, One₃, R₃, O₃, K₃⟩ => ?_)
  refine WP.seq (WP.mono (reduceOperand_ok C₃ (.inl rfl) One₃ R₃) fun u₄ ⟨C₄, V₄, O₄, K₄⟩ => ?_)
  refine WP.mono (copyArray_ok C₄.scr hn (src := slot n 5) (dst := slot n output)
    (by simp only [slot, stride]; omega) (by simp only [slot, stride]; omega)
    (.inr (.inr (by simp only [slot, stride]; omega)))) fun t ⟨V₅, O₅, K₅⟩ => ?_
  -- The factor and the input, through the copies and the context's setup.
  have prime₂ : wordsVal u₂.mem base (slot n 0) n = wordsVal s.mem base (slot n prime) n := by
    rw [O₂.wordsVal (by simp only [slot, stride]; omega) (by simp only [slot, stride]; omega), P₁]
  have input₂ : wordsVal u₂.mem base (slot n 5) n = wordsVal s.mem base (slot n inputSlot) n := by
    rw [X₂, O₁.wordsVal (by simp only [slot, stride, inputSlot]; omega) (by simp only [slot, stride, inputSlot]; omega)]
  have input₃ : wordsVal u₃.mem base (slot n 5) n = wordsVal u₂.mem base (slot n 5) n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    apply O₃.val32 _ (by simp only [slot, stride]; omega)
    intro r hr
    simp only [primeSetupRanges, setupRanges, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega
  refine ⟨?_, ?_, ?_⟩
  · rw [V₅, V₄, input₃, input₂, prime₂]
  · have o₃ := context_frame (output := output) (Nat.le_refl n)
      (O₃.mono (by intro r hr; exact List.mem_append_left _ hr))
    have o₄ : Outs base (factorRanges n output) u₃.mem u₄.mem := context_frame (Nat.le_refl n) (O₄.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [exponentRanges, productRanges]))
    exact ((((slots_frame O₁ (by simp only [slot, stride]; omega) (by simp only [contextBytes, slot, stride]; omega)).trans
      (slots_frame O₂ (by simp only [slot, stride]; omega) (by simp only [contextBytes, slot, stride]; omega))).trans
      o₃).trans o₄).trans (Outside.within O₅ (r := (slot n output, 16 * n)) (by simp [factorRanges]) (Nat.le_refl _)
        (by dsimp only; omega))
  · exact ((((K₁₂.mono (by decide)).trans K₃).trans (K₄.mono (by decide))).trans (K₅.mono (by decide)))

/-- The reduced input is below `2 ^ (64 h)` when the factor is. -/
theorem reduced_fits {x p h : Nat} (hh : 0 < h) (hp : p < 2 ^ (64 * h)) :
    x % safePrime p < 2 ^ (64 * h) := by
  have pos : 0 < safePrime p := by unfold safePrime; split <;> omega
  have le : safePrime p ≤ p ∨ safePrime p = 3 := by unfold safePrime; split <;> omega
  have big : 3 < 2 ^ (64 * h) :=
    Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) (show 64 ≤ 64 * h by omega))
  have := Nat.mod_lt x pos
  omega

theorem narrowPower_ok {s : State} {base : Addr} {bytes n prime exponent output : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32) (hz : size n ≤ bytes)
    (hp : 9 ≤ prime) (hp' : prime < 15) (he : 9 ≤ exponent) (he' : exponent < 16)
    (ho : 16 ≤ output) (ho' : output < 20) :
    WP isa (narrowPower n prime exponent output) s fun t =>
      (wordsVal s.mem base (slot n prime) n < 2 ^ (64 * half n) →
        wordsVal s.mem base (slot n exponent) n < 2 ^ (64 * half n) →
        let result := wordsVal s.mem base (slot n inputSlot) n ^ wordsVal s.mem base (slot n exponent) n %
          safePrime (wordsVal s.mem base (slot n prime) n)
        wordsVal t.mem base (slot n output) n = result ∧ wordsVal t.mem base (slot n output) (2 * n) = result) ∧
      Outs base (factorRanges n output) s.mem t.mem ∧ Keeps powerClob s t := by
  have nw := hs.nowrap
  have hh := half_pos hn
  have hhn := half_le n
  have fit : size n ≤ 2 ^ 64 := by omega
  have bp := slot_bound (n := n) (show prime < 20 by omega)
  have be := slot_bound (n := n) (show exponent < 20 by omega)
  have bo := slot_bound (n := n) ho'
  have sp := Nat.mul_le_mul_right (stride n) hp
  have se := Nat.mul_le_mul_right (stride n) he
  have so := Nat.mul_le_mul_right (stride n) ho
  have n9 : slot (half n) 8 + 16 * half n + 8 ≤ slot n 9 := by unfold slot stride half; omega
  simp only [size, slot, stride] at bp be bo sp se so n9 hz fit
  unfold narrowPower loadNarrow
  refine WP.seq (WP.mono (reduceInput_ok hs hn hn32 hz hp hp' ho ho') fun u₁ ⟨R, O₁, K₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.seq (WP.seq (WP.mono (copyArray_ok hs₁ hh (src := slot n prime) (dst := slot (half n) 0)
    (by simp only [slot, stride]; omega) (by simp only [slot, stride] at n9 ⊢; omega)
    (.inr (.inl (by simp only [slot, stride] at n9 ⊢; omega)))) fun u₂ ⟨P₂, O₂, K₂⟩ =>
    WP.seq (WP.mono (copyArray_ok (hs₁.of_keeps K₂ (by decide)) hh (src := slot n output)
    (dst := slot (half n) 5) (by simp only [slot, stride]; omega) (by simp only [slot, stride] at n9 ⊢; omega)
    (.inr (.inl (by simp only [slot, stride] at n9 ⊢; omega)))) fun u₃ ⟨X₃, O₃, K₃⟩ =>
    WP.mono (copyArray_ok ((hs₁.of_keeps K₂ (by decide)).of_keeps K₃ (by decide)) hh
    (src := slot n exponent) (dst := slot (half n) 8) (by simp only [slot, stride]; omega)
    (by simp only [slot, stride] at n9 ⊢; omega)
    (.inr (.inl (by simp only [slot, stride] at n9 ⊢; omega)))) fun u₄ ⟨E₄, O₄, K₄⟩ => ?_)))
  have K₂₄ := (K₂.trans K₃).trans K₄
  refine WP.seq (WP.mono (checkedPrimePower_ok (hs₁.of_keeps K₂₄ (by decide)) hh
    (by unfold half; omega) (Nat.le_trans (narrow_fits n) (Nat.le_trans (context_fits n) (by
      simp only [size, slot, stride]; omega)))) fun u₅ ⟨C₅, V₅, O₅, K₅⟩ => ?_)
  refine WP.mono (zeroCopy_ok C₅.scr hh hhn (src := slot (half n) 6) (dst := slot n output)
    (by simp only [slot, stride] at n9 ⊢; omega) (by simp only [slot, stride]; omega)
    (.inr (by simp only [slot, stride] at n9 ⊢; omega))) fun t ⟨W₁, W₂, O₆, K₆⟩ => ?_
  -- The narrow operands, from their modulus-width slots.
  have prime₁ : wordsVal u₁.mem base (slot n prime) n = wordsVal s.mem base (slot n prime) n :=
    factor_value O₁ hp (by omega) (by omega) (by omega) (by simp only [size, slot, stride]; omega)
  have exp₁ : wordsVal u₁.mem base (slot n exponent) n = wordsVal s.mem base (slot n exponent) n :=
    factor_value O₁ he (by omega) (by omega) (by omega) (by simp only [size, slot, stride]; omega)
  have prime₅ : wordsVal u₄.mem base (slot (half n) 0) (half n) =
      wordsVal s.mem base (slot n prime) n % 2 ^ (64 * half n) := by
    rw [O₄.wordsVal (by simp only [slot, stride]; omega) (by simp only [slot, stride]; omega),
      O₃.wordsVal (by simp only [slot, stride]; omega) (by simp only [slot, stride]; omega), P₂,
      VG.Proof.Bignum.wordsVal_prefix _ _ _ hhn, prime₁]
  have input₅ : wordsVal u₄.mem base (slot (half n) 5) (half n) =
      wordsVal u₁.mem base (slot n output) n % 2 ^ (64 * half n) := by
    rw [O₄.wordsVal (by simp only [slot, stride]; omega) (by simp only [slot, stride]; omega), X₃,
      O₂.wordsVal (by simp only [slot, stride] at n9 ⊢; omega) (by simp only [slot, stride]; omega),
      VG.Proof.Bignum.wordsVal_prefix _ _ _ hhn]
  have exp₅ : wordsVal u₄.mem base (slot (half n) 8) (half n) =
      wordsVal s.mem base (slot n exponent) n % 2 ^ (64 * half n) := by
    rw [E₄, O₃.wordsVal (by simp only [slot, stride] at n9 ⊢; omega) (by simp only [slot, stride]; omega),
      O₂.wordsVal (by simp only [slot, stride] at n9 ⊢; omega) (by simp only [slot, stride]; omega),
      VG.Proof.Bignum.wordsVal_prefix _ _ _ hhn, exp₁]
  refine ⟨fun pfit efit => ?_, ?_, ?_⟩
  · have value : wordsVal u₅.mem base (slot (half n) 6) (half n) =
        wordsVal s.mem base (slot n inputSlot) n ^ wordsVal s.mem base (slot n exponent) n %
          safePrime (wordsVal s.mem base (slot n prime) n) := by
      rw [V₅, prime₅, input₅, exp₅, Nat.mod_eq_of_lt pfit, Nat.mod_eq_of_lt efit, R,
        Nat.mod_eq_of_lt (reduced_fits hh pfit), ← Nat.pow_mod]
    exact ⟨W₁.trans value, W₂.trans value⟩
  · have f₂ := slots_frame (n := n) (output := output) O₂ (by simp only [slot, stride]; omega)
      (by simp only [contextBytes, slot, stride] at n9 ⊢; omega)
    have f₃ := slots_frame (n := n) (output := output) O₃ (by simp only [slot, stride]; omega)
      (by simp only [contextBytes, slot, stride] at n9 ⊢; omega)
    have f₄ := slots_frame (n := n) (output := output) O₄ (by simp only [slot, stride]; omega)
      (by simp only [contextBytes, slot, stride] at n9 ⊢; omega)
    exact ((((O₁.trans f₂).trans f₃).trans f₄).trans (context_frame hhn O₅)).trans
      (Outside.within O₆ (r := (slot n output, 16 * n)) (by simp [factorRanges]) (Nat.le_refl _)
        (by dsimp only; omega))
  · exact (K₁.trans ((K₂₄.mono (by decide)).trans K₅)).trans (K₆.mono (by decide))

/-- The comparison of a factor's length with `8 half n`, into CF. -/
theorem lengthFits_ok {s : State} {base : Addr} {bytes n lenArg : Nat} {v : BitVec 32}
    (hn32 : 128 * n < 2 ^ 32) (A : CallArgument s base bytes lenArg v) :
    WP isa (.block (lengthFits n lenArg)) s fun w =>
      w.mem = s.mem ∧ Keeps [.eax] s w ∧ w.cf = some (decide (v.toNat < 8 * half n + 1)) := by
  unfold lengthFits
  refine wp_movS A.readSrc fun u U _ => VG.Proof.Dsa.X86.wp_cmpSc rfl fun w F C => WP.block_nil ?_
  have bound : 8 * half n + 1 < 2 ^ 32 := by unfold half; omega
  refine ⟨F.mem.trans U.mem, U.keeps.trans (F.keeps _), ?_⟩
  rw [C, U.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

theorem factorPowerFit_ok {s : State} {base : Addr} {bytes n prime exponent output lenArg : Nat}
    {v : BitVec 32} (hs : Scr s base bytes) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32) (hz : size n ≤ bytes)
    (hp : 9 ≤ prime) (hp' : prime < 15) (he : 9 ≤ exponent) (he' : exponent < 16)
    (ho : 16 ≤ output) (ho' : output < 20) (A : CallArgument s base bytes lenArg v) :
    WP isa (factorPowerFit n prime exponent output lenArg) s fun t =>
      ((v.toNat ≤ 8 * half n → wordsVal s.mem base (slot n prime) n < 2 ^ (64 * half n) ∧
          wordsVal s.mem base (slot n exponent) n < 2 ^ (64 * half n)) →
        let result := wordsVal s.mem base (slot n inputSlot) n ^ wordsVal s.mem base (slot n exponent) n %
          safePrime (wordsVal s.mem base (slot n prime) n)
        wordsVal t.mem base (slot n output) n = result ∧ wordsVal t.mem base (slot n output) (2 * n) = result) ∧
      Outs base (factorRanges n output) s.mem t.mem ∧ Keeps powerClob s t := by
  unfold factorPowerFit
  refine WP.seq (WP.mono (lengthFits_ok hn32 A) fun w ⟨M, Kw, cf⟩ => ?_)
  have hw := hs.of_keeps Kw (by decide)
  refine WP.ite _ cf (fun fits => ?_) (fun long => ?_)
  · refine WP.mono (narrowPower_ok hw hn hn32 hz hp hp' he he' ho ho') fun t ⟨V, O, K⟩ => ?_
    rw [M] at V O
    refine ⟨fun B => ?_, O, (Kw.mono (by decide)).trans K⟩
    have B' := B (by have := of_decide_eq_true fits; omega)
    exact V B'.1 B'.2
  · refine WP.mono (factorPower_ok hw hn hn32 hz hp (by omega) he he' ho ho') fun t ⟨V, W, O, K⟩ => ?_
    rw [M] at V W O
    exact ⟨fun _ => ⟨V, W⟩, O, (Kw.mono (by decide)).trans K⟩

/-- Changes within ranges of the working space leave the rest of memory. -/
theorem Outs.outside {base : Addr} {rs : List (Nat × Nat)} {bytes : Nat} {m m' : Mem}
    (h : Outs base rs m m') (hr : ∀ r ∈ rs, r.1 + r.2 ≤ bytes) : Outside base 0 bytes m m' :=
  fun x hx => h x fun r hr' => by have := hr r hr'; omega

theorem factor_outside {n output bytes : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (factorRanges n output) m m') (ho : output < 20) (hz : size n ≤ bytes) :
    Outside base 0 bytes m m' := by
  have fits := context_fits n
  have bo := slot_bound (n := n) ho
  have c9 : contextBytes n = slot n 9 := rfl
  have h9 := slot_header n 9
  refine Outs.outside O ?_
  intro r hr
  simp only [factorRanges, arithmeticRanges, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  unfold stride at bo
  rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega

end VG.Proof.Bignum.X86.Crt
