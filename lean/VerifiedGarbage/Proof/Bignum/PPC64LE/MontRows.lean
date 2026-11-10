module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRounds
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFios
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: it builds in parallel with `MontCore`'s other imports, and a change to `MontCore` does not re-check it.

/-!
# Montgomery multiplication on PPC64LE: the rows of the kernel's rounds

The kernel's rounds for `w` a multiple of 4 (`rounds4`) go over `T`, `b`
and `m` in chunks of four words, and over a group's four words of `a`, its
rows, in each chunk. A row adds `aᵢ b + uᵢ m`, for the chunk's words of `b`
and `m` (in registers, `bR`, `mR`), to the window of `T` (`accR` and `r26`,
with CA), and moves the window down a word: its low word drops out.

A row is three carry chains of four words (`prodChain_ok`, each word an
`addc` or `adde` of a product's low or high word): `mulB_ok` adds `aᵢ b` into
five words, `loM_ok` the low words of `uᵢ m`, with `r26` at word 4 and its
carry out, and `shiftM_ok` the high words, one word down. `row_arith` puts
them together: for the window's value `Vv` (its four words, and `r26` and
CA at word 4), `2⁶⁴ Vv' + o = Vv + aᵢ b + uᵢ m`, `o` the word that drops
out. The first chunk's rows (`rows0_ok`) choose `uᵢ` so that `o = 0` and
store it in `T`; the others' (`rowsT_ok`) store `o` and move `uᵢ` a chunk up.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Mont4

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Impl.Bignum.PPC64LE
open VG.Proof.Bignum.PPC64LE (Scr Keep off_add gpr_write)

/-! ## A chain of four products -/

/-- The low word of `a b`, or its high word. -/
def pv (hi : Bool) (a b : BitVec 64) : Nat := if hi then hiw a b else (a * b).toNat

/-- The value of four (or `n`) registers, the first the low word. -/
abbrev rv (s : State) (f : Nat → Reg) (n : Nat) : Nat := psum (fun j => (s.gpr (f j)).toNat) n

/-- A product's low or high word into `r22`. -/
theorem wp_prod {is : List Instr} {s : State} {Q : State → Prop} (hi : Bool) (a b : Reg)
    (k : ∀ t, W1 s t .r22 → (t.gpr .r22).toNat = pv hi (s.gpr a) (s.gpr b) → t.ca = s.ca → WP isa (.block is) t Q) :
    WP isa (.block ((if hi then Instr.mulhu else Instr.mul) .r22 a b :: is)) s Q := by
  cases hi
  · exact wp_mul fun t w e c => k t w (by rw [e]; rfl) c
  · exact wp_mulhu fun t w e c => k t w (by rw [e]; rfl) c

theorem psum4 (f : Nat → Nat) : psum f 4 = f 0 + 2 ^ 64 * f 1 + 2 ^ 128 * f 2 + 2 ^ 192 * f 3 := by
  simp only [psum, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.reduceMul]

theorem psum5 (f : Nat → Nat) : psum f 5 = psum f 4 + 2 ^ 256 * f 4 := rfl

/-- What a chain's registers must be: the destinations distinct, and none read
after it is written. -/
def ChainRegs (x : Reg) (p dst src : Nat → Reg) : Prop :=
  x ≠ .r22 ∧ (∀ j < 4, p j ≠ .r22 ∧ src j ≠ .r22 ∧ dst j ≠ .r22 ∧ dst j ≠ x) ∧ (∀ j < 4, ∀ k < 4, dst j ≠ p k) ∧
    ∀ j < 4, ∀ k < 4, j < k → dst j ≠ src k ∧ dst j ≠ dst k

instance (x : Reg) (p dst src : Nat → Reg) : Decidable (ChainRegs x p dst src) := by
  unfold ChainRegs; exact inferInstance

theorem keep_sub5 {s t : State} {a b c d e : Reg} {rs : List Reg} (h : Keep rs s t)
    (hr : ∀ r ∈ rs, r = a ∨ r = b ∨ r = c ∨ r = d ∨ r = e) : Keep [a, b, c, d, e] s t :=
  h.mono fun r h' => by
    rcases hr r h' with rfl | rfl | rfl | rfl | rfl <;> simp

/-- A chain of four products (`prodChain`): `dst := src + (lo or hi) (p x)`,
as a 256-bit sum, the carry out in CA. -/
theorem prodChain_ok {hi : Bool} {x : Reg} {p dst src : Nat → Reg} {is : List Instr} {s : State}
    {Q : State → Prop} (hr : ChainRegs x p dst src)
    (k : ∀ t, Keep [.r22, dst 0, dst 1, dst 2, dst 3] s t → t.mem = s.mem →
      rv t dst 4 + 2 ^ 256 * t.ca.toNat = rv s src 4 + psum (fun j => pv hi (s.gpr (p j)) (s.gpr x)) 4 →
      (t.gpr (dst 0)).toNat = ((s.gpr (src 0)).toNat + pv hi (s.gpr (p 0)) (s.gpr x)) % 2 ^ 64 →
      WP isa (.block is) t Q) :
    WP isa (.block (prodChain hi x p dst src ++ is)) s Q := by
  obtain ⟨hx, hA, hP, hS⟩ := hr
  have a0 := hA 0 (by decide); have a1 := hA 1 (by decide); have a2 := hA 2 (by decide); have a3 := hA 3 (by decide)
  have s01 := hS 0 (by decide) 1 (by decide) (by decide); have s02 := hS 0 (by decide) 2 (by decide) (by decide)
  have s03 := hS 0 (by decide) 3 (by decide) (by decide); have s12 := hS 1 (by decide) 2 (by decide) (by decide)
  have s13 := hS 1 (by decide) 3 (by decide) (by decide); have s23 := hS 2 (by decide) 3 (by decide) (by decide)
  show WP isa (.block ((if hi then Instr.mulhu else Instr.mul) .r22 (p 0) x :: .addc (dst 0) (src 0) .r22 ::
    (if hi then Instr.mulhu else Instr.mul) .r22 (p 1) x :: .adde (dst 1) (src 1) .r22 ::
    (if hi then Instr.mulhu else Instr.mul) .r22 (p 2) x :: .adde (dst 2) (src 2) .r22 ::
    (if hi then Instr.mulhu else Instr.mul) .r22 (p 3) x :: .adde (dst 3) (src 3) .r22 :: is)) s Q
  refine wp_prod hi (p 0) x fun t₁ w₁ e₁ c₁ => ?_
  refine wp_addc fun t₂ w₂ e₂ => ?_
  refine wp_prod hi (p 1) x fun t₃ w₃ e₃ c₃ => ?_
  refine wp_adde fun t₄ w₄ e₄ => ?_
  refine wp_prod hi (p 2) x fun t₅ w₅ e₅ c₅ => ?_
  refine wp_adde fun t₆ w₆ e₆ => ?_
  refine wp_prod hi (p 3) x fun t₇ w₇ e₇ c₇ => ?_
  refine wp_adde fun t₈ w₈ e₈ => ?_
  -- What each step read: the values on entry.
  have g₂ : ∀ r, r ≠ .r22 → r ≠ dst 0 → t₂.gpr r = s.gpr r := fun r h₁ h₂ => (w₂.gpr r h₂).trans (w₁.gpr r h₁)
  have g₄ : ∀ r, r ≠ .r22 → r ≠ dst 0 → r ≠ dst 1 → t₄.gpr r = s.gpr r := fun r h₁ h₂ h₃ =>
    (w₄.gpr r h₃).trans ((w₃.gpr r h₁).trans (g₂ r h₁ h₂))
  have g₆ : ∀ r, r ≠ .r22 → r ≠ dst 0 → r ≠ dst 1 → r ≠ dst 2 → t₆.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ =>
    (w₆.gpr r h₄).trans ((w₅.gpr r h₁).trans (g₄ r h₁ h₂ h₃))
  rw [w₁.gpr _ a0.2.1, e₁] at e₂
  rw [w₃.gpr _ a1.2.1, g₂ _ a1.2.1 (Ne.symm s01.1), e₃, g₂ _ a1.1 (Ne.symm (hP 0 (by decide) 1 (by decide))),
    g₂ _ hx (Ne.symm a0.2.2.2), c₃] at e₄
  rw [w₅.gpr _ a2.2.1, g₄ _ a2.2.1 (Ne.symm s02.1) (Ne.symm s12.1), e₅,
    g₄ _ a2.1 (Ne.symm (hP 0 (by decide) 2 (by decide))) (Ne.symm (hP 1 (by decide) 2 (by decide))),
    g₄ _ hx (Ne.symm a0.2.2.2) (Ne.symm a1.2.2.2), c₅] at e₆
  rw [w₇.gpr _ a3.2.1, g₆ _ a3.2.1 (Ne.symm s03.1) (Ne.symm s13.1) (Ne.symm s23.1), e₇,
    g₆ _ a3.1 (Ne.symm (hP 0 (by decide) 3 (by decide))) (Ne.symm (hP 1 (by decide) 3 (by decide)))
      (Ne.symm (hP 2 (by decide) 3 (by decide))),
    g₆ _ hx (Ne.symm a0.2.2.2) (Ne.symm a1.2.2.2) (Ne.symm a2.2.2.2), c₇] at e₈
  -- What the chain left: each destination as its step wrote it.
  have f0 : t₈.gpr (dst 0) = t₂.gpr (dst 0) := by
    rw [w₈.gpr _ s03.2, w₇.gpr _ a0.2.2.1, w₆.gpr _ s02.2, w₅.gpr _ a0.2.2.1, w₄.gpr _ s01.2, w₃.gpr _ a0.2.2.1]
  have f1 : t₈.gpr (dst 1) = t₄.gpr (dst 1) := by
    rw [w₈.gpr _ s13.2, w₇.gpr _ a1.2.2.1, w₆.gpr _ s12.2, w₅.gpr _ a1.2.2.1]
  have f2 : t₈.gpr (dst 2) = t₆.gpr (dst 2) := by rw [w₈.gpr _ s23.2, w₇.gpr _ a2.2.2.1]
  have hl := (t₂.gpr (dst 0)).isLt
  refine k t₈ (keep_sub5 (((((((w₁.keep.trans w₂.keep).trans w₃.keep).trans w₄.keep).trans w₅.keep).trans
      w₆.keep).trans w₇.keep).trans w₈.keep) fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h | h | h | h | h <;> subst h <;> simp)
    (by rw [w₈.mem, w₇.mem, w₆.mem, w₅.mem, w₄.mem, w₃.mem, w₂.mem, w₁.mem]) ?_ ?_
  · simp only [rv, psum4]
    rw [f0, f1, f2]
    simp only [Nat.reducePow] at e₂ e₄ e₆ e₈ ⊢
    omega
  · rw [f0]
    omega

/-! ## The three chains of a row -/

theorem aR0 : accR 0 = .r27 := rfl
theorem aR1 : accR 1 = .r28 := rfl
theorem aR2 : accR 2 = .r29 := rfl
theorem aR3 : accR 3 = .r30 := rfl
theorem aR4 : accR 4 = .r31 := rfl
theorem bR0 : bR 0 = .r14 := rfl
theorem bR1 : bR 1 = .r15 := rfl
theorem bR2 : bR 2 = .r16 := rfl
theorem bR3 : bR 3 = .r17 := rfl
theorem mR0 : mR 0 = .r18 := rfl
theorem mR1 : mR 1 = .r19 := rfl
theorem mR2 : mR 2 = .r20 := rfl
theorem mR3 : mR 3 = .r2 := rfl

theorem rv_lt (s : State) (f : Nat → Reg) (n : Nat) : rv s f n < 2 ^ (64 * n) := by
  induction n with
  | zero => exact Nat.one_pos
  | succ n ih =>
    have := (s.gpr (f n)).isLt
    have h := Nat.mul_le_mul_left (2 ^ (64 * n)) (show (s.gpr (f n)).toNat + 1 ≤ 2 ^ 64 by omega)
    rw [Nat.mul_add, Nat.mul_one, ← Nat.pow_add, show 64 * n + 64 = 64 * (n + 1) by omega] at h
    show rv s f n + 2 ^ (64 * n) * (s.gpr (f n)).toNat < _
    omega

/-- The low words and the high words of the products of `x` with four words. -/
theorem lohi_sum (s : State) (p : Nat → Reg) (x : BitVec 64) :
    psum (fun j => pv false (s.gpr (p j)) x) 4 + 2 ^ 64 * psum (fun j => pv true (s.gpr (p j)) x) 4 =
      rv s p 4 * x.toNat := by
  simp only [rv, psum4, pv, Bool.false_eq_true, ite_false, ite_true]
  have h0 := lo_hi (s.gpr (p 0)) x; have h1 := lo_hi (s.gpr (p 1)) x
  have h2 := lo_hi (s.gpr (p 2)) x; have h3 := lo_hi (s.gpr (p 3)) x
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
  simp only [hiw] at *
  omega

theorem pv_sum_congr {s t : State} {p : Nat → Reg} {x y : BitVec 64} (hi : Bool)
    (hp : ∀ j < 4, t.gpr (p j) = s.gpr (p j)) (hx : x = y) :
    psum (fun j => pv hi (t.gpr (p j)) x) 4 = psum (fun j => pv hi (s.gpr (p j)) y) 4 :=
  psum_congr fun j hj => by rw [hp j hj, hx]

theorem rv_congr {s t : State} {p : Nat → Reg} (n : Nat) (hp : ∀ j < n, t.gpr (p j) = s.gpr (p j)) :
    rv t p n = rv s p n :=
  psum_congr fun j hj => by rw [hp j hj]

theorem rv5 (s : State) (f : Nat → Reg) : rv s f 5 = rv s f 4 + 2 ^ 256 * (s.gpr (f 4)).toNat := rfl

theorem accR_succ (s : State) : rv s accR 5 = (s.gpr .r27).toNat + 2 ^ 64 * rv s (fun j => accR (j + 1)) 4 :=
  psum_shift _ 4

theorem accR_succ4 (s : State) : rv s (fun j => accR (j + 1)) 4 =
    (s.gpr .r28).toNat + 2 ^ 64 * (s.gpr .r29).toNat + 2 ^ 128 * (s.gpr .r30).toNat + 2 ^ 192 * (s.gpr .r31).toNat :=
  psum4 _

theorem accR4 (s : State) : rv s accR 4 =
    (s.gpr .r27).toNat + 2 ^ 64 * (s.gpr .r28).toNat + 2 ^ 128 * (s.gpr .r29).toNat + 2 ^ 192 * (s.gpr .r30).toNat :=
  psum4 _

/-- `mulB`: the window's low four words += `aᵢ b`, into five words. -/
theorem mulB_ok {s : State} (h0 : s.gpr .r0 = 0) :
    WP isa (.block mulB) s fun t =>
      (rv t accR 5 = rv s accR 4 + rv s bR 4 * (s.gpr .r24).toNat ∧ t.mem = s.mem) ∧
        Keep [.r22, .r27, .r28, .r29, .r30, .r31] s t := by
  show WP isa (.block (prodChain false .r24 bR accR accR ++ (.addze (accR 4) .r0 ::
    (prodChain true .r24 bR (fun j => accR (j + 1)) (fun j => accR (j + 1)) ++ [])))) s _
  refine prodChain_ok (by decide) fun t₁ k₁ m₁ e₁ _ => ?_
  refine wp_addze fun t₂ w₂ e₂ => ?_
  refine prodChain_ok (by decide) fun t₃ k₃ m₃ e₃ _ => ?_
  simp only [aR0, aR1, aR2, aR3, aR4] at k₁ w₂ e₂ k₃
  refine WP.block_nil ⟨⟨?_, by rw [m₃, w₂.mem, m₁]⟩, (k₁.trans (w₂.keep.trans k₃)).mono (by decide)⟩
  have g : ∀ r ∈ [Reg.r0, .r14, .r15, .r16, .r17, .r24], t₂.gpr r = s.gpr r := fun r hr => by
    rw [w₂.gpr r (by revert r hr; decide), k₁.gpr r (by revert r hr; decide)]
  have lh := lohi_sum s bR (s.gpr .r24)
  have e₃' : rv t₃ (fun j => accR (j + 1)) 4 + 2 ^ 256 * t₃.ca.toNat =
      rv t₂ (fun j => accR (j + 1)) 4 + psum (fun j => pv true (s.gpr (bR j)) (s.gpr .r24)) 4 := by
    rw [e₃]; congr 1
    simp only [psum4, bR0, bR1, bR2, bR3, g .r14 (by decide), g .r15 (by decide), g .r16 (by decide),
      g .r17 (by decide), g .r24 (by decide)]
  have a0 : t₃.gpr .r27 = t₁.gpr .r27 := by rw [k₃.gpr _ (by decide), w₂.gpr _ (by decide)]
  have t2 : rv t₂ (fun j => accR (j + 1)) 4 = (t₁.gpr .r28).toNat + 2 ^ 64 * (t₁.gpr .r29).toNat +
      2 ^ 128 * (t₁.gpr .r30).toNat + 2 ^ 192 * (t₂.gpr .r31).toNat := by
    rw [accR_succ4, w₂.gpr _ (by decide), w₂.gpr _ (by decide), w₂.gpr _ (by decide)]
  rw [k₁.gpr .r0 (by decide), h0, show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add] at e₂
  rw [accR4] at e₁
  have hc₁ := Bool.toNat_le t₁.ca
  have hc₂ := Bool.toNat_le t₂.ca
  have hB := rv_lt s bR 4
  have hA := rv_lt s accR 4
  have hx := (s.gpr .r24).isLt
  have hP : rv s bR 4 * (s.gpr .r24).toNat ≤ (2 ^ 256 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  rw [accR_succ, a0]
  rw [t2] at e₃'
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub] at *
  omega

/-- `loM`: the window += the low words of `uᵢ m`, `r26` added at word 4 and
its carry out into `r26`. -/
theorem loM_ok {s : State} (h0 : s.gpr .r0 = 0) :
    WP isa (.block loM) s fun t =>
      (rv t accR 4 + 2 ^ 256 * ((t.gpr .r31).toNat + 2 ^ 64 * (t.gpr .r26).toNat) =
          rv s accR 5 + 2 ^ 256 * (s.gpr .r26).toNat +
          psum (fun j => pv false (s.gpr (mR j)) (s.gpr .r25)) 4 ∧ (t.gpr .r26).toNat ≤ 1 ∧
        (t.gpr .r27).toNat = ((s.gpr .r27).toNat + pv false (s.gpr .r18) (s.gpr .r25)) % 2 ^ 64 ∧ t.mem = s.mem) ∧
        Keep [.r22, .r27, .r28, .r29, .r30, .r31, .r26] s t := by
  show WP isa (.block (prodChain false .r25 mR accR accR ++ [.adde (accR 4) (accR 4) .r26, .addze .r26 .r0])) s _
  refine prodChain_ok (by decide) fun t₁ k₁ m₁ e₁ l₁ => ?_
  refine wp_adde fun t₂ w₂ e₂ => ?_
  refine wp_addze fun t₃ w₃ e₃ => ?_
  simp only [aR0, aR1, aR2, aR3, aR4, mR0] at k₁ l₁ w₂ e₂
  refine WP.block_nil ⟨⟨?_, ?_, ?_, by rw [w₃.mem, w₂.mem, m₁]⟩, (k₁.trans (w₂.keep.trans w₃.keep)).mono (by decide)⟩
  · rw [w₂.gpr _ (by decide), k₁.gpr .r0 (by decide), h0, show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add] at e₃
    rw [k₁.gpr .r31 (by decide), k₁.gpr .r26 (by decide)] at e₂
    have r4 : (t₃.gpr .r31) = t₂.gpr .r31 := w₃.gpr _ (by decide)
    have lo : rv t₃ accR 4 = rv t₁ accR 4 := by
      simp only [accR4]
      rw [w₃.gpr _ (by decide), w₃.gpr _ (by decide), w₃.gpr _ (by decide), w₃.gpr _ (by decide),
        w₂.gpr _ (by decide), w₂.gpr _ (by decide), w₂.gpr _ (by decide), w₂.gpr _ (by decide)]
    rw [rv5, lo, r4, aR4]
    have hc := Bool.toNat_le t₃.ca
    have hc' := Bool.toNat_le t₂.ca
    simp only [Nat.reducePow] at *
    omega
  · have hc := Bool.toNat_le t₃.ca
    rw [w₂.gpr _ (by decide), k₁.gpr .r0 (by decide), h0, show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add] at e₃
    have hc' := Bool.toNat_le t₂.ca
    omega
  · rw [w₃.gpr _ (by decide), w₂.gpr _ (by decide)]
    exact l₁

/-- `shiftM`: the window moved down a word, the high words of `uᵢ m` added,
the carry out in CA. -/
theorem shiftM_ok (s : State) :
    WP isa (.block shiftM) s fun t =>
      (rv t accR 4 + 2 ^ 256 * t.ca.toNat = rv s (fun j => accR (j + 1)) 4 +
          psum (fun j => pv true (s.gpr (mR j)) (s.gpr .r25)) 4 ∧ t.mem = s.mem) ∧
        Keep [.r22, .r27, .r28, .r29, .r30] s t := by
  show WP isa (.block (prodChain true .r25 mR accR (fun j => accR (j + 1)) ++ [])) s _
  exact prodChain_ok (by decide) fun t k m e _ => WP.block_nil ⟨⟨e, m⟩, k.mono (by decide)⟩

/-! ## A row -/

/-- The window's value: its four words, and `r26` and CA at word 4. -/
def Vv (s : State) : Nat := rv s accR 4 + 2 ^ 256 * ((s.gpr .r26).toNat + s.ca.toNat)

/-- The registers a row writes. -/
def rowRegs : List Reg := [.r26, .r24, .r25, .r22, .r27, .r28, .r29, .r30, .r31]

theorem mR_keep {s t : State} {rs : List Reg} (k : Keep rs s t) (h : ∀ j < 4, mR j ∉ rs := by decide) :
    ∀ j < 4, t.gpr (mR j) = s.gpr (mR j) := fun j hj => k.gpr _ (h j hj)

theorem bR_keep {s t : State} {rs : List Reg} (k : Keep rs s t) (h : ∀ j < 4, bR j ∉ rs := by decide) :
    ∀ j < 4, t.gpr (bR j) = s.gpr (bR j) := fun j hj => k.gpr _ (h j hj)

theorem accR_keep {s t : State} {rs : List Reg} (k : Keep rs s t) (h : ∀ j < 5, accR j ∉ rs := by decide) :
    ∀ j < 5, t.gpr (accR j) = s.gpr (accR j) := fun j hj => k.gpr _ (h j hj)

/-- What the three chains of a row add up to: the word that drops out, `o`,
and the window after, `2⁶⁴ Vv' + o = Vv + b a + m u`. -/
theorem row_arith {RA CY CA CY₁ c₁ R₃ R₆ A4₆ CY₆ R₆' R₇ ca₇ A₀ PB PM L H : Nat}
    (e₁ : CY₁ + 2 ^ 64 * c₁ = CY + CA) (hCY : CY ≤ 2) (hCA : CA ≤ 1) (hCY₁ : CY₁ < 2 ^ 64)
    (e₃ : R₃ = RA + PB) (e₆ : R₆ + 2 ^ 256 * (A4₆ + 2 ^ 64 * CY₆) = R₃ + 2 ^ 256 * CY₁ + L)
    (e₇ : R₇ + 2 ^ 256 * ca₇ = R₆' + H) (hs : R₆ + 2 ^ 256 * A4₆ = A₀ + 2 ^ 64 * R₆')
    (lh : L + 2 ^ 64 * H = PM) :
    2 ^ 64 * (R₇ + 2 ^ 256 * (CY₆ + ca₇)) + A₀ = RA + 2 ^ 256 * (CY + CA) + PB + PM := by
  omega

/-- `uᵢ`'s choice zeroes the window's low word. -/
theorem row0_zero (a m mp : BitVec 64) (hm : (m.toNat * mp.toNat + 1) % 2 ^ 64 = 0) :
    (a.toNat + pv false m (a * mp)) % 2 ^ 64 = 0 := by
  simp only [pv, Bool.false_eq_true, ite_false, BitVec.toNat_mul]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.mul_comm m.toNat]
  exact mont_low a.toNat mp.toNat m.toNat hm

/-- Row `r` of the first chunk (`row0 r`): `uᵢ` stored at word `r` of the
chunk (`r9`), and the word that drops out 0. -/
theorem row0_ok {s : State} {B : Addr} {Z da dT r : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h6 : s.gpr .r6 = off B da) (h9 : s.gpr .r9 = off B dT) (hr : r < 4) (ha : da + 32 ≤ Z) (hT : dT + 32 ≤ Z)
    (h26 : (s.gpr .r26).toNat ≤ 2) (hm : ((s.gpr .r18).toNat * (s.gpr .r23).toNat + 1) % 2 ^ 64 = 0) :
    WP isa (.block (row0 r)) s fun t =>
      (2 ^ 64 * Vv t = Vv s + rv s bR 4 * (word s.mem B (da + 8 * r)).toNat + rv s mR 4 * (t.gpr .r25).toNat ∧
        (t.gpr .r26).toNat ≤ 1 ∧ t.mem = s.mem.writeW (off B (dT + 8 * r)) (t.gpr .r25)) ∧ Keep rowRegs s t := by
  simp only [row0, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_addze fun t₁ w₁ e₁ => ?_
  refine wp_ld (d := .r24) (n := .r6) (off := 8 * r) (by decide) ⟨by omega, by omega⟩
    (by rw [w₁.gpr _ (by decide), h6, off_add]) ((hs.congr w₁.wr).ld (by omega)) fun t₂ w₂ e₂ _ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulB_ok (s := t₂) (by rw [w₂.gpr _ (by decide), w₁.gpr _ (by decide), h0]))
    fun t₃ ⟨⟨e₃, m₃⟩, k₃⟩ => ?_
  refine wp_mul fun t₄ w₄ e₄ _ => ?_
  refine wp_st (t := .r25) (n := .r9) (off := 8 * r) (by decide) ⟨by omega, by omega⟩
    (by rw [w₄.gpr _ (by decide), k₃.gpr _ (by decide), w₂.gpr _ (by decide), w₁.gpr _ (by decide), h9, off_add])
    ((hs.congr (w₄.wr.trans (k₃.wr.trans (w₂.wr.trans w₁.wr)))).st (by omega)) fun t₅ k₅ m₅ _ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loM_ok (s := t₅) (by
      rw [k₅.gpr _ (by decide), w₄.gpr _ (by decide), k₃.gpr _ (by decide), w₂.gpr _ (by decide),
        w₁.gpr _ (by decide), h0])) fun t₆ ⟨⟨e₆, b₆, l₆, m₆⟩, k₆⟩ => ?_
  refine WP.mono (shiftM_ok t₆) fun t₇ ⟨⟨e₇, m₇⟩, k₇⟩ => ?_
  -- Registers through the row.
  have K₂ : Keep [.r26, .r24] s t₂ := (w₁.keep.trans w₂.keep).mono (by decide)
  have K₅ : Keep [.r26, .r24, .r22, .r27, .r28, .r29, .r30, .r31, .r25] s t₅ :=
    (((K₂.trans k₃).trans w₄.keep).trans k₅).mono (by decide)
  have u₇ : t₇.gpr .r25 = t₄.gpr .r25 := by
    rw [k₇.gpr _ (by decide), k₆.gpr _ (by decide), k₅.gpr _ (by decide)]
  have mR₅ := mR_keep K₅
  have c₇ : t₇.gpr .r26 = t₆.gpr .r26 := k₇.gpr _ (by decide)
  refine ⟨⟨?_, by rw [c₇]; exact b₆, by rw [m₇, m₆, m₅, w₄.mem, m₃, w₂.mem, w₁.mem, u₇]⟩,
    ((K₅.trans k₆).trans k₇).mono (by decide)⟩
  -- The arithmetic.
  have hA₂ : rv t₂ accR 4 = rv s accR 4 := rv_congr 4 fun j hj => accR_keep K₂ (by decide) j (by omega)
  have hB₂ : rv t₂ bR 4 = rv s bR 4 := rv_congr 4 (bR_keep K₂)
  have ha₂ : (t₂.gpr .r24).toNat = (word s.mem B (da + 8 * r)).toNat := by rw [e₂, w₁.mem]
  rw [hA₂, hB₂, ha₂] at e₃
  have hA₅ : rv t₅ accR 5 = rv t₃ accR 5 :=
    rv_congr 5 (accR_keep ((w₄.keep.trans k₅).mono (by decide) : Keep [.r25] t₃ t₅))
  have c₅ : t₅.gpr .r26 = t₁.gpr .r26 := by
    rw [k₅.gpr _ (by decide), w₄.gpr _ (by decide), k₃.gpr _ (by decide), w₂.gpr _ (by decide)]
  have u₅ : t₅.gpr .r25 = t₄.gpr .r25 := k₅.gpr _ (by decide)
  rw [hA₅, c₅, pv_sum_congr false mR₅ u₅] at e₆
  have mR₆ := mR_keep (K₅.trans k₆)
  have u₆ : t₆.gpr .r25 = t₄.gpr .r25 := by rw [k₆.gpr _ (by decide), u₅]
  rw [pv_sum_congr true mR₆ u₆] at e₇
  have hs₆ : rv t₆ accR 4 + 2 ^ 256 * (t₆.gpr .r31).toNat = (t₆.gpr .r27).toNat + 2 ^ 64 * rv t₆ (fun j => accR (j + 1)) 4 :=
    accR_succ t₆
  have m0 : t₅.gpr .r18 = s.gpr .r18 := mR₅ 0 (by decide)
  have z : (t₆.gpr .r27).toNat = 0 := by
    rw [l₆, k₅.gpr _ (by decide), w₄.gpr _ (by decide), m0, u₅, e₄,
      show t₃.gpr .r23 = s.gpr .r23 from ((K₂.trans k₃).gpr _ (by decide))]
    exact row0_zero _ _ _ hm
  rw [z] at hs₆
  have H := row_arith e₁ h26 (Bool.toNat_le _) (t₁.gpr .r26).isLt e₃ e₆ e₇ hs₆ (lohi_sum s mR (t₄.gpr .r25))
  unfold Vv
  rw [u₇, c₇]
  omega

/-- Row `r` of a later chunk (`rowT r`): `uᵢ` moved from word `r` of the chunk
below (`r9`) to word `r` of this chunk, and the word that drops out stored
at word `r` of the chunk below. -/
theorem rowT_ok {s : State} {B : Addr} {Z da dT r : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h6 : s.gpr .r6 = off B da) (h9 : s.gpr .r9 = off B dT) (hr : r < 4) (ha : da + 32 ≤ Z) (hT : dT + 64 ≤ Z)
    (h26 : (s.gpr .r26).toNat ≤ 2) :
    WP isa (.block (rowT r)) s fun t =>
      ((∃ o : BitVec 64, t.mem = (s.mem.writeW (off B (dT + 8 * r + 32)) (word s.mem B (dT + 8 * r))).writeW
          (off B (dT + 8 * r)) o ∧
        2 ^ 64 * Vv t + o.toNat = Vv s + rv s bR 4 * (word s.mem B (da + 8 * r)).toNat +
          rv s mR 4 * (word s.mem B (dT + 8 * r)).toNat) ∧
        (t.gpr .r26).toNat ≤ 1) ∧ Keep rowRegs s t := by
  simp only [rowT, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_addze fun t₁ w₁ e₁ => ?_
  have h9₁ : t₁.gpr .r9 = off B dT := by rw [w₁.gpr _ (by decide), h9]
  refine wp_ld (d := .r24) (n := .r6) (off := 8 * r) (by decide) ⟨by omega, by omega⟩
    (by rw [w₁.gpr _ (by decide), h6, off_add]) ((hs.congr w₁.wr).ld (by omega)) fun t₂ w₂ e₂ _ => ?_
  refine wp_ld (d := .r25) (n := .r9) (off := 8 * r) (by decide) ⟨by omega, by omega⟩
    (by rw [w₂.gpr _ (by decide), h9₁, off_add]) ((hs.congr (w₂.wr.trans w₁.wr)).ld (by omega))
    fun t₂' w₂' e₂' _ => ?_
  refine wp_st (t := .r25) (n := .r9) (off := 8 * r + 32) (a := off B (dT + 8 * r + 32)) (by decide) ⟨by omega, by omega⟩
    (by rw [w₂'.gpr _ (by decide), w₂.gpr _ (by decide), h9₁, off_add, Nat.add_assoc])
    ((hs.congr (w₂'.wr.trans (w₂.wr.trans w₁.wr))).st (by omega)) fun t₂'' k₂'' m₂'' _ => ?_
  rw [WP.block_append_iff]
  have h0₂ : t₂''.gpr .r0 = 0 := by
    rw [k₂''.gpr _ (by decide), w₂'.gpr _ (by decide), w₂.gpr _ (by decide), w₁.gpr _ (by decide), h0]
  refine WP.mono (mulB_ok (s := t₂'') h0₂) fun t₃ ⟨⟨e₃, m₃⟩, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loM_ok (s := t₃) (by rw [k₃.gpr _ (by decide), h0₂])) fun t₆ ⟨⟨e₆, b₆, _, m₆⟩, k₆⟩ => ?_
  have K₂ : Keep [.r26, .r24, .r25] s t₂'' := (((w₁.keep.trans w₂.keep).trans w₂'.keep).trans k₂'').mono (by decide)
  have K₆ : Keep [.r26, .r24, .r25, .r22, .r27, .r28, .r29, .r30, .r31] s t₆ :=
    ((K₂.trans k₃).trans k₆).mono (by decide)
  refine wp_st (t := .r27) (n := .r9) (off := 8 * r) (by decide) ⟨by omega, by omega⟩
    (by rw [K₆.gpr _ (by decide), h9, off_add]) ((hs.congr K₆.wr).st (by omega)) fun t₅ k₅ m₅ _ => ?_
  refine WP.mono (shiftM_ok t₅) fun t₇ ⟨⟨e₇, m₇⟩, k₇⟩ => ?_
  have c₇ : t₇.gpr .r26 = t₆.gpr .r26 := by rw [k₇.gpr _ (by decide), k₅.gpr _ (by decide)]
  have u₂ : t₂'.gpr .r25 = word s.mem B (dT + 8 * r) := by rw [e₂', w₂.mem, w₁.mem]
  refine ⟨⟨⟨t₆.gpr .r27, ?_, ?_⟩, by rw [c₇]; exact b₆⟩, (((K₆.trans k₅).trans k₇)).mono (by decide)⟩
  · rw [m₇, m₅, m₆, m₃, m₂'', w₂'.mem, w₂.mem, w₁.mem, u₂]
  -- The arithmetic.
  have hA₂ : rv t₂'' accR 4 = rv s accR 4 := rv_congr 4 fun j hj => accR_keep K₂ (by decide) j (by omega)
  have hB₂ : rv t₂'' bR 4 = rv s bR 4 := rv_congr 4 (bR_keep K₂)
  have ha₂ : (t₂''.gpr .r24).toNat = (word s.mem B (da + 8 * r)).toNat := by
    rw [k₂''.gpr _ (by decide), w₂'.gpr _ (by decide), e₂, w₁.mem]
  rw [hA₂, hB₂, ha₂] at e₃
  have c₃ : t₃.gpr .r26 = t₁.gpr .r26 := by
    rw [k₃.gpr _ (by decide), k₂''.gpr _ (by decide), w₂'.gpr _ (by decide), w₂.gpr _ (by decide)]
  have u₃ : t₃.gpr .r25 = word s.mem B (dT + 8 * r) := by rw [k₃.gpr _ (by decide), k₂''.gpr _ (by decide), u₂]
  rw [c₃, pv_sum_congr false (mR_keep (K₂.trans k₃)) u₃] at e₆
  have u₅ : t₅.gpr .r25 = word s.mem B (dT + 8 * r) := by rw [k₅.gpr _ (by decide), k₆.gpr _ (by decide), u₃]
  rw [pv_sum_congr true (mR_keep ((K₆.trans k₅).mono (by decide) : Keep rowRegs s t₅)) u₅] at e₇
  have hs₆ : rv t₆ accR 4 + 2 ^ 256 * (t₆.gpr .r31).toNat = (t₆.gpr .r27).toNat + 2 ^ 64 * rv t₆ (fun j => accR (j + 1)) 4 :=
    accR_succ t₆
  have hA₅ : rv t₅ (fun j => accR (j + 1)) 4 = rv t₆ (fun j => accR (j + 1)) 4 := rv_congr 4 fun j _ => k₅.gpr _ List.not_mem_nil
  rw [hA₅] at e₇
  have H := row_arith e₁ h26 (Bool.toNat_le _) (t₁.gpr .r26).isLt e₃ e₆ e₇ hs₆ (lohi_sum s mR (word s.mem B (dT + 8 * r)))
  unfold Vv
  rw [c₇]
  omega

/-! ## A chunk's rows -/

theorem flatMap_range_succ (f : Nat → List Instr) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem pow_row (n : Nat) : 2 ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by
  rw [Nat.mul_succ, Nat.pow_add]

/-- The first `n` rows of the first chunk (`rows0`), `T`'s chunk at `dT`: the
`uᵢ` stored at its words, which the window's low words had been loaded
from, and `2^(64 n) Vv' = Vv + b A + m U` for the rows' words `A` of `a` and
`U` of `uᵢ`. -/
theorem rows0_ok {B : Addr} {Z da dT : Nat} :
    ∀ (n : Nat) {s : State}, Scr s B Z → s.gpr .r0 = 0 → s.gpr .r6 = off B da → s.gpr .r9 = off B dT → n ≤ 4 →
    da + 32 ≤ Z → dT + 32 ≤ Z → (da + 32 ≤ dT ∨ dT + 32 ≤ da) → (s.gpr .r26).toNat ≤ 2 →
    ((s.gpr .r18).toNat * (s.gpr .r23).toNat + 1) % 2 ^ 64 = 0 →
    WP isa (.block ((List.range n).flatMap row0)) s fun t =>
      (2 ^ (64 * n) * Vv t = Vv s + rv s bR 4 * wordsVal s.mem B da n + rv s mR 4 * wordsVal t.mem B dT n ∧
        (t.gpr .r26).toNat ≤ 2 ∧ (0 < n → (t.gpr .r26).toNat ≤ 1) ∧ Outside B dT (8 * n) s.mem t.mem) ∧
        Keep rowRegs s t
  | 0, s, _, _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨⟨by simp [wordsVal], by assumption, fun h => absurd h (by decide),
      Outside.refl _ _ _ _⟩, Keep.refl _ _⟩
  | n + 1, s, hs, h0, h6, h9, hn, ha, hT, hda, h26, hm => by
    have hnw := hs.nowrap
    rw [flatMap_range_succ, WP.block_append_iff]
    refine WP.mono (rows0_ok n hs h0 h6 h9 (by omega) ha hT hda h26 hm) fun t ⟨⟨e, c, _, o⟩, k⟩ => ?_
    have g : ∀ r ∈ [Reg.r0, .r6, .r9, .r18, .r23], t.gpr r = s.gpr r := fun r hr => k.gpr r (by revert r hr; decide)
    refine WP.mono (row0_ok (r := n) (hs.congr k.wr) (by rw [g _ (by decide), h0]) (by rw [g _ (by decide), h6])
      (by rw [g _ (by decide), h9]) (by omega) ha hT (by omega) (by rw [g _ (by decide), g _ (by decide)]; exact hm))
      fun t' ⟨⟨e', c', m'⟩, k'⟩ => ⟨⟨?_, by omega, fun _ => c', ?_⟩, (k.trans k').mono (by decide)⟩
    · have wa : word t.mem B (da + 8 * n) = word s.mem B (da + 8 * n) := o.word (by omega) (by omega)
      have hB : rv t bR 4 = rv s bR 4 := rv_congr 4 (bR_keep k)
      have hM : rv t mR 4 = rv s mR 4 := rv_congr 4 (mR_keep k)
      have wu : wordsVal t'.mem B dT (n + 1) = wordsVal t.mem B dT n + 2 ^ (64 * n) * (t'.gpr .r25).toNat := by
        rw [m', wordsVal_succ_top, (writeW_outside _ B _ (by omega)).wordsVal (by omega) (by omega), word_writeW_self]
      rw [wa, hB, hM] at e'
      rw [wordsVal_succ_top s.mem B da n, wu, pow_row, Nat.mul_assoc, e']
      rw [Nat.mul_add, Nat.mul_add, e]
      grind
    · rw [m']
      exact (o.mono (Nat.le_refl _) (by omega)).trans ((writeW_outside _ B _ (by omega)).mono (by omega) (by omega))

/-- The first `n` rows of a later chunk (`rowsT`), the chunk below at `dT`
(`r9`): its words, the `uᵢ`, moved a chunk up, the words that drop out stored
in their place, and `2^(64 n) Vv' + O = Vv + b A + m U` for the words `O`
stored, the rows' words `A` of `a` and `U` of `uᵢ`. -/
theorem rowsT_ok {B : Addr} {Z da dT : Nat} :
    ∀ (n : Nat) {s : State}, Scr s B Z → s.gpr .r0 = 0 → s.gpr .r6 = off B da → s.gpr .r9 = off B dT → n ≤ 4 →
    da + 32 ≤ Z → dT + 64 ≤ Z → (da + 32 ≤ dT ∨ dT + 64 ≤ da) → (s.gpr .r26).toNat ≤ 2 →
    WP isa (.block ((List.range n).flatMap rowT)) s fun t =>
      (2 ^ (64 * n) * Vv t + wordsVal t.mem B dT n =
          Vv s + rv s bR 4 * wordsVal s.mem B da n + rv s mR 4 * wordsVal s.mem B dT n ∧
        wordsVal t.mem B (dT + 32) n = wordsVal s.mem B dT n ∧
        (∀ j, n ≤ j → j < 4 → word t.mem B (dT + 8 * j) = word s.mem B (dT + 8 * j)) ∧
        (t.gpr .r26).toNat ≤ 2 ∧ (0 < n → (t.gpr .r26).toNat ≤ 1) ∧ Outside B dT 64 s.mem t.mem) ∧
        Keep rowRegs s t
  | 0, s, _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨⟨by simp [wordsVal], by simp [wordsVal], fun _ _ _ => rfl,
      by assumption, fun h => absurd h (by decide), Outside.refl _ _ _ _⟩, Keep.refl _ _⟩
  | n + 1, s, hs, h0, h6, h9, hn, ha, hT, hda, h26 => by
    have hnw := hs.nowrap
    rw [flatMap_range_succ, WP.block_append_iff]
    refine WP.mono (rowsT_ok n hs h0 h6 h9 (by omega) ha hT hda h26) fun t ⟨⟨e, eu, f, c, _, o⟩, k⟩ => ?_
    have g : ∀ r ∈ [Reg.r0, .r6, .r9], t.gpr r = s.gpr r := fun r hr => k.gpr r (by revert r hr; decide)
    refine WP.mono (rowT_ok (r := n) (hs.congr k.wr) (by rw [g _ (by decide), h0]) (by rw [g _ (by decide), h6])
      (by rw [g _ (by decide), h9]) (by omega) ha hT (by omega))
      fun t' ⟨⟨⟨w, m', e'⟩, c'⟩, k'⟩ => ⟨⟨?_, ?_, fun j hj hj4 => ?_, by omega, fun _ => c', ?_⟩,
        (k.trans k').mono (by decide)⟩
    · have wa : word t.mem B (da + 8 * n) = word s.mem B (da + 8 * n) := o.word (by omega) (by omega)
      have hB : rv t bR 4 = rv s bR 4 := rv_congr 4 (bR_keep k)
      have hM : rv t mR 4 = rv s mR 4 := rv_congr 4 (mR_keep k)
      have wu : word t.mem B (dT + 8 * n) = word s.mem B (dT + 8 * n) := f n (Nat.le_refl _) (by omega)
      have wo : wordsVal t'.mem B dT (n + 1) = wordsVal t.mem B dT n + 2 ^ (64 * n) * w.toNat := by
        rw [m', wordsVal_succ_top, (writeW_outside _ B _ (by omega)).wordsVal (by omega) (by omega),
          (writeW_outside _ B _ (by omega)).wordsVal (by omega) (by omega), word_writeW_self]
      rw [wa, hB, hM, wu] at e'
      rw [wordsVal_succ_top s.mem B da n, wordsVal_succ_top s.mem B dT n, wo, pow_row, Nat.mul_assoc]
      have : 2 ^ (64 * n) * (2 ^ 64 * Vv t') + (wordsVal t.mem B dT n + 2 ^ (64 * n) * w.toNat) =
          2 ^ (64 * n) * Vv t + wordsVal t.mem B dT n + 2 ^ (64 * n) * (rv s bR 4 * (word s.mem B (da + 8 * n)).toNat +
            rv s mR 4 * (word s.mem B (dT + 8 * n)).toNat) := by
        rw [← Nat.add_assoc, Nat.add_right_comm, ← Nat.mul_add, e']; grind
      rw [this, e]
      grind
    · have wu : word t.mem B (dT + 8 * n) = word s.mem B (dT + 8 * n) := f n (Nat.le_refl _) (by omega)
      rw [m', wordsVal_succ_top, (writeW_outside _ B _ (by omega)).wordsVal (by omega) (by omega),
        (writeW_outside _ B _ (by omega)).wordsVal (by omega) (by omega), eu, wordsVal_succ_top s.mem B dT n,
        (writeW_outside _ B _ (by omega)).word (by omega) (by omega),
        show dT + 32 + 8 * n = dT + 8 * n + 32 by omega, word_writeW_self, wu]
    · rw [m', (writeW_outside _ B _ (by omega)).word (by omega) (by omega),
        (writeW_outside _ B _ (by omega)).word (by omega) (by omega)]
      exact f j (by omega) hj4
    · rw [m']
      exact (o.trans ((writeW_outside _ B _ (by omega)).mono (by omega) (by omega))).trans
        ((writeW_outside _ B _ (by omega)).mono (by omega) (by omega))

/-! ## Loads and the chunk's words of `T` -/

theorem wordsVal4 (m : Mem) (B : Addr) (d : Nat) : wordsVal m B d 4 = (word m B d).toNat +
    2 ^ 64 * (word m B (d + 8)).toNat + 2 ^ 128 * (word m B (d + 16)).toNat + 2 ^ 192 * (word m B (d + 24)).toNat := by
  simp only [wordsVal, Nat.add_assoc, show d + 8 + 8 = d + 16 by omega, show d + 16 + 8 = d + 24 by omega]
  omega

/-- Four words loaded from `p` into `f 0`, …, `f 3`. -/
theorem load4_ok {f : Nat → Reg} {p : Reg} {s : State} {B : Addr} {Z d : Nat} (hs : Scr s B Z)
    (hp : s.gpr p = off B d) (hd : d + 32 ≤ Z)
    (hr : p ≠ .r0 ∧ ∀ j < 4, f j ≠ p ∧ ∀ k < 4, j < k → f j ≠ f k) :
    WP isa (.block ((List.range 4).map fun j => .load .d (f j) p (8 * j))) s fun t =>
      (rv t f 4 = wordsVal s.mem B d 4 ∧ t.gpr (f 0) = word s.mem B d ∧ t.mem = s.mem ∧ t.ca = s.ca) ∧
        Keep [f 0, f 1, f 2, f 3] s t := by
  obtain ⟨hp0, hf⟩ := hr
  have f0 := hf 0 (by decide); have f1 := hf 1 (by decide); have f2 := hf 2 (by decide); have f3 := hf 3 (by decide)
  show WP isa (.block [.load .d (f 0) p 0, .load .d (f 1) p 8, .load .d (f 2) p 16, .load .d (f 3) p 24]) s _
  refine wp_ld hp0 ⟨by decide, by decide⟩ (by rw [hp, off_add]) (hs.ld (by omega)) fun t₁ w₁ e₁ c₁ => ?_
  refine wp_ld hp0 ⟨by decide, by decide⟩ (by rw [w₁.gpr _ f0.1.symm, hp, off_add])
    ((hs.congr w₁.wr).ld (by omega)) fun t₂ w₂ e₂ c₂ => ?_
  refine wp_ld hp0 ⟨by decide, by decide⟩ (by rw [w₂.gpr _ f1.1.symm, w₁.gpr _ f0.1.symm, hp, off_add])
    ((hs.congr (w₂.wr.trans w₁.wr)).ld (by omega)) fun t₃ w₃ e₃ c₃ => ?_
  refine wp_ld hp0 ⟨by decide, by decide⟩
    (by rw [w₃.gpr _ f2.1.symm, w₂.gpr _ f1.1.symm, w₁.gpr _ f0.1.symm, hp, off_add])
    ((hs.congr (w₃.wr.trans (w₂.wr.trans w₁.wr))).ld (by omega)) fun t₄ w₄ e₄ c₄ =>
      WP.block_nil ⟨⟨?_, ?_, ?_, by rw [c₄, c₃, c₂, c₁]⟩, ?_⟩
  · rw [w₃.mem, w₂.mem, w₁.mem] at e₄
    rw [w₂.mem, w₁.mem] at e₃
    rw [w₁.mem] at e₂
    simp only [rv, psum4, wordsVal4]
    rw [w₄.gpr _ (f0.2 3 (by decide) (by decide)), w₃.gpr _ (f0.2 2 (by decide) (by decide)),
      w₂.gpr _ (f0.2 1 (by decide) (by decide)), e₁, w₄.gpr _ (f1.2 3 (by decide) (by decide)),
      w₃.gpr _ (f1.2 2 (by decide) (by decide)), e₂, w₄.gpr _ (f2.2 3 (by decide) (by decide)), e₃, e₄]
    rfl
  · rw [w₄.gpr _ (f0.2 3 (by decide) (by decide)), w₃.gpr _ (f0.2 2 (by decide) (by decide)),
      w₂.gpr _ (f0.2 1 (by decide) (by decide)), e₁, Nat.add_zero]
  · rw [w₄.mem, w₃.mem, w₂.mem, w₁.mem]
  · exact (((w₁.keep.trans w₂.keep).trans w₃.keep).trans w₄.keep).mono fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr

/-- The chunk's four words of `T` (a chunk above `r9`) added to the window. -/
theorem addT_ok {s : State} {B : Addr} {Z dT : Nat} (hs : Scr s B Z) (h9 : s.gpr .r9 = off B dT)
    (hT : dT + 64 ≤ Z) (h26 : (s.gpr .r26).toNat ≤ 1) :
    WP isa (.block addT) s fun t =>
      (Vv t = Vv s + wordsVal s.mem B (dT + 32) 4 ∧ (t.gpr .r26).toNat ≤ 2 ∧ t.mem = s.mem) ∧
        Keep [.r26, .r22, .r27, .r28, .r29, .r30] s t := by
  show WP isa (.block [.addze .r26 .r26, .load .d .r22 .r9 32, .addc .r27 .r27 .r22, .load .d .r22 .r9 40,
    .adde .r28 .r28 .r22, .load .d .r22 .r9 48, .adde .r29 .r29 .r22, .load .d .r22 .r9 56,
    .adde .r30 .r30 .r22]) s _
  have hs' : ∀ {t : State}, t.wr = s.wr → ∀ {i}, i < 4 → InRegions (t.rd ++ t.wr) (off B (dT + (32 + 8 * i))) 8 :=
    fun h i hi => (hs.congr h).ld (by omega)
  refine wp_addze fun t₁ w₁ e₁ => ?_
  have p₁ : t₁.gpr .r9 = off B dT := by rw [w₁.gpr _ (by decide), h9]
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [p₁, off_add]) (hs' (i := 0) w₁.wr (by decide))
    fun t₂ w₂ e₂ c₂ => ?_
  refine wp_addc fun t₃ w₃ e₃ => ?_
  have p₃ : t₃.gpr .r9 = off B dT := by rw [w₃.gpr _ (by decide), w₂.gpr _ (by decide), p₁]
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [p₃, off_add]) (hs' (i := 1) (w₃.wr.trans (w₂.wr.trans w₁.wr))
    (by decide)) fun t₄ w₄ e₄ c₄ => ?_
  refine wp_adde fun t₅ w₅ e₅ => ?_
  have p₅ : t₅.gpr .r9 = off B dT := by rw [w₅.gpr _ (by decide), w₄.gpr _ (by decide), p₃]
  have wr₅ : t₅.wr = s.wr := w₅.wr.trans (w₄.wr.trans (w₃.wr.trans (w₂.wr.trans w₁.wr)))
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [p₅, off_add]) (hs' (i := 2) wr₅ (by decide))
    fun t₆ w₆ e₆ c₆ => ?_
  refine wp_adde fun t₇ w₇ e₇ => ?_
  have p₇ : t₇.gpr .r9 = off B dT := by rw [w₇.gpr _ (by decide), w₆.gpr _ (by decide), p₅]
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [p₇, off_add]) (hs' (i := 3) (w₇.wr.trans (w₆.wr.trans wr₅))
    (by decide)) fun t₈ w₈ e₈ c₈ => ?_
  refine wp_adde fun t₉ w₉ e₉ => WP.block_nil ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · have m₇ : t₇.mem = s.mem := by rw [w₇.mem, w₆.mem, w₅.mem, w₄.mem, w₃.mem, w₂.mem, w₁.mem]
    have e₂' : t₂.gpr .r22 = word s.mem B (dT + 32) := by rw [e₂, w₁.mem]
    have e₄' : t₄.gpr .r22 = word s.mem B (dT + 40) := by rw [e₄, w₃.mem, w₂.mem, w₁.mem]
    have e₆' : t₆.gpr .r22 = word s.mem B (dT + 48) := by rw [e₆, w₅.mem, w₄.mem, w₃.mem, w₂.mem, w₁.mem]
    have e₈' : t₈.gpr .r22 = word s.mem B (dT + 56) := by rw [e₈, m₇]
    rw [e₂', w₂.gpr _ (by decide), w₁.gpr _ (by decide)] at e₃
    rw [e₄', w₄.gpr _ (by decide), w₃.gpr _ (by decide), w₂.gpr _ (by decide), w₁.gpr _ (by decide), c₄] at e₅
    rw [e₆', w₆.gpr _ (by decide), w₅.gpr _ (by decide), w₄.gpr _ (by decide), w₃.gpr _ (by decide),
      w₂.gpr _ (by decide), w₁.gpr _ (by decide), c₆] at e₇
    rw [e₈', w₈.gpr _ (by decide), w₇.gpr _ (by decide), w₆.gpr _ (by decide), w₅.gpr _ (by decide),
      w₄.gpr _ (by decide), w₃.gpr _ (by decide), w₂.gpr _ (by decide), w₁.gpr _ (by decide), c₈] at e₉
    have r26 : t₉.gpr .r26 = t₁.gpr .r26 := by
      rw [w₉.gpr _ (by decide), w₈.gpr _ (by decide), w₇.gpr _ (by decide), w₆.gpr _ (by decide),
        w₅.gpr _ (by decide), w₄.gpr _ (by decide), w₃.gpr _ (by decide), w₂.gpr _ (by decide)]
    have r27 : t₉.gpr .r27 = t₃.gpr .r27 := by
      rw [w₉.gpr _ (by decide), w₈.gpr _ (by decide), w₇.gpr _ (by decide), w₆.gpr _ (by decide),
        w₅.gpr _ (by decide), w₄.gpr _ (by decide)]
    have r28 : t₉.gpr .r28 = t₅.gpr .r28 := by
      rw [w₉.gpr _ (by decide), w₈.gpr _ (by decide), w₇.gpr _ (by decide), w₆.gpr _ (by decide)]
    have r29 : t₉.gpr .r29 = t₇.gpr .r29 := by rw [w₉.gpr _ (by decide), w₈.gpr _ (by decide)]
    have hc := Bool.toNat_le s.ca
    have hc₁ := Bool.toNat_le t₁.ca
    have h1 := (t₁.gpr .r26).isLt
    unfold Vv
    simp only [accR4, wordsVal4, r26, r27, r28, r29]
    simp only [Nat.reducePow, show dT + 32 + 8 = dT + 40 by omega, show dT + 32 + 16 = dT + 48 by omega,
      show dT + 32 + 24 = dT + 56 by omega] at *
    omega
  · rw [w₉.gpr _ (by decide), w₈.gpr _ (by decide), w₇.gpr _ (by decide), w₆.gpr _ (by decide),
      w₅.gpr _ (by decide), w₄.gpr _ (by decide), w₃.gpr _ (by decide), w₂.gpr _ (by decide)]
    have := Bool.toNat_le s.ca
    have := Bool.toNat_le t₁.ca
    omega
  · rw [w₉.mem, w₈.mem, w₇.mem, w₆.mem, w₅.mem, w₄.mem, w₃.mem, w₂.mem, w₁.mem]
  · exact ((((((((w₁.keep.trans w₂.keep).trans w₃.keep).trans w₄.keep).trans w₅.keep).trans w₆.keep).trans
      w₇.keep).trans w₈.keep).trans w₉.keep).mono (by decide)

/-- The chunk's words of `b` and `m` loaded, their pointers a chunk on. -/
theorem loadBM_ok {s : State} {B : Addr} {Z dB dM : Nat} (hs : Scr s B Z) (h7 : s.gpr .r7 = off B dB)
    (h12 : s.gpr .r12 = off B dM) (hB : dB + 32 ≤ Z) (hM : dM + 32 ≤ Z) :
    WP isa (.block loadBM) s fun t =>
      (rv t bR 4 = wordsVal s.mem B dB 4 ∧ rv t mR 4 = wordsVal s.mem B dM 4 ∧ t.gpr .r18 = word s.mem B dM ∧
        t.gpr .r7 = off B (dB + 32) ∧ t.gpr .r12 = off B (dM + 32) ∧ t.mem = s.mem ∧ t.ca = s.ca) ∧
        Keep [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r2, .r7, .r12] s t := by
  unfold loadBM
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (load4_ok (f := bR) (p := .r7) hs h7 hB (by decide)) fun t₁ ⟨⟨e₁, _, m₁, c₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (load4_ok (f := mR) (p := .r12) (hs.congr k₁.wr) (by rw [k₁.gpr _ (by decide), h12]) hM (by decide))
    fun t₂ ⟨⟨e₂, f₂, m₂, c₂⟩, k₂⟩ => ?_
  refine wp_addi (by decide) (by decide) fun t₃ w₃ e₃ c₃ => ?_
  refine wp_addi (by decide) (by decide) fun t₄ w₄ e₄ c₄ =>
    WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [c₄, c₃, c₂, c₁]⟩, ?_⟩
  · rw [rv_congr 4 (bR_keep ((k₂.trans (w₃.keep.trans w₄.keep)).mono (by decide) : Keep [.r18, .r19, .r20, .r2, .r7, .r12] t₁ t₄)),
      e₁]
  · rw [rv_congr 4 (mR_keep ((w₃.keep.trans w₄.keep).mono (by decide) : Keep [.r7, .r12] t₂ t₄)), e₂, m₁]
  · rw [w₄.gpr _ (by decide), w₃.gpr _ (by decide), ← m₁]; exact f₂
  · rw [w₄.gpr _ (by decide), e₃, k₂.gpr _ (by decide), k₁.gpr _ (by decide), h7, off_add]
  · rw [e₄, w₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide), h12, off_add]
  · rw [w₄.mem, w₃.mem, m₂, m₁]
  · exact ((k₁.trans k₂).trans (w₃.keep.trans w₄.keep)).mono (by decide)

/-! ## The chunks -/

/-- The registers a group's chunks write. -/
def chunkRegs : List Reg :=
  [.r2, .r3, .r7, .r9, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r23, .r24, .r25, .r26, .r27, .r28,
    .r29, .r30, .r31]

/-- The registers a later chunk writes. -/
def chunkTRegs : List Reg :=
  [.r2, .r7, .r9, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

theorem shr3_2w (w : Nat) (hw : w < 2 ^ 31) : BitVec.ofNat 64 (2 * w) >>> 3 = BitVec.ofNat 64 (w / 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- The first chunk of a group (`chunk0`), `T` at `dA` (`r8`), `b` at `dB`,
`m` at `dM`, the group's words of `a` at `da`: the window's low words `T`'s,
the four rows, the `uᵢ` stored at `T`'s low words (`U`), and `2²⁵⁶ Vv = T₀ + b₀
A + m₀ U` for the chunk's four words `T₀`, `b₀`, `m₀` and the group's `A`. -/
theorem chunk0_ok {s : State} {B : Addr} {Z da dA dB dM w : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h6 : s.gpr .r6 = off B da) (h7 : s.gpr .r7 = off B dB) (h8 : s.gpr .r8 = off B dA)
    (h10 : s.gpr .r10 = off B dM) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw' : w < 2 ^ 31)
    (hm : ((word s.mem B dM).toNat * (word s.mem B (dA + 8 * (w + 1))).toNat + 1) % 2 ^ 64 = 0)
    (ha : da + 32 ≤ Z) (hA : dA + 8 * (w + 2) ≤ Z) (hw4 : 4 ≤ w) (hB : dB + 32 ≤ Z) (hM : dM + 32 ≤ Z)
    (hda : da + 32 ≤ dA ∨ dA + 32 ≤ da) :
    WP isa (.block chunk0) s fun t =>
      (2 ^ 256 * Vv t = wordsVal s.mem B dA 4 + wordsVal s.mem B dB 4 * wordsVal s.mem B da 4 +
          wordsVal s.mem B dM 4 * wordsVal t.mem B dA 4 ∧ (t.gpr .r26).toNat ≤ 1 ∧ Outside B dA 32 s.mem t.mem ∧
        t.gpr .r9 = off B dA ∧ t.gpr .r12 = off B (dM + 32) ∧ t.gpr .r7 = off B (dB + 32) ∧
        t.gpr .r3 = BitVec.ofNat 64 (w / 4 - 1)) ∧ Keep chunkRegs s t := by
  have hnw := hs.nowrap
  unfold chunk0
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  have a1 : BitVec.ofNat 64 (8 * w) + off B dA = off B (dA + 8 * w) := by rw [BitVec.add_comm, off_add]
  have a2 : off B (dA + 8 * w + 8) = off B (dA + 8 * (w + 1)) := by rw [show dA + 8 * w + 8 = dA + 8 * (w + 1) by omega]
  refine WP.mono (WP.keep [.r9, .r12, .r22, .r23, .r3] (Q := fun u => u.gpr .r9 = off B dA ∧ u.gpr .r12 = off B dM ∧
      u.gpr .r23 = word s.mem B (dA + 8 * (w + 1)) ∧ u.gpr .r3 = BitVec.ofNat 64 (w / 4 - 1) ∧ u.mem = s.mem) (by
        prun [h8, h10, h11, shl2_8 w, BitVec.add_zero, a1, a2, hs.ld (show dA + 8 * (w + 1) + 8 ≤ Z by omega),
          shr3_2w w hw', VG.Proof.Bignum.PPC64LE.ofNat_sub_one (n := w / 4) (by omega) (by omega)])
      (by decide)) fun u ⟨⟨u9, u12, u23, u3, um⟩, ku⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadBM_ok (hs.congr ku.wr) (by rw [ku.gpr _ (by decide), h7]) u12 hB hM)
    fun t₁ ⟨⟨b₁, m₁, r18, r7₁, r12₁, mm₁, _⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (load4_ok (f := accR) (p := .r9) (d := dA) (hs.congr (k₁.wr.trans ku.wr)) (by rw [k₁.gpr _ (by decide), u9])
      (by omega) (by decide)) fun t₂ ⟨⟨a₂, _, mm₂, _⟩, k₂⟩ => ?_
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine wp_write (exec_li (by decide)) fun t₃ w₃ e₃ _ => ?_
  refine wp_addc fun t₄ w₄ e₄ => ?_
  have K₄ : Keep [.r9, .r12, .r22, .r23, .r3, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r2, .r7, .r27, .r28, .r29,
      .r30, .r26] s t₄ := ((((ku.trans k₁).trans k₂).trans w₃.keep).trans w₄.keep).mono (by decide)
  have m₄ : t₄.mem = s.mem := by rw [w₄.mem, w₃.mem, mm₂, mm₁, um]
  have g : ∀ r ∈ [Reg.r3, .r7, .r9, .r12, .r18, .r23], t₄.gpr r = t₁.gpr r := fun r hr => by
    rw [w₄.gpr r (by revert r hr; decide), w₃.gpr r (by revert r hr; decide), k₂.gpr r (by revert r hr; decide)]
  have g23 : t₄.gpr .r23 = word s.mem B (dA + 8 * (w + 1)) := by rw [g _ (by decide), k₁.gpr _ (by decide), u23]
  have g18 : t₄.gpr .r18 = word s.mem B dM := by rw [g _ (by decide), r18, um]
  refine WP.mono (rows0_ok 4 (da := da) (dT := dA) (hs.congr K₄.wr) (by rw [K₄.gpr _ (by decide), h0])
      (by rw [K₄.gpr _ (by decide), h6]) (by rw [g _ (by decide), k₁.gpr _ (by decide), u9]) (Nat.le_refl _) ha
      (by omega) hda (by rw [w₄.gpr _ (by decide), e₃]; decide) (by rw [g18, g23]; exact hm))
    fun t ⟨⟨e₅, _, c₅, o₅⟩, k₅⟩ => ?_
  have K : Keep chunkRegs s t := (K₄.trans k₅).mono (by decide)
  refine ⟨⟨?_, c₅ (by decide), by rw [← m₄]; exact o₅, by rw [k₅.gpr _ (by decide), g _ (by decide),
      k₁.gpr _ (by decide), u9], by rw [k₅.gpr _ (by decide), g _ (by decide), r12₁],
    by rw [k₅.gpr _ (by decide), g _ (by decide), r7₁],
    by rw [k₅.gpr _ (by decide), g _ (by decide), k₁.gpr _ (by decide), u3]⟩, K⟩
  -- The window from `T`'s low words, `r26` and CA 0.
  have z0 : (t₃.gpr .r0).toNat = 0 := by
    rw [w₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide), ku.gpr _ (by decide), h0]; rfl
  rw [z0, w₃.gpr .r27 (by decide), Nat.add_zero] at e₄
  have v₄ : Vv t₄ = wordsVal s.mem B dA 4 := by
    unfold Vv
    have r26 : t₄.gpr .r26 = 0 := by rw [w₄.gpr _ (by decide), e₃]; rfl
    have h27 := (t₄.gpr .r27).isLt
    have c : t₄.ca.toNat = 0 := by
      have := (t₂.gpr .r27).isLt
      omega
    have r27 : t₄.gpr .r27 = t₂.gpr .r27 := by
      apply BitVec.eq_of_toNat_eq
      omega
    rw [r26, c, ← um, ← mm₁, ← a₂]
    simp only [accR4, show (0 : BitVec 64).toNat = 0 from rfl]
    rw [r27, w₄.gpr _ (by decide), w₄.gpr _ (by decide), w₄.gpr _ (by decide), w₃.gpr _ (by decide),
      w₃.gpr _ (by decide), w₃.gpr _ (by decide)]
    omega
  have bB : rv t₄ bR 4 = wordsVal s.mem B dB 4 := by
    rw [rv_congr 4 (bR_keep ((k₂.trans (w₃.keep.trans w₄.keep)).mono (by decide) : Keep [.r27, .r28, .r29, .r30, .r26] t₁ t₄)),
      b₁, um]
  have mM : rv t₄ mR 4 = wordsVal s.mem B dM 4 := by
    rw [rv_congr 4 (mR_keep ((k₂.trans (w₃.keep.trans w₄.keep)).mono (by decide) : Keep [.r27, .r28, .r29, .r30, .r26] t₁ t₄)),
      m₁, um]
  rw [v₄, bB, mM, m₄] at e₅
  exact e₅

/-- A later chunk (`chunkT`), the chunk below at `dT` (`r9`), the chunk's words
of `b` and `m` at `dB` and `dM`: the chunk's words of `T` added, the four
rows, and `2²⁵⁶ Vv' + O = Vv + T_c + b_c A + m_c U` for the words `O` stored
at `dT`, the chunk's words `T_c`, `b_c`, `m_c`, the group's `A` and the `U`
at `dT`, moved a chunk up. -/
theorem chunkT_ok {s : State} {B : Addr} {Z da dT dB dM : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h6 : s.gpr .r6 = off B da) (h7 : s.gpr .r7 = off B dB) (h9 : s.gpr .r9 = off B dT)
    (h12 : s.gpr .r12 = off B dM) (h26 : (s.gpr .r26).toNat ≤ 1) (ha : da + 32 ≤ Z) (hT : dT + 64 ≤ Z)
    (hB : dB + 32 ≤ Z) (hM : dM + 32 ≤ Z) (hda : da + 32 ≤ dT ∨ dT + 64 ≤ da) :
    WP isa (.block chunkT) s fun t =>
      (2 ^ 256 * Vv t + wordsVal t.mem B dT 4 = Vv s + wordsVal s.mem B (dT + 32) 4 +
          wordsVal s.mem B dB 4 * wordsVal s.mem B da 4 + wordsVal s.mem B dM 4 * wordsVal s.mem B dT 4 ∧
        wordsVal t.mem B (dT + 32) 4 = wordsVal s.mem B dT 4 ∧ (t.gpr .r26).toNat ≤ 1 ∧
        Outside B dT 64 s.mem t.mem ∧ t.gpr .r9 = off B (dT + 32) ∧ t.gpr .r7 = off B (dB + 32) ∧
        t.gpr .r12 = off B (dM + 32)) ∧ Keep chunkTRegs s t := by
  have hnw := hs.nowrap
  unfold chunkT
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (addT_ok hs h9 hT h26) fun t₁ ⟨⟨v₁, c₁, m₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadBM_ok (hs.congr k₁.wr) (by rw [k₁.gpr _ (by decide), h7]) (by rw [k₁.gpr _ (by decide), h12])
    hB hM) fun t₂ ⟨⟨b₂, m₂', _, r7₂, r12₂, mm₂, ca₂⟩, k₂⟩ => ?_
  have K₂ : Keep [.r26, .r22, .r27, .r28, .r29, .r30, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r2, .r7, .r12] s t₂ :=
    (k₁.trans k₂).mono (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (rowsT_ok 4 (da := da) (dT := dT) (hs.congr K₂.wr) (by rw [K₂.gpr _ (by decide), h0])
    (by rw [K₂.gpr _ (by decide), h6]) (by rw [K₂.gpr _ (by decide), h9]) (Nat.le_refl _) ha hT hda
    (by rw [k₂.gpr _ (by decide)]; exact c₁)) fun t₃ ⟨⟨e₃, u₃, _, _, c₃, o₃⟩, k₃⟩ => ?_
  refine wp_addi (by decide) (by decide) fun t w e ca => WP.block_nil ⟨⟨?_, ?_, by rw [w.gpr _ (by decide)]; exact c₃ (by decide),
    by rw [w.mem, ← m₁, ← mm₂]; exact o₃, by rw [e, k₃.gpr _ (by decide), K₂.gpr _ (by decide), h9, off_add],
    by rw [w.gpr _ (by decide), k₃.gpr _ (by decide), r7₂], by rw [w.gpr _ (by decide), k₃.gpr _ (by decide), r12₂]⟩,
    ((K₂.trans k₃).trans w.keep).mono (by decide)⟩
  · have vt : Vv t = Vv t₃ := by
      unfold Vv
      rw [rv_congr 4 fun j hj => w.gpr _ (show accR j ≠ .r9 by revert j; decide), w.gpr _ (by decide), ca]
    have v₂ : Vv t₂ = Vv t₁ := by
      unfold Vv
      rw [rv_congr 4 fun j hj => accR_keep k₂ (by decide) j (by omega), k₂.gpr _ (by decide), ca₂]
    rw [vt, w.mem, e₃, v₂, v₁, b₂, m₂', mm₂, m₁]
  · rw [w.mem, u₃, mm₂, m₁]

/-! ## A group -/

/-- After the first chunk and `i` more of a group that started in `g`, `T` at
`dA`, `b` at `dB`, `m` at `dM`, the group's words of `a` at `da`: `r9` at
chunk `i`, which holds the `uᵢ` (`U`), the words of `T` from chunk `i + 1` on
as they were, and `2^(256 (i + 1)) Vv + 2²⁵⁶ O = T' + b' A + m' U` for the
words `O` stored below chunk `i` and the first `i + 1` chunks `T'`, `b'`,
`m'` of `T`, `b` and `m`. -/
def ChunkInv (g : State) (B : Addr) (da dA dB dM i : Nat) (t : State) : Prop :=
  t.gpr .r9 = off B (dA + 32 * i) ∧ t.gpr .r7 = off B (dB + 32 * (i + 1)) ∧ t.gpr .r12 = off B (dM + 32 * (i + 1)) ∧
    (t.gpr .r26).toNat ≤ 1 ∧ Outside B dA (32 * (i + 1)) g.mem t.mem ∧
    2 ^ (256 * (i + 1)) * Vv t + 2 ^ 256 * wordsVal t.mem B dA (4 * i) =
      wordsVal g.mem B dA (4 * (i + 1)) + wordsVal g.mem B dB (4 * (i + 1)) * wordsVal g.mem B da 4 +
        wordsVal g.mem B dM (4 * (i + 1)) * wordsVal t.mem B (dA + 32 * i) 4

theorem pow256 (i : Nat) : 2 ^ (64 * (4 * (i + 1))) = 2 ^ (256 * (i + 1)) := by
  rw [← Nat.mul_assoc]

theorem chunkInv_step {g t t' : State} {B : Addr} {Z da dA dB dM w i : Nat} (hs : Scr g B Z)
    (hJ : ChunkInv g B da dA dB dM i t) (hi : i + 2 ≤ w / 4) (hw : w < 2 ^ 31)
    (ha : da + 32 ≤ Z) (hA : dA + 8 * (w + 2) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (daA : da + 32 ≤ dA ∨ dA + 8 * (w + 2) ≤ da) (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ dB)
    (dMA : dM + 8 * w ≤ dA)
    (h : 2 ^ 256 * Vv t' + wordsVal t'.mem B (dA + 32 * i) 4 = Vv t + wordsVal t.mem B (dA + 32 * i + 32) 4 +
          wordsVal t.mem B (dB + 32 * (i + 1)) 4 * wordsVal t.mem B da 4 +
          wordsVal t.mem B (dM + 32 * (i + 1)) 4 * wordsVal t.mem B (dA + 32 * i) 4)
    (hu : wordsVal t'.mem B (dA + 32 * i + 32) 4 = wordsVal t.mem B (dA + 32 * i) 4) (hc : (t'.gpr .r26).toNat ≤ 1)
    (ho : Outside B (dA + 32 * i) 64 t.mem t'.mem) (h9 : t'.gpr .r9 = off B (dA + 32 * i + 32))
    (h7 : t'.gpr .r7 = off B (dB + 32 * (i + 1) + 32)) (h12 : t'.gpr .r12 = off B (dM + 32 * (i + 1) + 32)) :
    ChunkInv g B da dA dB dM (i + 1) t' := by
  have hnw := hs.nowrap
  obtain ⟨_, _, _, _, o, e⟩ := hJ
  have h4 : 4 * (w / 4) ≤ w := Nat.mul_div_le w 4
  have wT : wordsVal t.mem B (dA + 32 * i + 32) 4 = wordsVal g.mem B (dA + 32 * (i + 1)) 4 := by
    rw [o.wordsVal (by omega) (by omega)]; congr 1
  have wB : ∀ k, k ≤ 4 * (i + 2) → wordsVal t.mem B dB k = wordsVal g.mem B dB k := fun k hk =>
    o.wordsVal (by omega) (by omega)
  have wB' : wordsVal t.mem B (dB + 32 * (i + 1)) 4 = wordsVal g.mem B (dB + 32 * (i + 1)) 4 :=
    o.wordsVal (by omega) (by omega)
  have wM' : wordsVal t.mem B (dM + 32 * (i + 1)) 4 = wordsVal g.mem B (dM + 32 * (i + 1)) 4 :=
    o.wordsVal (by omega) (by omega)
  have wa : wordsVal t.mem B da 4 = wordsVal g.mem B da 4 := o.wordsVal (by omega) (by omega)
  have wO : wordsVal t'.mem B dA (4 * i) = wordsVal t.mem B dA (4 * i) := ho.wordsVal (by omega) (by omega)
  refine ⟨h9.trans (by rw [show dA + 32 * i + 32 = dA + 32 * (i + 1) by omega]),
    h7.trans (by rw [show dB + 32 * (i + 1) + 32 = dB + 32 * (i + 1 + 1) by omega]),
    h12.trans (by rw [show dM + 32 * (i + 1) + 32 = dM + 32 * (i + 1 + 1) by omega]), hc,
    (o.mono (Nat.le_refl _) (by omega)).trans (ho.mono (by omega) (by omega)), ?_⟩
  rw [wT, wB', wM', wa] at h
  rw [show 4 * (i + 1) = 4 * i + 4 by omega, fios_wordsVal_append, wO, show dA + 32 * (i + 1) = dA + 32 * i + 32 by omega,
    hu, show 8 * (4 * i) = 32 * i by omega, show 4 * (i + 1 + 1) = 4 * (i + 1) + 4 by omega,
    fios_wordsVal_append g.mem B dA, fios_wordsVal_append g.mem B dB, fios_wordsVal_append g.mem B dM,
    show 8 * (4 * (i + 1)) = 32 * (i + 1) by omega, pow256, show 256 * (i + 1 + 1) = 256 * (i + 1) + 256 by omega,
    Nat.pow_add]
  rw [show 2 ^ (64 * (4 * i)) = 2 ^ (256 * i) by rw [← Nat.mul_assoc]] at *
  rw [show dA + 32 * (i + 1) = dA + 32 * i + 32 by omega] at *
  have e' : 2 ^ (256 * (i + 1)) * 2 ^ 256 * Vv t' + 2 ^ 256 * (wordsVal t.mem B dA (4 * i) +
      2 ^ (256 * i) * wordsVal t'.mem B (dA + 32 * i) 4) =
      2 ^ (256 * (i + 1)) * (2 ^ 256 * Vv t' + wordsVal t'.mem B (dA + 32 * i) 4) +
        2 ^ 256 * wordsVal t.mem B dA (4 * i) := by
    rw [show 256 * (i + 1) = 256 * i + 256 by omega, Nat.pow_add]; grind
  rw [e', h]
  grind

theorem ChunkInv.w1 {g t t' : State} {B : Addr} {da dA dB dM i : Nat} (h : ChunkInv g B da dA dB dM i t)
    (w : W1 t t' .r3) (c : t'.ca = t.ca) : ChunkInv g B da dA dB dM i t' := by
  obtain ⟨h9, h7, h12, h26, o, e⟩ := h
  have v : Vv t' = Vv t := by
    unfold Vv
    rw [rv_congr 4 fun j _ => w.gpr _ (show accR j ≠ .r3 by revert j; decide), w.gpr _ (by decide), c]
  exact ⟨by rw [w.gpr _ (by decide), h9], by rw [w.gpr _ (by decide), h7], by rw [w.gpr _ (by decide), h12],
    by rw [w.gpr _ (by decide)]; exact h26, by rw [w.mem]; exact o, by rw [v, w.mem]; exact e⟩

/-- The chunks after the first (`chunkLoop`), counted by `r3`: `w / 4 - 1` of
them. -/
theorem chunkLoop_ok {g s : State} {B : Addr} {Z da dA dB dM w : Nat} (hs : Scr g B Z)
    (hJ : ChunkInv g B da dA dB dM 0 s) (hk : Keep chunkRegs g s) (h0 : g.gpr .r0 = 0) (h6 : g.gpr .r6 = off B da)
    (h3 : s.gpr .r3 = BitVec.ofNat 64 (w / 4 - 1)) (hw4 : 4 ≤ w) (hw : w < 2 ^ 31)
    (ha : da + 32 ≤ Z) (hA : dA + 8 * (w + 2) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (daA : da + 32 ≤ dA ∨ dA + 8 * (w + 2) ≤ da) (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ dB)
    (dMA : dM + 8 * w ≤ dA) :
    WP isa chunkLoop s fun t => ChunkInv g B da dA dB dM (w / 4 - 1) t ∧ Keep chunkRegs g t := by
  have hnw := hs.nowrap
  have h4 : 4 * (w / 4) ≤ w := Nat.mul_div_le w 4
  unfold chunkLoop
  refine WP.ite _ (eval_zero_ofNat _ _ (by omega) h3) (fun hz => ?_) (fun hz => ?_)
  · have : w / 4 - 1 = 0 := of_decide_eq_true hz
    rw [this]
    exact WP.block_nil ⟨hJ, hk⟩
  have hN : w / 4 - 1 ≠ 0 := of_decide_eq_false hz
  refine wp_countdown (N := w / 4 - 1) (by omega) (by omega)
    (fun i t => ChunkInv g B da dA dB dM i t ∧ Keep chunkRegs g t) (fun i hi t ⟨hJ', hk'⟩ ht3 => ?_) ⟨hJ, hk⟩ h3
  obtain ⟨j9, j7, j12, j26, jo, je⟩ := hJ'
  rw [WP.block_append_iff]
  refine WP.mono (chunkT_ok (da := da) (dT := dA + 32 * i) (dB := dB + 32 * (i + 1)) (dM := dM + 32 * (i + 1))
    (hs.congr hk'.wr) (by rw [hk'.gpr _ (by decide), h0]) (by rw [hk'.gpr _ (by decide), h6]) j7 j9 j12 j26 ha
    (by omega) (by omega) (by omega) (by omega)) fun t' ⟨⟨e', u', c', o', r9', r7', r12'⟩, k'⟩ => ?_
  have J' := chunkInv_step (i := i) (w := w) hs ⟨j9, j7, j12, j26, jo, je⟩ (by omega) hw ha hA hB hM daA dBA dMA e' u' c'
    o' r9' r7' r12'
  refine wp_write (exec_subi (by decide) (by decide)) fun u w e c => WP.block_nil ⟨⟨J'.w1 w c,
    (hk'.trans ((k'.trans w.keep).mono (by decide) : Keep chunkRegs t u)).mono (by decide)⟩,
    by rw [e, k'.gpr _ (by decide)]⟩

theorem wordsVal5 (m : Mem) (B : Addr) (d : Nat) : wordsVal m B d 5 = wordsVal m B d 4 +
    2 ^ 256 * (word m B (d + 32)).toNat := by
  rw [wordsVal_succ_top]

/-- The group's top (`groupEnd`), `r9` at the last chunk, `dT`: `T`'s top word
added to the window, which is stored as the new `T`'s top five words; `b`'s
pointer back to its base, `a`'s a group on, one group less. -/
theorem groupEnd_ok {s : State} {B : Addr} {Z dT dB w G : Nat} (hs : Scr s B Z) (h9 : s.gpr .r9 = off B dT)
    (hT : dT + 40 ≤ Z) (h26 : (s.gpr .r26).toNat ≤ 1) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h7 : s.gpr .r7 = off B (dB + 8 * w)) (h4 : s.gpr .r4 = BitVec.ofNat 64 G) (hG : 1 ≤ G) (hG' : G < 2 ^ 64) :
    WP isa (.block groupEnd) s fun t =>
      (wordsVal t.mem B dT 5 = Vv s + (word s.mem B (dT + 32)).toNat ∧ Outside B dT 40 s.mem t.mem ∧
        t.gpr .r7 = off B dB ∧ t.gpr .r6 = s.gpr .r6 + BitVec.ofNat 64 32 ∧ t.gpr .r4 = BitVec.ofNat 64 (G - 1)) ∧
        Keep [.r26, .r22, .r27, .r28, .r29, .r30, .r7, .r6, .r4] s t := by
  have hnw := hs.nowrap
  show WP isa (.block ([.addze .r26 .r26, .load .d .r22 .r9 32, .addc .r27 .r27 .r22, .addze .r28 .r28,
    .addze .r29 .r29, .addze .r30 .r30, .addze .r26 .r26, .store .d .r27 .r9 0, .store .d .r28 .r9 8,
    .store .d .r29 .r9 16, .store .d .r30 .r9 24, .store .d .r26 .r9 32, .lsl .r22 .r11 2, .sub .r7 .r7 .r22,
    .addi .r6 .r6 32, .subi .r4 .r4 1])) s _
  refine wp_addze fun t₁ w₁ e₁ => ?_
  refine wp_ld (by decide) ⟨by decide, by decide⟩ (by rw [w₁.gpr _ (by decide), h9, off_add])
    ((hs.congr w₁.wr).ld (by omega)) fun t₂ w₂ e₂ _ => ?_
  refine wp_addc fun t₃ w₃ e₃ => ?_
  refine wp_addze fun t₄ w₄ e₄ => ?_
  refine wp_addze fun t₅ w₅ e₅ => ?_
  refine wp_addze fun t₆ w₆ e₆ => ?_
  refine wp_addze fun t₇ w₇ e₇ => ?_
  have K₇ : Keep [.r26, .r22, .r27, .r28, .r29, .r30] s t₇ :=
    ((((((w₁.keep.trans w₂.keep).trans w₃.keep).trans w₄.keep).trans w₅.keep).trans w₆.keep).trans w₇.keep).mono
      (by decide)
  have m₇ : t₇.mem = s.mem := by rw [w₇.mem, w₆.mem, w₅.mem, w₄.mem, w₃.mem, w₂.mem, w₁.mem]
  have p9 : t₇.gpr .r9 = off B dT := by rw [K₇.gpr _ (by decide), h9]
  have hst : ∀ {u : State}, u.wr = s.wr → ∀ {o}, o ≤ 32 → InRegions u.wr (off B (dT + o)) 8 :=
    fun h o ho => (hs.congr h).st (by omega)
  refine wp_st (a := off B dT) (by decide) ⟨by decide, by decide⟩ (by rw [p9, off_add, Nat.add_zero])
    (by have := hst K₇.wr (o := 0) (by decide); rwa [Nat.add_zero] at this) fun u₁ k₁ m₁ _ => ?_
  refine wp_st (by decide) ⟨by decide, by decide⟩ (by rw [k₁.gpr _ (by simp), p9, off_add])
    (hst (k₁.wr.trans K₇.wr) (o := 8) (by decide)) fun u₂ k₂ m₂ _ => ?_
  refine wp_st (by decide) ⟨by decide, by decide⟩ (by rw [k₂.gpr _ (by simp), k₁.gpr _ (by simp), p9, off_add])
    (hst (k₂.wr.trans (k₁.wr.trans K₇.wr)) (o := 16) (by decide)) fun u₃ k₃ m₃ _ => ?_
  refine wp_st (by decide) ⟨by decide, by decide⟩
    (by rw [k₃.gpr _ (by simp), k₂.gpr _ (by simp), k₁.gpr _ (by simp), p9, off_add])
    (hst (k₃.wr.trans (k₂.wr.trans (k₁.wr.trans K₇.wr))) (o := 24) (by decide)) fun u₄ k₄ m₄ _ => ?_
  refine wp_st (by decide) ⟨by decide, by decide⟩
    (by rw [k₄.gpr _ (by simp), k₃.gpr _ (by simp), k₂.gpr _ (by simp), k₁.gpr _ (by simp), p9, off_add])
    (hst (k₄.wr.trans (k₃.wr.trans (k₂.wr.trans (k₁.wr.trans K₇.wr)))) (o := 32) (by decide)) fun u₅ k₅ m₅ _ => ?_
  have g : ∀ r, u₅.gpr r = t₇.gpr r := fun r => by
    rw [k₅.gpr _ (by simp), k₄.gpr _ (by simp), k₃.gpr _ (by simp), k₂.gpr _ (by simp), k₁.gpr _ (by simp)]
  refine wp_write (exec_lsl (by decide)) fun v₁ x₁ f₁ _ => ?_
  refine wp_write exec_sub fun v₂ x₂ f₂ _ => ?_
  refine wp_addi (by decide) (by decide) fun v₃ x₃ f₃ _ => ?_
  refine wp_write (exec_subi (by decide) (by decide)) fun t x₄ f₄ _ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- The value stored.
    have mt : t.mem = u₅.mem := by rw [x₄.mem, x₃.mem, x₂.mem, x₁.mem]
    have wo : ∀ (m : Mem) (e d : Nat) (v : BitVec 64), (d + 8 ≤ e ∨ e + 8 ≤ d) → e + 8 ≤ Z → d + 8 ≤ Z →
        word (m.writeW (off B e) v) B d = word m B d := fun m e d v h he hd =>
      (writeW_outside m B v (by omega)).word (by omega) (by omega)
    rw [mt, m₅, m₄, m₃, m₂, m₁, wordsVal5, wordsVal4, word_writeW_self,
      wo _ _ dT _ (by omega) (by omega) (by omega), wo _ _ dT _ (by omega) (by omega) (by omega),
      wo _ _ dT _ (by omega) (by omega) (by omega), wo _ _ dT _ (by omega) (by omega) (by omega), word_writeW_self,
      wo _ _ (dT + 8) _ (by omega) (by omega) (by omega), wo _ _ (dT + 8) _ (by omega) (by omega) (by omega),
      wo _ _ (dT + 8) _ (by omega) (by omega) (by omega), word_writeW_self,
      wo _ _ (dT + 16) _ (by omega) (by omega) (by omega), wo _ _ (dT + 16) _ (by omega) (by omega) (by omega),
      word_writeW_self, wo _ _ (dT + 24) _ (by omega) (by omega) (by omega), word_writeW_self]
    simp only [k₁.gpr _ (List.not_mem_nil), k₂.gpr _ (List.not_mem_nil), k₃.gpr _ (List.not_mem_nil),
      k₄.gpr _ (List.not_mem_nil)]
    have e₂' : t₂.gpr .r22 = word s.mem B (dT + 32) := by rw [e₂, w₁.mem]
    rw [e₂', w₂.gpr _ (by decide), w₁.gpr _ (by decide)] at e₃
    rw [w₃.gpr _ (by decide), w₂.gpr _ (by decide), w₁.gpr _ (by decide)] at e₄
    rw [w₄.gpr _ (by decide), w₃.gpr _ (by decide), w₂.gpr _ (by decide), w₁.gpr _ (by decide)] at e₅
    rw [w₅.gpr _ (by decide), w₄.gpr _ (by decide), w₃.gpr _ (by decide), w₂.gpr _ (by decide),
      w₁.gpr _ (by decide)] at e₆
    rw [w₆.gpr _ (by decide), w₅.gpr _ (by decide), w₄.gpr _ (by decide), w₃.gpr _ (by decide),
      w₂.gpr _ (by decide)] at e₇
    have r27 : t₇.gpr .r27 = t₃.gpr .r27 := by
      rw [w₇.gpr _ (by decide), w₆.gpr _ (by decide), w₅.gpr _ (by decide), w₄.gpr _ (by decide)]
    have r28 : t₇.gpr .r28 = t₄.gpr .r28 := by
      rw [w₇.gpr _ (by decide), w₆.gpr _ (by decide), w₅.gpr _ (by decide)]
    have r29 : t₇.gpr .r29 = t₅.gpr .r29 := by rw [w₇.gpr _ (by decide), w₆.gpr _ (by decide)]
    have r30 : t₇.gpr .r30 = t₆.gpr .r30 := w₇.gpr _ (by decide)
    rw [r27, r28, r29, r30]
    unfold Vv
    simp only [accR4]
    have := Bool.toNat_le s.ca; have := Bool.toNat_le t₁.ca; have := Bool.toNat_le t₆.ca
    have := (t₁.gpr .r26).isLt; have := (t₇.gpr .r26).isLt
    simp only [Nat.reducePow] at *
    omega
  · rw [x₄.mem, x₃.mem, x₂.mem, x₁.mem, m₅, m₄, m₃, m₂, m₁, m₇]
    have o : ∀ (m : Mem) (e : Nat) (v : BitVec 64), dT ≤ e → e + 8 ≤ dT + 40 →
        Outside B dT 40 m (m.writeW (off B e) v) := fun m e v h₁ h₂ =>
      (writeW_outside m B v (by omega)).mono h₁ h₂
    refine Outside.trans ?_ (o _ _ _ (by omega) (by omega))
    refine Outside.trans ?_ (o _ _ _ (by omega) (by omega))
    refine Outside.trans ?_ (o _ _ _ (by omega) (by omega))
    refine Outside.trans ?_ (o _ _ _ (by omega) (by omega))
    exact o _ _ _ (by omega) (by omega)
  · rw [x₄.gpr _ (by decide), x₃.gpr _ (by decide), f₂, x₁.gpr _ (by decide), f₁, g, g, K₇.gpr _ (by decide),
      K₇.gpr _ (by decide), h7, h11, shl2_8 w, VG.Offset.add_ofNat_sub _ (by omega), Nat.add_sub_cancel]
  · rw [x₄.gpr _ (by decide), f₃, x₂.gpr _ (by decide), x₁.gpr _ (by decide), g, K₇.gpr _ (by decide)]
  · rw [f₄, x₃.gpr _ (by decide), x₂.gpr _ (by decide), x₁.gpr _ (by decide), g, K₇.gpr _ (by decide), h4,
      VG.Proof.Bignum.PPC64LE.ofNat_sub_one hG hG']
  · exact (((((K₇.trans k₁).trans k₂).trans k₃).trans k₄).trans k₅ |>.trans x₁.keep |>.trans x₂.keep |>.trans x₃.keep
      |>.trans x₄.keep).mono (by decide)

/-- The registers a group writes. -/
def groupRegs : List Reg := chunkRegs ++ [.r6, .r4]

/-- One group (`group`), for `w` a multiple of 4: `T := (T + A b + U m) / 2²⁵⁶`
for the group's four words `A` of `a` (at `da`) and some `U < 2²⁵⁶`; `a`'s
pointer a group on, one group less in `r4`. -/
theorem group_ok {s : State} {B : Addr} {Z da dA dB dM w G : Nat} (hs : Scr s B Z) (h0 : s.gpr .r0 = 0)
    (h6 : s.gpr .r6 = off B da) (h7 : s.gpr .r7 = off B dB) (h8 : s.gpr .r8 = off B dA)
    (h10 : s.gpr .r10 = off B dM) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (h4 : s.gpr .r4 = BitVec.ofNat 64 G)
    (hG : 1 ≤ G) (hG' : G < 2 ^ 64) (hw4 : 4 ≤ w) (hw40 : w % 4 = 0) (hw' : w < 2 ^ 31)
    (hm : ((word s.mem B dM).toNat * (word s.mem B (dA + 8 * (w + 1))).toNat + 1) % 2 ^ 64 = 0)
    (ha : da + 32 ≤ Z) (hA : dA + 8 * (w + 2) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (daA : da + 32 ≤ dA ∨ dA + 8 * (w + 2) ≤ da) (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ dB)
    (dMA : dM + 8 * w ≤ dA) :
    WP isa group s fun t =>
      ((∃ U < 2 ^ 256, 2 ^ 256 * wordsVal t.mem B dA (w + 1) =
          wordsVal s.mem B dA (w + 1) + wordsVal s.mem B dB w * wordsVal s.mem B da 4 + wordsVal s.mem B dM w * U) ∧
        Outside B dA (8 * (w + 1)) s.mem t.mem ∧ t.gpr .r6 = off B (da + 32) ∧ t.gpr .r7 = off B dB ∧
        t.gpr .r4 = BitVec.ofNat 64 (G - 1)) ∧ Keep groupRegs s t := by
  have hnw := hs.nowrap
  have hq : w = 4 * (w / 4) := by omega
  unfold group
  refine WP.seq (WP.mono (chunk0_ok hs h0 h6 h7 h8 h10 h11 hw' hm ha hA hw4 (by omega) (by omega)
    (by omega)) fun t₁ ⟨⟨e₁, c₁, o₁, r9₁, r12₁, r7₁, r3₁⟩, k₁⟩ => ?_)
  have J₁ : ChunkInv s B da dA dB dM 0 t₁ := ⟨by rw [r9₁]; rfl, by rw [r7₁], by rw [r12₁], c₁, o₁,
    by simpa [wordsVal] using e₁⟩
  refine WP.seq (WP.mono (chunkLoop_ok hs J₁ k₁ h0 h6 r3₁ hw4 hw' ha hA hB hM daA dBA dMA)
    fun t₂ ⟨J₂, k₂⟩ => ?_)
  obtain ⟨j9, j7, j12, j26, jo, je⟩ := J₂
  have ei : w / 4 - 1 + 1 = w / 4 := by omega
  rw [ei] at j7 je jo
  rw [← hq] at je
  refine WP.mono (groupEnd_ok (dT := dA + 32 * (w / 4 - 1)) (dB := dB) (w := w) (G := G) (hs.congr k₂.wr) j9
    (by omega) j26 (by rw [k₂.gpr _ (by decide), h11]) (by rw [j7, show 32 * (w / 4) = 8 * w by omega])
    (by rw [k₂.gpr _ (by decide), h4]) hG hG') fun t ⟨⟨e, o, r7, r6, r4⟩, k⟩ => ?_
  refine ⟨⟨⟨wordsVal t₂.mem B (dA + 32 * (w / 4 - 1)) 4, wordsVal_lt _ _ _ _, ?_⟩,
    (jo.mono (Nat.le_refl _) (by omega)).trans (o.mono (by omega) (by omega)),
    by rw [r6, k₂.gpr _ (by decide), h6, off_add], r7, r4⟩, (k₂.trans k).mono (by decide)⟩
  have wT : word t₂.mem B (dA + 32 * (w / 4 - 1) + 32) = word s.mem B (dA + 8 * w) := by
    rw [show dA + 32 * (w / 4 - 1) + 32 = dA + 8 * w by omega]
    exact jo.word (by omega) (by omega)
  rw [wT] at e
  have wO : wordsVal t.mem B dA (4 * (w / 4 - 1)) = wordsVal t₂.mem B dA (4 * (w / 4 - 1)) :=
    o.wordsVal (by omega) (by omega)
  rw [show w + 1 = 4 * (w / 4 - 1) + 5 by omega, fios_wordsVal_append, wO,
    show dA + 8 * (4 * (w / 4 - 1)) = dA + 32 * (w / 4 - 1) by omega, e,
    show 4 * (w / 4 - 1) + 5 = w + 1 by omega, wordsVal_succ_top s.mem B dA w]
  have p : 2 ^ (64 * (4 * (w / 4 - 1))) = 2 ^ (256 * (w / 4 - 1)) := by rw [← Nat.mul_assoc]
  have p' : 2 ^ (256 * (w / 4)) = 2 ^ 256 * 2 ^ (256 * (w / 4 - 1)) := by
    rw [← Nat.pow_add]; congr 1; omega
  have p'' : 2 ^ (64 * w) = 2 ^ (256 * (w / 4)) := by congr 1; omega
  rw [p, p'', p']
  rw [p'] at je
  grind

end VG.Proof.Bignum.PPC64LE.Mont4

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE
open VG.Proof.Bignum.PPC64LE.Mont4 (group_ok groupRegs shr3_2w shl2_8)

/-! ## The groups -/

/-- `T' < 2 m` after a group, for `T < 2 m`. -/
theorem group_lt {T T' A b U m : Nat} (h : 2 ^ 256 * T' = T + b * A + m * U) (hT : T < 2 * m)
    (hA : A < 2 ^ 256) (hb : b < m) (hU : U < 2 ^ 256) : T' < 2 * m := by
  have h₁ : b * A ≤ (m - 1) * (2 ^ 256 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have h₂ : m * U ≤ m * (2 ^ 256 - 1) := Nat.mul_le_mul_left _ (by omega)
  simp only [Nat.reducePow, Nat.reduceSub] at *
  omega

/-- The groups' invariant `2^(256 i) T ≡ A_i b (mod m)`, one group on. -/
theorem group_step {P T T' A b U m Ai : Nat} (h : 2 ^ 256 * T' = T + b * A + m * U)
    (hI : P * T % m = Ai * b % m) : P * 2 ^ 256 * T' % m = (Ai + P * A) * b % m := by
  have e : P * 2 ^ 256 * T' = P * T + P * A * b + P * U * m := by rw [Nat.mul_assoc, h]; grind
  rw [e, Nat.add_mul_mod_self_right, Nat.add_mod, hI, ← Nat.add_mod, Nat.add_mul]

/-- The registers the kernel's rounds write. -/
def roundsRegs4 : List Reg := roundsRegs ++ [.r2, .r23, .r24, .r25, .r26]

theorem rounds4_regs : ∀ r, r ∈ groupRegs ++ ([.r0] : List Reg) ++ ([.r22, .r9] : List Reg) →
    r ∈ roundsRegs4 ∨ r = .r7 ∨ r = .r9 := by
  decide

/-- The rounds of the kernel for `w` a multiple of 4 (`rounds4`): `RoundsSpecW`'s
conclusion. -/
theorem rounds4_ok {s₀ : State} {B : Addr} {Z da dA dB dM w : Nat} (hs : Scr s₀ B Z)
    (h6 : s₀.gpr .r6 = off B da) (h8 : s₀.gpr .r8 = off B dA) (h7 : s₀.gpr .r7 = off B dB)
    (h9 : s₀.gpr .r9 = off B (dA + 8 * (w + 2))) (h10 : s₀.gpr .r10 = off B dM)
    (h11 : s₀.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hm : ((word s₀.mem B dM).toNat * (s₀.gpr .r22).toNat + 1) % 2 ^ 64 = 0)
    (h22 : s₀.gpr .r22 = word s₀.mem B (dA + 8 * (w + 1)))
    (hw : 4 ≤ w) (hw40 : w % 4 = 0) (hw' : w < 2 ^ 31) (hlay : dA = dM + 16 * (w + 2))
    (ha : da + 8 * w ≤ Z) (hA : dA + 8 * (w + 2) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (daA : da + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ da) (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 2) ≤ dB)
    (hz : wordsVal s₀.mem B dA (w + 1) = 0) (hb : wordsVal s₀.mem B dB w < wordsVal s₀.mem B dM w) :
    WP isa rounds4 s₀ fun s =>
      (wordsVal s.mem B dA (w + 1) < 2 * wordsVal s₀.mem B dM w ∧
        2 ^ (64 * w) * wordsVal s.mem B dA (w + 1) % wordsVal s₀.mem B dM w =
          wordsVal s₀.mem B da w * wordsVal s₀.mem B dB w % wordsVal s₀.mem B dM w ∧
        Outside B dA (8 * (w + 2)) s₀.mem s.mem ∧ s.gpr .r22 = s₀.gpr .r22) ∧
      Keep roundsRegs4 s₀ s := by
  have hnw := hs.nowrap
  have hq : w = 4 * (w / 4) := by omega
  let M := wordsVal s₀.mem B dM w
  let Bv := wordsVal s₀.mem B dB w
  unfold rounds4
  refine WP.seq (WP.mono (WP.keep [.r0, .r4] (Q := fun u => u.gpr .r0 = 0 ∧ u.gpr .r4 = BitVec.ofNat 64 (w / 4) ∧
      u.mem = s₀.mem) (by prun [h11, shr3_2w w hw']; rfl) (by decide)) fun s₁ ⟨⟨a0, a4, am⟩, k₁⟩ => ?_)
  let J : Nat → State → Prop := fun i s =>
    s.gpr .r6 = off B (da + 32 * i) ∧ s.gpr .r7 = off B dB ∧ s.gpr .r0 = 0 ∧
      Outside B dA (8 * (w + 1)) s₀.mem s.mem ∧ wordsVal s.mem B dA (w + 1) < 2 * M ∧
      2 ^ (256 * i) * wordsVal s.mem B dA (w + 1) % M = wordsVal s₀.mem B da (4 * i) * Bv % M ∧
      Keep (groupRegs ++ [.r0]) s₀ s
  have hJ0 : J 0 s₁ := ⟨by rw [k₁.gpr _ (by decide), h6]; rfl, by rw [k₁.gpr _ (by decide), h7], a0,
    by rw [am]; exact Outside.refl _ _ _ _, by rw [am, hz]; omega, by rw [am, hz]; simp [wordsVal],
    k₁.mono (by decide)⟩
  refine WP.seq (WP.mono (VG.Proof.Bignum.PPC64LE.wp_countdown (cnt := .r4) (N := w / 4) (by omega) (by omega) J
    (fun i hi s hJ h4 => ?_) hJ0 a4) fun s₂ hJ₂ => ?_)
  · obtain ⟨j6, j7, j0, jo, jlt, jeq, jk⟩ := hJ
    have g : ∀ r ∈ [Reg.r8, .r10, .r11], s.gpr r = s₀.gpr r := fun r hr => jk.gpr r (by revert r hr; decide)
    have vM : wordsVal s.mem B dM w = M := jo.wordsVal (by omega) (by omega)
    have vB : wordsVal s.mem B dB w = Bv := jo.wordsVal (by omega) (by omega)
    have wM : word s.mem B dM = word s₀.mem B dM := jo.word (by omega) (by omega)
    have wm' : word s.mem B (dA + 8 * (w + 1)) = word s₀.mem B (dA + 8 * (w + 1)) := jo.word (by omega) (by omega)
    have wa : wordsVal s.mem B (da + 32 * i) 4 = wordsVal s₀.mem B (da + 32 * i) 4 := jo.wordsVal (by omega) (by omega)
    refine WP.mono (group_ok (da := da + 32 * i) (dA := dA) (dB := dB) (dM := dM) (w := w) (G := w / 4 - i)
      (hs.congr jk.wr) j0 j6 j7 (by rw [g _ (by decide), h8]) (by rw [g _ (by decide), h10])
      (by rw [g _ (by decide), h11]) h4 (by omega) (by omega) hw hw40 hw' (by rw [wM, wm', ← h22]; exact hm)
      (by omega) hA hB hM (by omega) dBA (by omega)) fun s' ⟨⟨⟨U, hU, e⟩, o, r6, r7, r4⟩, k⟩ => ⟨⟨?_, r7, ?_, ?_, ?_, ?_,
        (jk.trans k).mono (by decide)⟩, ?_⟩
    · rw [r6, show da + 32 * i + 32 = da + 32 * (i + 1) by omega]
    · rw [k.gpr _ (by decide), j0]
    · exact jo.trans o
    · rw [vM, vB, wa] at e
      have hM0 : 0 < M := by omega
      exact group_lt e jlt (wordsVal_lt _ _ _ _) hb hU
    · rw [vM, vB, wa] at e
      rw [show 4 * (i + 1) = 4 * i + 4 by omega, fios_wordsVal_append s₀.mem B da, show 8 * (4 * i) = 32 * i by omega,
        show 2 ^ (64 * (4 * i)) = 2 ^ (256 * i) by rw [← Nat.mul_assoc],
        show 256 * (i + 1) = 256 * i + 256 by omega, Nat.pow_add]
      exact group_step e jeq
    · rw [r4, h4, VG.Proof.Bignum.PPC64LE.ofNat_sub_one (by omega) (by omega), Nat.sub_sub]
  obtain ⟨j6, j7, j0, jo, jlt, jeq, jk⟩ := hJ₂
  have g : ∀ r ∈ [Reg.r8, .r11], s₂.gpr r = s₀.gpr r := fun r hr => jk.gpr r (by revert r hr; decide)
  have a9 : off B (dA + 8 * w + 16) = off B (dA + 8 * (w + 2)) := by rw [show dA + 8 * w + 16 = dA + 8 * (w + 2) by omega]
  refine WP.mono (WP.keep [.r22, .r9] (Q := fun u => u.gpr .r9 = off B (dA + 8 * (w + 2)) ∧
      u.gpr .r22 = word s₂.mem B (dA + 8 * w + 8) ∧ u.mem = s₂.mem)
    (by
      have e : off B dA + BitVec.ofNat 64 (8 * w) = off B (dA + 8 * w) := off_add _ _ _
      prun [g .r8 (by decide), g .r11 (by decide), h8, h11, shl2_8 w, e, a9,
        (hs.congr jk.wr).ld (show dA + 8 * w + 8 + 8 ≤ Z by omega)])
    (by decide)) fun s ⟨⟨t9, t22, tm⟩, kt⟩ => ?_
  rw [show 4 * (w / 4) = w by omega, show 256 * (w / 4) = 64 * w by omega] at jeq
  refine ⟨⟨by rw [tm]; exact jlt, by rw [tm]; exact jeq, by rw [tm]; exact jo.mono (Nat.le_refl _) (by omega),
    by rw [t22, show dA + 8 * w + 8 = dA + 8 * (w + 1) by omega, jo.word (by omega) (by omega), h22]⟩,
    ⟨fun r hr => ?_, kt.rd.trans jk.rd, kt.wr.trans jk.wr, kt.sp.trans jk.sp, kt.lr.trans jk.lr⟩⟩
  by_cases e7 : r = .r7
  · subst e7; rw [kt.gpr _ (by decide), j7, h7]
  by_cases e9 : r = .r9
  · subst e9; rw [t9, h9]
  have hn : r ∉ groupRegs ++ [.r0] ++ [.r22, .r9] := fun h => by
    rcases rounds4_regs r h with h | h | h
    exacts [hr h, e7 h, e9 h]
  rw [kt.gpr r fun h => hn (List.mem_append_right _ h), jk.gpr r fun h => hn (List.mem_append_left _ h)]

theorem mod4_shift (w : Nat) : BitVec.ofNat 64 (2 * w) <<< 61 >>> 62 = BitVec.ofNat 64 (w % 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  omega

/-- The kernel's rounds (`roundsK`): `rounds4` if `w` is a multiple of 4, else
`rounds8`. -/
theorem roundsK_spec : RoundsSpecW roundsRegs4 roundsK := by
  intro s₀ B Z da dA dB dM w hs h6 h8 h7 h9 h10 h11 h4 hm h22 hw hw' hlay ha hA hB hM daA dBA hz hb
  unfold roundsK
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 (w % 4) ∧ u.mem = s₀.mem)
    (by prun [h11, mod4_shift w]) (by decide)) fun s₁ ⟨⟨a3, am⟩, k₁⟩ => ?_)
  have g : ∀ r ∈ [Reg.r4, .r6, .r7, .r8, .r9, .r10, .r11, .r22], s₁.gpr r = s₀.gpr r := fun r hr =>
    k₁.gpr r (by revert r hr; decide)
  have hs₁ := hs.congr k₁.wr
  have post : ∀ {rr : List Reg} {s : State}, (∀ r ∈ .r3 :: rr, r ∈ roundsRegs4) →
      ((wordsVal s.mem B dA (w + 1) < 2 * wordsVal s₁.mem B dM w ∧
        2 ^ (64 * w) * wordsVal s.mem B dA (w + 1) % wordsVal s₁.mem B dM w =
          wordsVal s₁.mem B da w * wordsVal s₁.mem B dB w % wordsVal s₁.mem B dM w ∧
        Outside B dA (8 * (w + 2)) s₁.mem s.mem ∧ s.gpr .r22 = s₁.gpr .r22) ∧ Keep rr s₁ s) →
      (wordsVal s.mem B dA (w + 1) < 2 * wordsVal s₀.mem B dM w ∧
        2 ^ (64 * w) * wordsVal s.mem B dA (w + 1) % wordsVal s₀.mem B dM w =
          wordsVal s₀.mem B da w * wordsVal s₀.mem B dB w % wordsVal s₀.mem B dM w ∧
        Outside B dA (8 * (w + 2)) s₀.mem s.mem ∧ s.gpr .r22 = s₀.gpr .r22) ∧ Keep roundsRegs4 s₀ s :=
    fun hrr ⟨⟨a, b, c, d⟩, k⟩ => by
      rw [am] at a b c
      exact ⟨⟨a, b, c, d.trans (g _ (by decide))⟩, (k₁.trans k).mono hrr⟩
  refine WP.ite _ (eval_zero_ofNat _ _ (by omega) a3) (fun hz' => ?_) (fun _ => ?_)
  · have h40 : w % 4 = 0 := of_decide_eq_true hz'
    exact WP.mono (rounds4_ok hs₁ (by rw [g _ (by decide), h6]) (by rw [g _ (by decide), h8])
      (by rw [g _ (by decide), h7]) (by rw [g _ (by decide), h9]) (by rw [g _ (by decide), h10])
      (by rw [g _ (by decide), h11]) (by rw [am, g _ (by decide)]; exact hm) (by rw [am, g _ (by decide)]; exact h22)
      (by omega) h40 hw' hlay ha hA hB hM daA dBA (by rw [am]; exact hz) (by rw [am]; exact hb))
      fun s h => post (by decide) h
  · exact WP.mono (rounds8_spec hs₁ (by rw [g _ (by decide), h6]) (by rw [g _ (by decide), h8])
      (by rw [g _ (by decide), h7]) (by rw [g _ (by decide), h9]) (by rw [g _ (by decide), h10])
      (by rw [g _ (by decide), h11]) (by rw [g _ (by decide), h4]) (by rw [am, g _ (by decide)]; exact hm)
      (by rw [am, g _ (by decide)]; exact h22) hw hw' hlay ha hA hB hM daA dBA (by rw [am]; exact hz)
      (by rw [am]; exact hb)) fun s h => post (by decide) h

end VG.Proof.Bignum.PPC64LE
