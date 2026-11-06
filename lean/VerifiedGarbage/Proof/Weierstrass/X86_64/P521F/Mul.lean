module
-- separate module: its proofs build in parallel with those of `Red`, which `Fns` also imports

public import VerifiedGarbage.Proof.Weierstrass.X86_64.P521F.Sqr
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86_64.Friendly
import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontFnX

/-!
# P-521 on x86-64: the product's words (`mulS`)

`mulS` (`Impl/Weierstrass/X86_64/P521Fast.lean`) leaves `[rbx] [rcx]` as
`sqrS` leaves a square (`mulS_ok`): its words `0 … 7` in the temporary area
and `8 … 16` in `xWin 8`. Its rows are s2n-bignum's `bignum_mul_p521`'s:
`b_i [a_0 … a_7]` added along the registers `q w` of consecutive words
(`prodRow0_ok`, `prodRow_ok`, as `sqChain_ok`'s chains), each row's lowest word
stored once final and its register the next row's top one, then the top
words' products (`prodTop_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.P521F

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64.P521F
open VG.Impl.Weierstrass.X86_64.Mont (fnTmp)
open VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono madd_ok movRdx_ok of_setReg of_setFlags adc_carry
  mulx_arith execMulx_eq mulx_ok)
open VG.Proof.Weierstrass.X86_64.Mont (ptrC_of apart_off wordsVal_off)

variable {Z : Nat}

/-! ## Steps -/

/-- `maddStepsM_ok` through any pointer register: `maddStepsMR r`. -/
theorem maddStepsMR_ok {size : Nat} (r : Reg) : ∀ (k : Nat) (ts : List Reg) {s : State} {base : Addr}
    {d : Nat} {c o : Bool}, PtrC s r base size 0 → (∀ t ∈ ts, t ∈ xRegs) → d + 8 * k ≤ size →
    k + 1 ≤ ts.length → FreshX ts → s.cf = some c → s.of = some o →
    WP isa (.block (maddStepsMR r k ts d)) s fun s' => ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
      regsVal s' (ts.take (k + 1)) + 2 ^ (64 * k) * c'.toNat + 2 ^ (64 * (k + 1)) * o'.toNat =
        regsVal s (ts.take (k + 1)) + c.toNat + 2 ^ 64 * o.toNat +
          (s.gpr .rdx).toNat * wordsVal s.mem base d k ∧
      Keeps (.rcx :: .rax :: ts.take (k + 1)) s s'
  | 0, ts, s, _, _, c, o, _, _, _, _, _, hc, ho => by
    show WP isa (.block []) s _
    exact WP.block_nil ⟨c, o, hc, ho, by simp [wordsVal], fun _ _ => rfl, rfl, rfl, rfl⟩
  | _ + 1, [], _, _, _, _, _, _, _, _, hl, _, _, _ => absurd hl (by simp)
  | _ + 1, [_], _, _, _, _, _, _, _, _, hl, _, _, _ => absurd hl (by simp)
  | k + 1, x :: y :: rest, s, base, d, c, o, hs, hts, hd, hl, hf, hc, ho => by
    obtain ⟨hxn, hxa, hxc, hxd, -⟩ := hf.head
    obtain ⟨hyn, hya, hyc, hyd, -⟩ := hf.tail.head
    have hxy : x ≠ y := fun h => hxn (h ▸ List.mem_cons_self ..)
    simp only [List.length_cons] at hl
    rw [maddStepsMR, WP.block_append_iff]
    refine WP.mono (maddM_ok s (v := word s.mem base d) (by exact readSrc_rcR hs (d := d) (by omega_arith))
      (fun _ h => nomatch h) hc ho
      hxc hxa hyc hya hxy) fun s₁ ⟨c₁, o₁, cf₁, of₁, e₁, k₁⟩ => ?_
    have hx := mem_rowRegs_x (hts x (List.mem_cons_self ..))
    have hy := mem_rowRegs_x (hts y (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have hs₁ := hs.of_keeps k₁ (by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> first | decide | exact hx | exact hy)
    refine WP.mono (maddStepsMR_ok r k (y :: rest) hs₁ (fun t ht => hts t (List.mem_cons_of_mem _ ht))
      (d := d + 8) (by omega_arith)
      (by simp only [List.length_cons]; omega_arith) hf.tail cf₁ of₁) fun s₂ ⟨c', o', cf₂, of₂, e₂, k₂⟩ =>
      ⟨c', o', cf₂, of₂, ?_, ?_⟩
    · have hdx : s₁.gpr .rdx = s.gpr .rdx := k₁.1 .rdx (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨by decide, by decide, Ne.symm hxd, Ne.symm hyd⟩)
      have hx₂ : s₂.gpr x = s₁.gpr x := k₂.1 x (by
        simp only [List.mem_cons, not_or]
        exact ⟨hxc, hxa, fun h => hxn (List.mem_of_mem_take h)⟩)
      have hR : regsVal s₁ (rest.take k) = regsVal s (rest.take k) := regsVal_congr fun q hq => k₁.1 q (by
        have hq' := List.mem_of_mem_take hq
        have := hf.2 q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq'))
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨this.2.1, this.1, fun h => hxn (h ▸ List.mem_cons_of_mem _ hq'),
          fun h => hyn (h ▸ hq')⟩)
      rw [k₁.2.1, hdx] at e₂
      simp only [List.take_succ_cons, regsVal, hR] at e₂ ⊢
      simp only [wordsVal]
      rw [hx₂]
      rw [pow64_succ (k + 1), pow64_succ k] at *
      simp only [Nat.mul_assoc] at e₂ ⊢
      rw [Nat.mul_add (s.gpr .rdx).toNat, Nat.mul_left_comm (s.gpr .rdx).toNat (2 ^ 64)]
      omega_arith
    · simp only [List.take_succ_cons] at k₂ ⊢
      exact (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))

/-- `imul d, r`: `d r` modulo `2⁶⁴`. -/
theorem imulR_ok (s : State) (d r : Reg) :
    WP isa (.block [.imul d r]) s fun s' =>
      (s'.gpr d).toNat = (s.gpr d).toNat * (s.gpr r).toNat % 2 ^ 64 ∧ Keeps [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execImul, RegUpd.gpr_setReg_self,
    Option.some.injEq, exists_eq_left']
  refine ⟨imul_toNat' _ _, fun r' hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-! ## Row 0 -/

/-- Row 0: `b_0 [a_0 … a_7]` at the words `0 … 8`, word 0 stored. -/
theorem prodRow0_ok {s : State} {base bA bB : Addr} (hZ : 4096 ≤ Z) (hs : Scr s base Z) (hp : PtrC s .rbx bA 72 0)
    (hq : PtrC s .rsi bB 72 0) (hap : Apart bA 0 72 base fnTmp 72) :
    WP isa (.block prodRow0) s fun s' =>
      (word s'.mem base (T 0)).toNat + 2 ^ 64 * qv s' 1 8 8 = (word s.mem bB 0).toNat * wordsVal s.mem bA 0 8 ∧
      s'.gpr .r14 = 0 ∧ KeepRegs sqRegs s s' ∧ Outside base (T 0) 8 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [prodRow0, List.append_assoc, WP.block_append_iff]
  -- `xor`, `rdx = b₀`, `a₀ b₀`, word 0 stored.
  refine WP.mono (show WP isa (.block [.alu32 .xor .r14 (.reg .r14), .mov .rdx (bsrc 0),
      .mulx (q 1) .rax (asrc 0), .store (sc (T 0)) .rax]) s (fun s₄ =>
      s₄.gpr .r14 = 0 ∧ s₄.cf = some false ∧ s₄.of = some false ∧ s₄.gpr .rdx = word s.mem bB 0 ∧
      (word s₄.mem base (T 0)).toNat + 2 ^ 64 * (s₄.gpr (q 1)).toNat =
        (word s.mem bB 0).toNat * (word s.mem bA 0).toNat ∧
      Outside base (T 0) 8 s.mem s₄.mem ∧ KeepRegs [.rdx, .r14, q 1, .rax] s s₄) by
    rw [show [Instr.alu32 .xor .r14 (.reg .r14), .mov .rdx (bsrc 0), .mulx (q 1) .rax (asrc 0),
      .store (sc (T 0)) .rax] = [.alu32 .xor .r14 (.reg .r14)] ++ ([.mov .rdx (bsrc 0)] ++
      ([.mulx (q 1) .rax (asrc 0)] ++ [.store (sc (T 0)) .rax])) from rfl]
    rw [WP.block_append_iff]
    refine WP.mono (xorZ_ok s .r14) fun s₁ ⟨z₁, cf₁, of₁, k₁⟩ => ?_
    have hq₁ := hq.of_keeps k₁ (by intro t ht; simp at ht; subst ht; decide)
    rw [WP.block_append_iff]
    refine WP.mono (movRdx_ok s₁ (v := word s₁.mem bB 0) (by exact readSrc_rcR hq₁ (d := 0) (by omega)))
      fun s₂ ⟨d₂, cf₂, of₂, k₂⟩ => ?_
    have hp₂ := (hp.of_keeps k₁ (by intro t ht; simp at ht; subst ht; decide)).of_keeps k₂
      (by intro t ht; simp at ht; subst ht; decide)
    rw [WP.block_append_iff]
    refine WP.mono (mulx_ok s₂ (hi := q 1) (lo := .rax) (v := word s₂.mem bA 0)
      (by exact readSrc_rcR hp₂ (d := 0) (by omega)) (fun _ h => nomatch h) (by decide))
      fun s₃ ⟨e₃, cf₃, of₃, k₃⟩ => ?_
    have hs₃ : Scr s₃ base Z := ((hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
    refine WP.mono (storeX_ok hs₃ .rax (d := T 0) (by t_omega)) fun s₄ ⟨m₄, g₄, cf₄, of₄, rd₄, wr₄⟩ => ?_
    have hm : s₃.mem = s.mem := k₃.2.1.trans (k₂.2.1.trans k₁.2.1)
    refine ⟨?_, cf₄.trans (cf₃.trans (cf₂.trans cf₁)), of₄.trans (of₃.trans (of₂.trans of₁)), ?_, ?_, ?_, ?_⟩
    · rw [g₄, k₃.1 _ (by decide), k₂.1 _ (by decide)]; exact z₁
    · rw [g₄, k₃.1 _ (by decide), d₂, k₁.2.1]
    · rw [m₄, word_writeW_self, g₄, e₃, d₂, k₂.2.1, k₁.2.1]
    · rw [m₄, hm]; exact writeW_outside _ _ _ (by t_omega)
    · refine ⟨fun r hr => ?_, by rw [rd₄, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1], by rw [wr₄, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g₄, k₃.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.2.2.1, hr.2.2.2⟩),
        k₂.1 r (by simpa using hr.1), k₁.1 r (by simpa using hr.2.1)]) fun s₄ ⟨z₄, cf₄, of₄, d₄, e₄, O₄, k₄⟩ => ?_
  have hs₄ : Scr s₄ base Z := ⟨by rw [k₄.gpr _ (by decide)]; exact hs.rdi, by rw [k₄.wr]; exact hs.wr, hnw⟩
  have hp₄ := hp.of_keepRegs k₄ (by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> decide)
  -- `b₀ [a₁ … a₇]`.
  rw [WP.block_append_iff]
  refine WP.mono (mulAccs_ok 7 (w := 1) (d := 8) hp₄ (by omega) (by omega) of₄)
    fun s₅ ⟨o₅, of₅, cf₅, e₅, k₅⟩ => ?_
  have hz₅ : s₅.gpr .r14 = 0 := by
    rw [k₅.1 _ (by simp only [List.mem_cons, not_or]; exact ⟨by decide, fun h => by
      obtain ⟨i, -, hi⟩ := mem_qs.mp h; exact (q_ne _).2.2.2.2.2.1 hi⟩)]; exact z₄
  -- The last carry.
  refine WP.mono (adoxS_ok s₅ (x := q 8) (src := .reg .r14) (v := 0) (by simp [readSrc, hz₅])
    (fun _ h => nomatch h) of₅) fun s₆ ⟨o₆, of₆, cf₆, e₆, k₆⟩ => ?_
  have hm₆ : s₆.mem = s₄.mem := k₆.2.1.trans k₅.2.1
  have hW : wordsVal s₄.mem bA 8 7 = wordsVal s.mem bA 8 7 := opnd_eq hap O₄ (by t_omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hW, d₄] at e₅
    rw [hm₆]
    have hb : (word s.mem bB 0).toNat ≤ 2 ^ 64 - 1 := by have := (word s.mem bB 0).isLt; omega
    have ha0 : (word s.mem bA 0).toNat ≤ 2 ^ 64 - 1 := by have := (word s.mem bA 0).isLt; omega
    have hW' : wordsVal s.mem bA 8 7 ≤ 2 ^ (64 * 7) - 1 := by have := wordsVal_lt s.mem bA 8 7; omega
    have hX := Nat.mul_le_mul hb ha0
    have hY := Nat.mul_le_mul hb hW'
    rw [show wordsVal s.mem bA 0 8 = (word s.mem bA 0).toNat + 2 ^ 64 * wordsVal s.mem bA 8 7 from rfl,
      Nat.mul_add, Nat.mul_left_comm]
    generalize (word s.mem bB 0).toNat * (word s.mem bA 0).toNat = X at *
    generalize (word s.mem bB 0).toNat * wordsVal s.mem bA 8 7 = Y at *
    simp only [Bool.toNat_false, Nat.add_zero] at e₅
    rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at e₆
    qv_simp at e₅ ⊢
    rw [k₆.1 (q 1) (by decide), k₆.1 (q 2) (by decide), k₆.1 (q 3) (by decide), k₆.1 (q 4) (by decide),
      k₆.1 (q 5) (by decide), k₆.1 (q 6) (by decide), k₆.1 (q 7) (by decide)]
    have ho₅ := Bool.toNat_le o₅; have ho₆ := Bool.toNat_le o₆
    omega_using [e₄, e₅, e₆, hX, hY, ho₅, ho₆]
  · rw [k₆.1 .r14 (by decide)]; exact hz₅
  · exact (k₄.mono (by decide)).trans (((keepRegs_of_keeps k₅).mono (by decide)).trans
      ((keepRegs_of_keeps k₆).mono (by decide)))
  · rw [hm₆]; exact O₄

/-! ## Rows 1 to 7 -/

theorem q_add8 (w : Nat) : q (w + 8) = q w := by rw [q_mod, q_mod w]; congr 1; omega

/-- Row `i` of `1 … 7` (`prodRow`), as its two chains and the last carry:
what each adds, and the words each leaves alone. -/
theorem prodRow_skel {i : Nat} (h1 : 1 ≤ i) (h7 : i ≤ 7) {s : State} {base bA bB : Addr} (hZ : 4096 ≤ Z)
    (hs : Scr s base Z) (hp : PtrC s .rbx bA 72 0) (hq : PtrC s .rsi bB 72 0) (hap : Apart bA 0 72 base fnTmp 72) :
    WP isa (.block (prodRow i)) s fun s₃ => ∃ (s₁ s₂ : State) (o₁ c₁ o₂ c₂ o₃ : Bool),
      qv s₁ i (7 + 1) (7 + 1) + 2 ^ (64 * 7) * o₁.toNat + 2 ^ (64 * (7 + 1)) * c₁.toNat =
        qv s i (7 + 1) 8 + 0 + 2 ^ 64 * 0 + (word s.mem bB (8 * i)).toNat * wordsVal s.mem bA 0 7 ∧
      qv s₂ (i + 7) (1 + 1) (1 + 1) + 2 ^ (64 * 1) * o₂.toNat + 2 ^ (64 * (1 + 1)) * c₂.toNat =
        qv s₁ (i + 7) (1 + 1) 1 + o₁.toNat + 2 ^ 64 * c₁.toNat +
          (word s.mem bB (8 * i)).toNat * wordsVal s.mem bA 56 1 ∧
      (s₃.gpr (q (i + 8))).toNat + 2 ^ 64 * o₃.toNat = (s₂.gpr (q (i + 8))).toNat + o₂.toNat ∧
      qv s₃ (i + 1) 6 6 = qv s₁ (i + 1) 6 6 ∧ s₃.gpr (q (i + 7)) = s₂.gpr (q (i + 7)) ∧
      word s₃.mem base (T i) = s₁.gpr (q i) ∧ s₃.gpr .r14 = 0 ∧
      KeepRegs sqRegs s s₃ ∧ Outside base (T i) 8 s.mem s₃.mem := by
  have hnw := hs.nowrap
  rw [prodRow, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.alu32 .xor .r14 (.reg .r14), .mov .rdx (bsrc (8 * i))]) s (fun s₀ =>
      s₀.gpr .r14 = 0 ∧ s₀.cf = some false ∧ s₀.of = some false ∧ s₀.gpr .rdx = word s.mem bB (8 * i) ∧
      Keeps [.rdx, .r14] s s₀) by
    rw [show [Instr.alu32 .xor .r14 (.reg .r14), .mov .rdx (bsrc (8 * i))] =
      [.alu32 .xor .r14 (.reg .r14)] ++ [.mov .rdx (bsrc (8 * i))] from rfl, WP.block_append_iff]
    refine WP.mono (xorZ_ok s .r14) fun s₁ ⟨z₁, cf₁, of₁, k₁⟩ => ?_
    have hq₁ := hq.of_keeps k₁ (by decide)
    refine WP.mono (movRdx_ok s₁ (v := word s₁.mem bB (8 * i)) (by exact readSrc_rcR hq₁ (by omega)))
      fun s₂ ⟨d₂, cf₂, of₂, k₂⟩ => ⟨by rw [k₂.1 _ (by decide)]; exact z₁, cf₂.trans cf₁, of₂.trans of₁,
        by rw [d₂, k₁.2.1], (k₁.mono (by decide)).trans (k₂.mono (by decide))⟩) fun s₀ ⟨z₀, cf₀, of₀, d₀, k₀⟩ => ?_
  have hs₀ := hs.of_keeps k₀ (by decide)
  have hp₀ := hp.of_keeps k₀ (by decide)
  -- The first chain: `b_i [a_0 … a_6]`, word `i` stored.
  rw [WP.block_append_iff]
  refine WP.mono (sqChain_ok 7 (w := i) (d := 0) (f := 8) (st := 1)
    hs₀ hZ hp₀ hap (by omega) (by omega) (by omega) z₀ cf₀ of₀) fun s₁ ⟨c₁, o₁, cf₁, of₁, E1, st₁, k₁, O₁⟩ => ?_
  have hs₁ : Scr s₁ base Z := ⟨by
      rw [k₁.gpr _ (by simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, notin_qs fun w => (q_ne w).2.2.2.1⟩)]
      exact hs₀.rdi, by rw [k₁.wr]; exact hs₀.wr, hnw⟩
  have hp₁ := hp₀.of_keepRegs k₁ (qsRows' _ _)
  have hz₁ : s₁.gpr .r14 = 0 := by
    rw [k₁.gpr _ (by simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, fun h => by
      obtain ⟨j, -, hj⟩ := mem_qs.mp h; exact (q_ne _).2.2.2.2.2.1 hj⟩)]; exact z₀
  have O₁' : Outside base (T i) 8 s.mem s₁.mem := by
    rw [← k₀.2.1]; exact O₁.mono (Nat.le_refl _) (by omega)
  -- The second chain: `b_i a_7`, its high half fresh.
  rw [WP.block_append_iff]
  refine WP.mono (sqChain_ok 1 (w := i + 7) (d := 56) (f := 0) (st := 0) hs₁ hZ hp₁ hap (by omega) (by omega)
    (by omega) hz₁ cf₁ of₁) fun s₂ ⟨c₂, o₂, cf₂, of₂, E2, _, k₂, O₂⟩ => ?_
  have hz₂ : s₂.gpr .r14 = 0 := by
    rw [k₂.gpr _ (by simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, fun h => by
      obtain ⟨j, -, hj⟩ := mem_qs.mp h; exact (q_ne _).2.2.2.2.2.1 hj⟩)]; exact hz₁
  -- The last carry.
  refine WP.mono (adoxS_ok s₂ (x := q (i + 8)) (src := .reg .r14) (v := 0) (by simp [readSrc, hz₂])
    (fun _ h => nomatch h) of₂) fun s₃ ⟨o₃, of₃, cf₃, e₃, k₃⟩ => ?_
  -- The memory.
  have hm₂ : s₂.mem = s₁.mem := by
    funext x; exact (O₂ x (by simp only [Nat.zero_min, Nat.mul_zero]; omega))
  have hm₃ : s₃.mem = s₁.mem := k₃.2.1.trans hm₂
  have hT : T i + 8 ≤ 4096 := by rw [T_eq]; omega
  have hW1 : wordsVal s₀.mem bA 0 7 = wordsVal s.mem bA 0 7 := by rw [k₀.2.1]
  have hW2 : wordsVal s₁.mem bA 56 1 = wordsVal s.mem bA 56 1 := opnd_eq hap O₁' hT (by omega)
  -- The registers.
  have hq₀ : ∀ w, s₀.gpr (q w) = s.gpr (q w) := fun w => k₀.1 _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨(q_ne w).2.2.1, (q_ne w).2.2.2.2.2.1⟩)
  have h2 : ∀ w, (∀ j, j < 2 → (w % 8) ≠ ((i + 7 + j) % 8)) → s₂.gpr (q w) = s₁.gpr (q w) := fun w hw =>
    k₂.gpr _ (by
      simp only [List.mem_cons, not_or]
      refine ⟨(q_ne w).1, (q_ne w).2.1, fun h => ?_⟩
      obtain ⟨j, hj, he⟩ := mem_qs.mp h
      exact q_ne_of (hw j hj) he.symm)
  have h3 : ∀ w, w % 8 ≠ (i + 8) % 8 → s₃.gpr (q w) = s₂.gpr (q w) := fun w hw =>
    k₃.1 _ (by simpa using q_ne_of hw)
  refine ⟨s₁, s₂, o₁, c₁, o₂, c₂, o₃, ?_, ?_, e₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hW1, d₀, qv_congr (s := s) (s' := s₀) fun j _ => hq₀ _] at E1
    rw [show max 8 1 = 8 from rfl] at E1
    exact E1
  · rw [hW2, k₁.gpr .rdx (by simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide,
      notin_qs fun w => (q_ne w).2.2.1⟩), d₀] at E2
    rw [show max 0 1 = 1 from rfl] at E2
    exact E2
  · exact qv_congr fun j hj => by rw [h3 _ (by omega), h2 _ (fun j' hj' => by omega)]
  · exact h3 _ (by omega)
  · rw [hm₃]
    have := st₁ 0 (by omega) (by omega)
    rw [Nat.add_zero] at this
    exact this
  · rw [k₃.1 _ (by simpa using (q_ne _).2.2.2.2.2.1.symm)]; exact hz₂
  · refine ⟨fun x hx => ?_, ?_, ?_⟩
    · have hq : ∀ w, x ≠ q w := fun w h => hx (h ▸ q_mem w)
      have hnq : ∀ w n, x ∉ qs w n := fun w n h => by obtain ⟨j, -, hj⟩ := mem_qs.mp h; exact hq _ hj.symm
      have hxa : x ≠ .rax := fun h => hx (h ▸ by decide)
      have hxc : x ≠ .rcx := fun h => hx (h ▸ by decide)
      have hxd : x ≠ .rdx := fun h => hx (h ▸ by decide)
      have hxz : x ≠ .r14 := fun h => hx (h ▸ by decide)
      rw [k₃.1 x (by simpa using hq _), k₂.gpr x (by simp only [List.mem_cons, not_or]; exact ⟨hxa, hxc, hnq _ _⟩),
        k₁.gpr x (by simp only [List.mem_cons, not_or]; exact ⟨hxa, hxc, hnq _ _⟩),
        k₀.1 x (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hxd, hxz⟩)]
    · rw [k₃.2.2.1, k₂.rd, k₁.rd, k₀.2.2.1]
    · rw [k₃.2.2.2, k₂.wr, k₁.wr, k₀.2.2.2]
  · rw [hm₃]; exact O₁'

/-- Row `i` of `1 … 7`: `b_i [a_0 … a_7]` added to the words `i … i + 7` into
the words `i … i + 8`, if the sum fits; word `i` stored. -/
theorem prodRow_ok {i : Nat} (h1 : 1 ≤ i) (h7 : i ≤ 7) {s : State} {base bA bB : Addr} (hZ : 4096 ≤ Z)
    (hs : Scr s base Z) (hp : PtrC s .rbx bA 72 0) (hq : PtrC s .rsi bB 72 0) (hap : Apart bA 0 72 base fnTmp 72)
    (hB : qv s i 8 8 + (word s.mem bB (8 * i)).toNat * wordsVal s.mem bA 0 8 < 2 ^ (64 * 9)) :
    WP isa (.block (prodRow i)) s fun s' =>
      (word s'.mem base (T i)).toNat + 2 ^ 64 * qv s' (i + 1) 8 8 =
        qv s i 8 8 + (word s.mem bB (8 * i)).toNat * wordsVal s.mem bA 0 8 ∧
      s'.gpr .r14 = 0 ∧ KeepRegs sqRegs s s' ∧ Outside base (T i) 8 s.mem s'.mem := by
  refine WP.mono (prodRow_skel h1 h7 hZ hs hp hq hap)
    fun s₃ ⟨s₁, s₂, o₁, c₁, o₂, c₂, o₃, E1, E2, E3, F1, F2, F3, rest⟩ => ⟨?_, rest⟩
  rw [show wordsVal s.mem bA 0 8 = wordsVal s.mem bA 0 7 + (2 ^ 64) ^ 7 * (word s.mem bA 56).toNat from
      wordsVal_succ_last _ _ 0 7] at hB ⊢
  rw [show wordsVal s.mem bA 56 1 = (word s.mem bA 56).toNat by simp [wordsVal]] at E2
  rw [Nat.mul_add, Nat.mul_left_comm] at hB ⊢
  generalize (word s.mem bB (8 * i)).toNat * wordsVal s.mem bA 0 7 = P1 at *
  generalize (word s.mem bB (8 * i)).toNat * (word s.mem bA 56).toNat = P2 at *
  have F2' := congrArg BitVec.toNat F2
  have F3' := congrArg BitVec.toNat F3
  have ho₁ := Bool.toNat_le o₁; have hc₁ := Bool.toNat_le c₁; have ho₂ := Bool.toNat_le o₂
  have hc₂ := Bool.toNat_le c₂; have ho₃ := Bool.toNat_le o₃
  qv_simp at E1 E2 F1 hB ⊢
  simp only [Nat.add_assoc, Nat.reduceAdd] at E1 E2 E3 F1 F2' hB ⊢
  rw [F3']
  omega_using [E1, E2, E3, F1, F2', hB, ho₁, hc₁, ho₂, hc₂, ho₃]

/-! ## The rows together -/

theorem tsum_succ_last (m : Mem) (base : Addr) (n : Nat) :
    tsum m base 0 (n + 1) = tsum m base 0 n + (2 ^ 64) ^ n * (word m base (T n)).toNat := by
  rw [tsum_eq, tsum_eq, wordsVal_succ_last, show T 0 + 8 * n = T n by rw [T_eq, T_eq]]

/-- Rows `0 … j`: `[b_0 … b_j] [a_0 … a_7]`, its words `0 … j` in the
temporary area and `j + 1 … j + 8` in their registers. -/
theorem prodRows_ok {s : State} {base bA bB : Addr} (hZ : 4096 ≤ Z) (hs : Scr s base Z) (hp : PtrC s .rbx bA 72 0)
    (hq : PtrC s .rsi bB 72 0) (hap : Apart bA 0 72 base fnTmp 72) (hbp : Apart bB 0 72 base fnTmp 72) :
    ∀ j ≤ 7, WP isa (.block (prodRow0 ++ (List.range j).flatMap (fun i => prodRow (i + 1)))) s fun s' =>
      tsum s'.mem base 0 (j + 1) + (2 ^ 64) ^ (j + 1) * qv s' (j + 1) 8 8 =
        wordsVal s.mem bB 0 (j + 1) * wordsVal s.mem bA 0 8 ∧
      s'.gpr .r14 = 0 ∧ KeepRegs sqRegs s s' ∧ Outside base (T 0) (8 * (j + 1)) s.mem s'.mem
  | 0, _ => by
    rw [List.range_zero, List.flatMap_nil, List.append_nil]
    refine WP.mono (prodRow0_ok hZ hs hp hq hap) fun s' ⟨e, z, k, O⟩ => ⟨?_, z, k, O⟩
    simp only [tsum, wordsVal, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_one]
    exact e
  | j + 1, hj => by
    have hnw := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ← List.append_assoc, WP.block_append_iff]
    refine WP.mono (prodRows_ok hZ hs hp hq hap hbp j (by omega)) fun s₁ ⟨e₁, z₁, k₁, O₁⟩ => ?_
    have hs₁ : Scr s₁ base Z := hs.of_keepRegs' k₁ (by decide)
    have hp₁ := hp.of_keepRegs k₁ (by decide)
    have hq₁ := hq.of_keepRegs k₁ (by decide)
    have hT₁ : T 0 + 8 * (j + 1) ≤ 4096 := by rw [T_eq]; omega
    have hA₁ : wordsVal s₁.mem bA 0 8 = wordsVal s.mem bA 0 8 := opnd_eq hap O₁ hT₁ (by omega)
    have hb₁ : word s₁.mem bB (8 * (j + 1)) = word s.mem bB (8 * (j + 1)) := opnd_word hbp O₁ hT₁ (by omega)
    -- The bound on the row's sum.
    have hA : wordsVal s.mem bA 0 8 < (2 ^ 64) ^ 8 := by rw [← Nat.pow_mul]; exact wordsVal_lt s.mem bA 0 8
    have hB := wordsVal_lt s.mem bB 0 (j + 1)
    have hqv : qv s₁ (j + 1) 8 8 < (2 ^ 64) ^ 8 := by
      have hB' : wordsVal s.mem bB 0 (j + 1) < (2 ^ 64) ^ (j + 1) := by rw [← Nat.pow_mul]; exact hB
      have hBA := Nat.mul_lt_mul_of_lt_of_le hB' (Nat.le_of_lt hA) (Nat.pow_pos (Nat.two_pow_pos 64))
      have hle := Nat.le_add_left ((2 ^ 64) ^ (j + 1) * qv s₁ (j + 1) 8 8) (tsum s₁.mem base 0 (j + 1))
      rw [e₁] at hle
      exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt hle hBA)
    have hbw : (word s.mem bB (8 * (j + 1))).toNat * wordsVal s.mem bA 0 8 ≤ (2 ^ 64 - 1) * ((2 ^ 64) ^ 8 - 1) :=
      Nat.mul_le_mul (by have := (word s.mem bB (8 * (j + 1))).isLt; omega) (by omega)
    refine WP.mono (prodRow_ok (i := j + 1) (by omega) (by omega) hZ hs₁ hp₁ hq₁ hap (by
      rw [hb₁, hA₁]; omega_using [hqv, hbw])) fun s₂ ⟨e₂, z₂, k₂, O₂⟩ => ⟨?_, z₂, k₁.trans k₂, ?_⟩
    · have ht : tsum s₂.mem base 0 (j + 1) = tsum s₁.mem base 0 (j + 1) := by
        rw [tsum_eq, tsum_eq]
        exact O₂.wordsVal (by rw [T_eq, T_eq]; omega) (by rw [T_eq]; omega)
      rw [hb₁, hA₁] at e₂
      rw [tsum_succ_last, ht, wordsVal_succ_last s.mem bB 0 (j + 1), show 0 + 8 * (j + 1) = 8 * (j + 1) by omega,
        show (2 ^ 64) ^ (j + 1 + 1) = (2 ^ 64) ^ (j + 1) * 2 ^ 64 from Nat.pow_succ ..]
      generalize (2 ^ 64) ^ (j + 1) = Q at *
      generalize qv s₁ (j + 1) 8 8 = V₁ at *
      generalize qv s₂ (j + 1 + 1) 8 8 = V₂ at *
      generalize (word s₂.mem base (T (j + 1))).toNat = W at *
      generalize (word s.mem bB (8 * (j + 1))).toNat = b at *
      generalize wordsVal s.mem bA 0 8 = A at *
      generalize wordsVal s.mem bB 0 (j + 1) = B at *
      generalize tsum s₁.mem base 0 (j + 1) = t at *
      grind
    · rw [show 8 * (j + 1 + 1) = 8 * (j + 1) + 8 by omega]
      exact (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by rw [T_eq, T_eq]; omega) (by rw [T_eq, T_eq]; omega))

/-! ## The top words -/

/-- `prodTop`: `a_8 b_8` at word 16 and `b_8 [a_0 … a_7]`, `a_8 [b_0 … b_7]` at
word 8, added to the words `8 … 15`, into `xWin 8` (words `8 … 16`), if that
fits in nine words. -/
theorem prodTop_ok {s : State} {bA bB : Addr} (hp : PtrC s .rbx bA 72 0) (hq : PtrC s .rsi bB 72 0)
    (ha8 : (word s.mem bA 64).toNat < 2 ^ 9) (hb8 : (word s.mem bB 64).toNat < 2 ^ 9)
    (hB : qv s 8 8 8 + (2 ^ 64) ^ 8 * ((word s.mem bA 64).toNat * (word s.mem bB 64).toNat) +
      (word s.mem bB 64).toNat * wordsVal s.mem bA 0 8 + (word s.mem bA 64).toNat * wordsVal s.mem bB 0 8 <
        (2 ^ 64) ^ 9) :
    WP isa (.block prodTop) s fun s' =>
      regsVal s' (xWin 8) = qv s 8 8 8 + (2 ^ 64) ^ 8 * ((word s.mem bA 64).toNat * (word s.mem bB 64).toNat) +
        (word s.mem bB 64).toNat * wordsVal s.mem bA 0 8 + (word s.mem bA 64).toNat * wordsVal s.mem bB 0 8 ∧
      Keeps (.rcx :: .rax :: .rdx :: xWin 8) s s' := by
  rw [prodTop, ← xWin8]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  -- `rdx = b₈`, `r14 = a₈ b₈`, the carries clear.
  refine WP.mono (show WP isa (.block [.mov .rdx (bsrc 64), .mov .r14 (asrc 64), .imul .r14 .rdx,
      .alu32 .xor .rax (.reg .rax)]) s (fun s₄ =>
        (s₄.gpr .r14).toNat = (word s.mem bA 64).toNat * (word s.mem bB 64).toNat ∧
        s₄.gpr .rdx = word s.mem bB 64 ∧ s₄.cf = some false ∧ s₄.of = some false ∧
        Keeps [.rdx, .r14, .rax] s s₄) by
    rw [show [Instr.mov .rdx (bsrc 64), .mov .r14 (asrc 64), .imul .r14 .rdx, .alu32 .xor .rax (.reg .rax)] =
      [.mov .rdx (bsrc 64)] ++ ([.mov .r14 (asrc 64)] ++ ([.imul .r14 .rdx] ++ [.alu32 .xor .rax (.reg .rax)])) from rfl,
      WP.block_append_iff]
    refine WP.mono (movRdx_ok s (v := word s.mem bB 64) (by exact readSrc_rcR hq (by omega)))
      fun s₁ ⟨d₁, _, _, k₁⟩ => ?_
    have hp₁ := hp.of_keeps k₁ (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (movR_ok s₁ .r14 (v := word s₁.mem bA 64) (by exact readSrc_rcR hp₁ (by omega)))
      fun s₂ ⟨r₂, _, _, k₂⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (imulR_ok s₂ .r14 .rdx) fun s₃ ⟨r₃, k₃⟩ => ?_
    refine WP.mono (xorZ_ok s₃ .rax) fun s₄ ⟨_, cf₄, of₄, k₄⟩ => ⟨?_, ?_, cf₄, of₄, ?_⟩
    · rw [k₄.1 _ (by decide), r₃, r₂, k₂.1 _ (by decide), d₁, k₁.2.1]
      have := Nat.mul_lt_mul'' ha8 hb8
      exact Nat.mod_eq_of_lt (by omega)
    · rw [k₄.1 _ (by decide), k₃.1 _ (by decide), k₂.1 _ (by decide), d₁]
    · exact ((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans ((k₃.mono (by decide)).trans
        (k₄.mono (by decide)))) fun s₄ ⟨r₄, d₄, cf₄, of₄, k₄⟩ => ?_
  have hp₄ := hp.of_keeps k₄ (by decide)
  have hq₄ := hq.of_keeps k₄ (by decide)
  -- `b₈ [a₀ … a₇]`.
  rw [WP.block_append_iff]
  refine WP.mono (maddStepsM_ok 8 (xWin 8) hp₄ (xWin_sub 8) (d := 0) (by omega) (by simp [xWin]) (xWin_fresh 8)
    cf₄ of₄) fun s₅ ⟨c₅, o₅, cf₅, of₅, e₅, k₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adc0_ok s₅ .r14 cf₅) fun s₆ ⟨c₆, cf₆, e₆, k₆⟩ => ?_
  -- `rdx = a₈`, the carries clear.
  have hp₆ := (hp₄.of_keeps k₅ (by rw [xWin8]; decide)).of_keeps k₆ (by decide)
  have hq₆ := (hq₄.of_keeps k₅ (by rw [xWin8]; decide)).of_keeps k₆ (by decide)
  rw [WP.block_append_iff, show [Instr.mov .rdx (asrc 64), .alu32 .xor .rax (.reg .rax)] =
    [.mov .rdx (asrc 64)] ++ [.alu32 .xor .rax (.reg .rax)] from rfl, WP.block_append_iff]
  refine WP.mono (movRdx_ok s₆ (v := word s₆.mem bA 64) (by exact readSrc_rcR hp₆ (by omega)))
    fun s₇ ⟨d₇, _, _, k₇⟩ => ?_
  refine WP.mono (xorZ_ok s₇ .rax) fun s₈ ⟨_, cf₈, of₈, k₈⟩ => ?_
  have hq₈ := (hq₆.of_keeps k₇ (by decide)).of_keeps k₈ (by decide)
  -- `a₈ [b₀ … b₇]`.
  rw [WP.block_append_iff]
  refine WP.mono (maddStepsMR_ok .rsi 8 (xWin 8) hq₈ (xWin_sub 8) (d := 0) (by omega) (by simp [xWin])
    (xWin_fresh 8) cf₈ of₈) fun s₉ ⟨c₉, o₉, cf₉, of₉, e₉, k₉⟩ => ?_
  refine WP.mono (adc0_ok s₉ .r14 cf₉) fun s₁₀ ⟨c₁₀, cf₁₀, e₁₀, k₁₀⟩ => ⟨?_, ?_⟩
  · have hm₆ : s₆.mem = s.mem := k₆.2.1.trans (k₅.2.1.trans k₄.2.1)
    have hm₈ : s₈.mem = s.mem := k₈.2.1.trans (k₇.2.1.trans hm₆)
    rw [List.take_of_length_le (by simp [xWin]), k₄.2.1, d₄] at e₅
    rw [List.take_of_length_le (by simp [xWin]), hm₈] at e₉
    rw [k₈.1 _ (by decide), d₇, hm₆] at e₉
    rw [xWin8] at e₅ e₉ ⊢
    obtain ⟨q8, q9, q10, q11, q12, q13, q14, q15⟩ := q_lit
    qv_simp at hB ⊢
    rw [q8, q9, q10, q11, q12, q13, q14, q15] at hB ⊢
    simp only [regsVal, Nat.mul_zero, Nat.add_zero, Bool.toNat_false] at e₅ e₉ ⊢
    -- The registers between the steps.
    rw [k₁₀.1 .r15 (by decide), k₁₀.1 .rbp (by decide), k₁₀.1 .r8 (by decide), k₁₀.1 .r9 (by decide),
      k₁₀.1 .r10 (by decide), k₁₀.1 .r11 (by decide), k₁₀.1 .r12 (by decide), k₁₀.1 .r13 (by decide)]
    rw [k₈.1 .r15 (by decide), k₈.1 .rbp (by decide), k₈.1 .r8 (by decide), k₈.1 .r9 (by decide),
      k₈.1 .r10 (by decide), k₈.1 .r11 (by decide), k₈.1 .r12 (by decide), k₈.1 .r13 (by decide),
      k₈.1 .r14 (by decide), k₇.1 .r15 (by decide), k₇.1 .rbp (by decide), k₇.1 .r8 (by decide),
      k₇.1 .r9 (by decide), k₇.1 .r10 (by decide), k₇.1 .r11 (by decide), k₇.1 .r12 (by decide),
      k₇.1 .r13 (by decide), k₇.1 .r14 (by decide)] at e₉
    rw [k₆.1 .r15 (by decide), k₆.1 .rbp (by decide), k₆.1 .r8 (by decide), k₆.1 .r9 (by decide),
      k₆.1 .r10 (by decide), k₆.1 .r11 (by decide), k₆.1 .r12 (by decide), k₆.1 .r13 (by decide)] at e₉
    rw [k₄.1 .r15 (by decide), k₄.1 .rbp (by decide), k₄.1 .r8 (by decide), k₄.1 .r9 (by decide),
      k₄.1 .r10 (by decide), k₄.1 .r11 (by decide), k₄.1 .r12 (by decide), k₄.1 .r13 (by decide), r₄] at e₅
    have hc₅ := Bool.toNat_le c₅; have ho₅ := Bool.toNat_le o₅; have hc₆ := Bool.toNat_le c₆
    have hc₉ := Bool.toNat_le c₉; have ho₉ := Bool.toNat_le o₉; have hc₁₀ := Bool.toNat_le c₁₀
    omega_using [e₅, e₆, e₉, e₁₀, hB, hc₅, ho₅, hc₆, hc₉, ho₉, hc₁₀]
  · refine (k₄.mono ?_).trans ((k₅.mono ?_).trans ((k₆.mono ?_).trans ((k₇.mono ?_).trans ((k₈.mono ?_).trans
      ((k₉.mono ?_).trans (k₁₀.mono ?_)))))) <;> rw [xWin8] <;> decide

/-! ## The product -/

/-- A block that writes no vector register keeps them. -/
private theorem runBlock_xmm : ∀ (is : List Instr) {s s' : State}, is.all (fun i => !KeepReg.writesVec i) = true →
    runBlock isa is s = some s' → s'.xmm = s.xmm
  | [], s, s', _, h => by rw [runBlock_nil, Option.some.injEq] at h; rw [h]
  | i :: is, s, s', hw, h => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hw
    rw [runBlock_cons] at h
    cases he : exec i s with
    | none => rw [he, runStep, Option.bind_none] at h; cases h
    | some t =>
      rw [he, runStep_some] at h
      rw [runBlock_xmm is hw.2 h, KeepReg.exec_xmm hw.1 he]

private theorem WP.keep_xmm {is : List Instr} (hw : is.all (fun i => !KeepReg.writesVec i) = true) {s : State}
    {Q : State → Prop} (h : WP isa (.block is) s Q) : WP isa (.block is) s fun s' => Q s' ∧ s'.xmm = s.xmm := by
  obtain ⟨s', hr, hq⟩ := WP.runBlock_of h
  exact WP.of_runBlock ⟨s', hr, hq, runBlock_xmm is hw hr⟩

/-- `mulRows`' first two instructions: the output's offset into `xmm13`, `rsi = rcx`. -/
theorem mulPro_ok (s : State) :
    WP isa (.block [.xop (.movq .xmm13 .rsi), .mov .rsi (.reg .rcx)]) s fun s' =>
      s'.gpr .rsi = s.gpr .rcx ∧ (∀ r, r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ (s'.xmm .xmm13).extractLsb' 0 64 = s.gpr .rsi := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, readSrc, Option.map_some]
  refine ⟨_, rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, ?_⟩
  · simp only [RegUpd.gpr_setReg_self, RegUpd.gpr_setXmm]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setXmm]
  · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setXmm_self, BitVec.extractLsb'_append_eq_right]

/-- `mulRows`' last instruction: `rsi` from `xmm13`. -/
theorem mulEpi_ok (s : State) :
    WP isa (.block [.movqR .rsi .xmm13]) s fun s' =>
      s'.gpr .rsi = (s.xmm .xmm13).extractLsb' 0 64 ∧ (∀ r, r ≠ .rsi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, exec]
  exact ⟨_, rfl, RegUpd.gpr_setReg_self .., fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩

theorem wordsVal9' (m : Mem) (b : Addr) :
    wordsVal m b 0 9 = wordsVal m b 0 8 + (2 ^ 64) ^ 8 * (word m b 64).toNat := wordsVal_succ_last m b 0 8

/-- `mulS`: `[a] [b]` with its words `0 … 7` in the temporary area and `8 … 16` in `xWin 8`,
for `rbx = ws + a` and `rcx = ws + b`, as `sqrS_ok` leaves a square. -/
theorem mulS_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} (hs : Scr s base Z) {a b : Nat}
    (hbx : s.gpr .rbx = off base a) (hcx : s.gpr .rcx = off base b) (ha : a + 72 ≤ 3520) (hb : b + 72 ≤ 3520)
    (ha8 : (word s.mem (off base a) 64).toNat < 2 ^ 9) (hb8 : (word s.mem (off base b) 64).toNat < 2 ^ 9) :
    WP isa (.block mulS) s fun s' =>
      tsum s'.mem base 0 8 + (2 ^ 64) ^ 8 * regsVal s' (xWin 8) = wordsVal s.mem base a 9 * wordsVal s.mem base b 9 ∧
      KeepRegs sqRegs s s' ∧ Outside base (T 0) 64 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [show mulS = [.xop (.movq .xmm13 .rsi), .mov .rsi (.reg .rcx)] ++
      (((prodRow0 ++ (List.range 7).flatMap (fun i => prodRow (i + 1))) ++ prodTop) ++ [.movqR .rsi .xmm13]) by
    simp only [mulS, List.append_assoc], WP.block_append_iff]
  refine WP.mono (mulPro_ok s) fun s₁ ⟨v₁, k₁, m₁, rd₁, wr₁, x₁⟩ => ?_
  have hs₁ : Scr s₁ base Z := ⟨by rw [k₁ _ (by decide)]; exact hs.rdi, wr₁ ▸ hs.wr, hnw⟩
  have hp₁ := ptrC_of hs₁ (show s₁.gpr .rbx = off base a by rw [k₁ _ (by decide), hbx]) (show a + 72 ≤ Z by omega)
    (by decide) (Or.inr (Or.inr rfl))
  have hq₁ := ptrC_of hs₁ (show s₁.gpr .rsi = off base b by rw [v₁, hcx]) (show b + 72 ≤ Z by omega)
    (by decide) (Or.inr (Or.inl rfl))
  have hap : Apart (off base a) 0 72 base fnTmp 72 := apart_off base (by simp only [fnTmp]; omega) (by omega)
  have hbp : Apart (off base b) 0 72 base fnTmp 72 := apart_off base (by simp only [fnTmp]; omega) (by omega)
  -- The rows and the top words, which write no vector register.
  have hmid : WP isa (.block ((prodRow0 ++ (List.range 7).flatMap (fun i => prodRow (i + 1))) ++ prodTop)) s₁
      fun s' => tsum s'.mem base 0 8 + (2 ^ 64) ^ 8 * regsVal s' (xWin 8) =
          wordsVal s₁.mem (off base a) 0 9 * wordsVal s₁.mem (off base b) 0 9 ∧
        KeepRegs sqRegs s₁ s' ∧ Outside base (T 0) 64 s₁.mem s'.mem := by
    rw [WP.block_append_iff]
    refine WP.mono (prodRows_ok hZ hs₁ hp₁ hq₁ hap hbp 7 (by omega)) fun s₂ ⟨e₂, _, k₂, O₂⟩ => ?_
    have hp₂ := hp₁.of_keepRegs k₂ (by decide)
    have hq₂ := hq₁.of_keepRegs k₂ (by decide)
    have hT : T 0 + 8 * (7 + 1) ≤ 4096 := by rw [T_eq]; omega
    have hwa : ∀ d, d + 8 ≤ 72 → word s₂.mem (off base a) d = word s₁.mem (off base a) d :=
      fun d h => opnd_word hap O₂ hT h
    have hwb : ∀ d, d + 8 ≤ 72 → word s₂.mem (off base b) d = word s₁.mem (off base b) d :=
      fun d h => opnd_word hbp O₂ hT h
    have hWa : wordsVal s₂.mem (off base a) 0 8 = wordsVal s₁.mem (off base a) 0 8 := opnd_eq hap O₂ hT (by omega)
    have hWb : wordsVal s₂.mem (off base b) 0 8 = wordsVal s₁.mem (off base b) 0 8 := opnd_eq hbp O₂ hT (by omega)
    have ha8₁ : (word s₁.mem (off base a) 64).toNat < 2 ^ 9 := by rw [m₁]; exact ha8
    have hb8₁ : (word s₁.mem (off base b) 64).toNat < 2 ^ 9 := by rw [m₁]; exact hb8
    have ha8₂ : (word s₂.mem (off base a) 64).toNat < 2 ^ 9 := by rw [hwa _ (by omega)]; exact ha8₁
    have hb8₂ : (word s₂.mem (off base b) 64).toNat < 2 ^ 9 := by rw [hwb _ (by omega)]; exact hb8₁
    -- The bound on the top words' sum.
    have hA : wordsVal s₁.mem (off base a) 0 8 < (2 ^ 64) ^ 8 := by
      rw [← Nat.pow_mul]; exact wordsVal_lt _ _ 0 8
    have hB : wordsVal s₁.mem (off base b) 0 8 < (2 ^ 64) ^ 8 := by
      rw [← Nat.pow_mul]; exact wordsVal_lt _ _ 0 8
    have hqv : qv s₂ 8 8 8 < (2 ^ 64) ^ 8 := by
      have hBA := Nat.mul_lt_mul_of_lt_of_le hB (Nat.le_of_lt hA) (Nat.pow_pos (Nat.two_pow_pos 64))
      have hle := Nat.le_add_left ((2 ^ 64) ^ (7 + 1) * qv s₂ (7 + 1) 8 8) (tsum s₂.mem base 0 (7 + 1))
      rw [e₂] at hle
      exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt hle hBA)
    have hab := Nat.mul_le_mul (Nat.le_sub_one_of_lt ha8₁) (Nat.le_sub_one_of_lt hb8₁)
    have hbA := Nat.mul_le_mul (Nat.le_sub_one_of_lt hb8₁) (Nat.le_sub_one_of_lt hA)
    have haB := Nat.mul_le_mul (Nat.le_sub_one_of_lt ha8₁) (Nat.le_sub_one_of_lt hB)
    refine WP.mono (prodTop_ok hp₂ hq₂ ha8₂ hb8₂ (by
      rw [hwa _ (by omega), hwb _ (by omega), hWa, hWb]
      omega_using [hqv, hab, hbA, haB])) fun s₃ ⟨Tp, k₃⟩ => ⟨?_, ?_, ?_⟩
    · rw [Tp, k₃.2.1, hwa _ (by omega), hwb _ (by omega), hWa, hWb, wordsVal9', wordsVal9']
      generalize (2 ^ 64) ^ 8 = Q at *
      generalize qv s₂ 8 8 8 = V at *
      generalize tsum s₂.mem base 0 (7 + 1) = t at *
      generalize wordsVal s₁.mem (off base a) 0 8 = A at *
      generalize wordsVal s₁.mem (off base b) 0 8 = B at *
      generalize (word s₁.mem (off base a) 64).toNat = a8 at *
      generalize (word s₁.mem (off base b) 64).toNat = b8 at *
      grind
    · exact k₂.trans ((keepRegs_of_keeps k₃).mono (by rw [xWin8]; decide))
    · rw [k₃.2.1]; exact O₂
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep_xmm (by
    simp only [List.all_append, Bool.and_eq_true]
    refine ⟨⟨by decide, by rw [List.all_flatMap, List.all_eq_true]; decide⟩, by decide⟩) hmid)
    fun s₂ ⟨⟨e₂, k₂, O₂⟩, x₂⟩ => ?_
  refine WP.mono (mulEpi_ok s₂) fun s₃ ⟨v₃, k₃, m₃, rd₃, wr₃⟩ => ⟨?_, ?_, ?_⟩
  · have hx : regsVal s₃ (xWin 8) = regsVal s₂ (xWin 8) := regsVal_congr fun r hr => k₃ r (by
      rw [xWin8] at hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    rw [m₃, hx, e₂, m₁, wordsVal_off, wordsVal_off, Nat.add_zero, Nat.add_zero]
  · refine ⟨fun r hr => ?_, by rw [rd₃, k₂.rd, rd₁], by rw [wr₃, k₂.wr, wr₁]⟩
    by_cases hrs : r = .rsi
    · subst hrs; rw [v₃, x₂, x₁]
    · rw [k₃ r hrs, k₂.gpr r hr, k₁ r hrs]
  · rw [m₃, ← m₁]; exact O₂

end VG.Proof.Weierstrass.X86_64.P521F
