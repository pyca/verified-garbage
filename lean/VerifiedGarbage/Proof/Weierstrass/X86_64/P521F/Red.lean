module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.P521F.Sqr
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-!
# P-521 on x86-64: the reduction by shifts (`redS`)

For `P < 2¹⁰⁴²` with its words `0 … 8` in the temporary area and `9 … 16`
in `xAcc 9 … 16`, `redS` leaves
`Q = P_hi + (P₀ mod 2⁵⁵) 2⁴⁶⁶ + ⌊P_lo / 2⁵⁵⌋` (plus one if asked) in
`xWin 9` (`redS_ok`), `P_lo` the low nine words and `P_hi` the others: as
`2⁵²¹ ≡ 1 (mod p)`, `2⁵⁷⁶ Q ≡ P` (`redQ_mod`), and `Q < 2p` (`redQ_lt`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.P521F

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64.P521F
open VG.Impl.Weierstrass.X86_64.Mont (fnTmp)
open VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono of_setReg of_setFlags adc_carry)

variable {Z : Nat}

/-! ## Steps -/

theorem shlS_ok (s : State) (t : Reg) {n : Nat} (hn : 1 ≤ n ∧ n ≤ 63) :
    WP isa (.block [.shift .shl t n]) s fun s' =>
      (s'.gpr t).toNat = (s.gpr t).toNat * 2 ^ n % 2 ^ 64 ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execShift, hn, and_self, ite_true,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq], fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

theorem shrS_ok (s : State) (t : Reg) {n : Nat} (hn : 1 ≤ n ∧ n ≤ 63) :
    WP isa (.block [.shift .shr t n]) s fun s' =>
      (s'.gpr t).toNat = (s.gpr t).toNat / 2 ^ n ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execShift, hn, and_self, ite_true,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow], fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `and t32, 511`. -/
theorem and511w_ok (s : State) (t : Reg) :
    WP isa (.block [.alu32 .and t (.imm 511)]) s fun s' =>
      (s'.gpr t).toNat = (s.gpr t).toNat % 512 ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, Option.bind_some,
    State.setReg32, RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth,
      show (511 : BitVec 32).toNat = 2 ^ 9 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- Disjoint bits: `or` adds. -/
theorem or_disj (a b : BitVec 64) {k : Nat} (ha : a.toNat % 2 ^ k = 0) (hb : b.toNat < 2 ^ k) :
    (a ||| b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_or]
  have : a.toNat = 2 ^ k * (a.toNat / 2 ^ k) := by
    have := Nat.div_add_mod a.toNat (2 ^ k); omega
  rw [this, ← Nat.two_pow_add_eq_or_of_lt hb]

/-- `or t, r` for `t < 2ᵏ` and `r` a multiple of `2ᵏ`. -/
theorem orR_ok (s : State) (t r : Reg) {k : Nat} (ht : (s.gpr t).toNat < 2 ^ k)
    (hr : (s.gpr r).toNat % 2 ^ k = 0) :
    WP isa (.block [.alu .or t (.reg r)]) s fun s' =>
      (s'.gpr t).toNat = (s.gpr t).toNat + (s.gpr r).toNat ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r' hr' => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.or_comm, or_disj _ _ hr ht]; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr', RegUpd.gpr_arithFlags]

/-- `shld d, r, n`: `d 2ⁿ mod 2⁶⁴` and `r`'s top `n` bits. -/
theorem shldS_ok (s : State) (d r : Reg) {n : Nat} (hn : 1 ≤ n ∧ n ≤ 63) :
    WP isa (.block [.shld d r n]) s fun s' =>
      (s'.gpr d).toNat = (s.gpr d).toNat * 2 ^ n % 2 ^ 64 + (s.gpr r).toNat / 2 ^ (64 - n) ∧
        Keeps [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execShld, hn, and_self, ite_true,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r' hr' => ?_, rfl, rfl, rfl⟩
  · have h1 : ((s.gpr d) <<< n).toNat % 2 ^ n = 0 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
      exact Nat.mul_mod_left _ _
    have h2 : ((s.gpr r) >>> (64 - n)).toNat < 2 ^ n := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have := (s.gpr r).isLt
      exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add, show 64 - n + n = 64 by omega]; exact this)
    rw [or_disj _ _ h1 h2, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr', RegUpd.gpr_setFlags]

/-- `cmp t, -1` for `t = 0`: CF set, OF clear. -/
theorem cmpM1_ok (s : State) (t : Reg) (ht : s.gpr t = 0) :
    WP isa (.block [.alu .cmp t (.imm (-1))]) s fun s' =>
      s'.cf = some true ∧ s'.of = some false ∧ Keeps [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left', arithFlags, State.setFlags, ht]
  exact ⟨by decide, by decide, fun _ _ => rfl, rfl, rfl, rfl⟩

/-- `adc x, src`. -/
theorem adcS_ok (s : State) (x : Reg) {src : Src} {v : BitVec 64} (hsrc : readSrc s src = some v)
    {c : Bool} (hc : s.cf = some c) :
    WP isa (.block [.alu .adc x src]) s fun s' => ∃ c', s'.cf = some c' ∧
      (s'.gpr x).toNat + 2 ^ 64 * c'.toNat = (s.gpr x).toNat + v.toNat + c.toNat ∧ Keeps [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, hsrc, Option.bind_some,
    Option.map_some, hc, RegUpd.gpr_setReg_self, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
    Option.some.injEq, exists_eq_left']
  refine ⟨adc_carry _ _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]


/-! ## The parts of `redS` -/

/-- `(P₀ mod 2⁵⁵) 2⁴⁶⁶` into words 16 (`r14 < 2¹⁸`) and 17 (`r15`), `rax = P₈`. -/
theorem redPre_ok {s : State} {base : Addr} (hZ : 4096 ≤ Z) (hs : Scr s base Z) (h14 : (s.gpr .r14).toNat < 2 ^ 18) :
    WP isa (.block [.mov .rcx (.mem (sc (T 0))), .shift .shl .rcx 18, .alu .or .r14 (.reg .rcx),
      .mov .r15 (.mem (sc (T 0))), .shift .shr .r15 46, .alu32 .and .r15 (.imm 511), .mov .rax (.mem (sc (T 8)))]) s
      fun s' => s'.gpr .rax = word s.mem base (T 8) ∧
        (s'.gpr .r14).toNat = (s.gpr .r14).toNat + (word s.mem base (T 0)).toNat % 2 ^ 46 * 2 ^ 18 ∧
        (s'.gpr .r15).toNat = (word s.mem base (T 0)).toNat / 2 ^ 46 % 512 ∧
        Keeps [.rax, .rcx, .r14, .r15] s s' := by
  rw [show [Instr.mov .rcx (.mem (sc (T 0))), .shift .shl .rcx 18, .alu .or .r14 (.reg .rcx),
      .mov .r15 (.mem (sc (T 0))), .shift .shr .r15 46, .alu32 .and .r15 (.imm 511), .mov .rax (.mem (sc (T 8)))] =
      [.mov .rcx (.mem (sc (T 0)))] ++ ([.shift .shl .rcx 18] ++ ([.alu .or .r14 (.reg .rcx)] ++
      ([.mov .r15 (.mem (sc (T 0)))] ++ ([.shift .shr .r15 46] ++ ([.alu32 .and .r15 (.imm 511)] ++
      [.mov .rax (.mem (sc (T 8)))]))))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (movR_ok s .rcx (sc_ok hZ hs (d := T 0) (by t_omega))) fun s₁ ⟨r₁, _, _, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (shlS_ok s₁ .rcx (n := 18) (by omega)) fun s₂ ⟨r₂, k₂⟩ => ?_
  have h14₂ : (s₂.gpr .r14).toNat < 2 ^ 18 := by
    rw [k₂.1 _ (by decide), k₁.1 _ (by decide)]; exact h14
  have hr2 : (s₂.gpr .rcx).toNat % 2 ^ 18 = 0 := by
    rw [r₂, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]; exact Nat.mul_mod_left _ _
  rw [WP.block_append_iff]
  refine WP.mono (orR_ok s₂ .r14 .rcx h14₂ hr2) fun s₃ ⟨r₃, k₃⟩ => ?_
  have hm₃ : s₃.mem = s.mem := k₃.2.1.trans (k₂.2.1.trans k₁.2.1)
  have hs₃ : Scr s₃ base Z := ((hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movR_ok s₃ .r15 (sc_ok hZ hs₃ (d := T 0) (by t_omega))) fun s₄ ⟨r₄, _, _, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (shrS_ok s₄ .r15 (n := 46) (by omega)) fun s₅ ⟨r₅, k₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (and511w_ok s₅ .r15) fun s₆ ⟨r₆, k₆⟩ => ?_
  have hm₆ : s₆.mem = s.mem := k₆.2.1.trans (k₅.2.1.trans (k₄.2.1.trans hm₃))
  have hs₆ : Scr s₆ base Z := ((hs₃.of_keeps k₄ (by decide)).of_keeps k₅ (by decide)).of_keeps k₆ (by decide)
  refine WP.mono (movR_ok s₆ .rax (sc_ok hZ hs₆ (d := T 8) (by t_omega))) fun s₇ ⟨r₇, _, _, k₇⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [r₇, hm₆]
  · rw [k₇.1 _ (by decide), k₆.1 _ (by decide), k₅.1 _ (by decide), k₄.1 _ (by decide), r₃, r₂, r₁,
      k₂.1 _ (by decide), k₁.1 _ (by decide)]
    have := (word s.mem base (T 0)).isLt
    omega
  · rw [k₇.1 _ (by decide), r₆, r₅, r₄, hm₃]
  · refine (((k₁.mono ?_).trans (k₂.mono ?_)).trans ((k₃.mono ?_).trans (k₄.mono ?_))).trans
      (((k₅.mono ?_).trans (k₆.mono ?_)).trans (k₇.mono ?_)) <;> decide

/-- `redPair j`, from `rax = x`: words `2j + 1` and `2j` replaced by their
steps of `P_lo >> 55` (word `2j + 2` being `x`), `rax` word `2j`. -/
theorem redPair_ok {s : State} {base : Addr} (hZ : 4096 ≤ Z) (hs : Scr s base Z) {j : Nat} (hj : j < 4)
    {x : BitVec 64} (hx : s.gpr .rax = x) :
    WP isa (.block (redPair j)) s fun s' =>
      (word s'.mem base (T (2 * j + 1))).toNat =
        512 * (x.toNat % 2 ^ 55) + (word s.mem base (T (2 * j + 1))).toNat / 2 ^ 55 ∧
      (word s'.mem base (T (2 * j))).toNat =
        512 * ((word s.mem base (T (2 * j + 1))).toNat % 2 ^ 55) + (word s.mem base (T (2 * j))).toNat / 2 ^ 55 ∧
      s'.gpr .rax = word s.mem base (T (2 * j)) ∧ KeepRegs [.rax, .rcx] s s' ∧
      Outside base (T (2 * j)) 16 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [redPair, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movR_ok s .rcx (sc_ok hZ hs (d := T (2 * j + 1)) (by rw [T_eq]; omega)))
    fun s₁ ⟨r₁, _, _, k₁⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (shldS_ok s₁ .rax .rcx (n := 9) (by omega)) fun s₂ ⟨r₂, k₂⟩ => ?_
  have hs₂ : Scr s₂ base Z := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  have hm₂ : s₂.mem = s.mem := k₂.2.1.trans k₁.2.1
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (storeX_ok hs₂ .rax (d := T (2 * j + 1)) (by rw [T_eq]; omega))
    fun s₃ ⟨m₃, g₃, _, _, rd₃, wr₃⟩ => ?_
  have hs₃ : Scr s₃ base Z := ⟨by rw [g₃]; exact hs₂.rdi, wr₃ ▸ hs₂.wr, hnw⟩
  have O₃ : Outside base (T (2 * j + 1)) 8 s.mem s₃.mem := by
    rw [m₃, hm₂]; exact writeW_outside _ _ _ (by rw [T_eq]; omega)
  have hw0 : word s₃.mem base (T (2 * j)) = word s.mem base (T (2 * j)) :=
    O₃.word (by rw [T_eq, T_eq]; omega) (by rw [T_eq]; omega)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movR_ok s₃ .rax (sc_ok hZ hs₃ (d := T (2 * j)) (by rw [T_eq]; omega)))
    fun s₄ ⟨r₄, _, _, k₄⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (shldS_ok s₄ .rcx .rax (n := 9) (by omega)) fun s₅ ⟨r₅, k₅⟩ => ?_
  have hs₅ : Scr s₅ base Z := (hs₃.of_keeps k₄ (by decide)).of_keeps k₅ (by decide)
  have hm₅ : s₅.mem = s₃.mem := k₅.2.1.trans k₄.2.1
  refine WP.mono (storeX_ok hs₅ .rcx (d := T (2 * j)) (by rw [T_eq]; omega))
    fun s₆ ⟨m₆, g₆, _, _, rd₆, wr₆⟩ => ?_
  have O₆ : Outside base (T (2 * j)) 8 s₃.mem s₆.mem := by
    rw [m₆, hm₅]; exact writeW_outside _ _ _ (by rw [T_eq]; omega)
  have hrax : (s₂.gpr .rax).toNat = 512 * (x.toNat % 2 ^ 55) + (word s.mem base (T (2 * j + 1))).toNat / 2 ^ 55 := by
    rw [r₂, k₁.1 _ (by decide), hx, r₁, show 64 - 9 = 55 from rfl]
    have := x.isLt
    omega
  have hrcx : (s₅.gpr .rcx).toNat =
      512 * ((word s.mem base (T (2 * j + 1))).toNat % 2 ^ 55) + (word s.mem base (T (2 * j))).toNat / 2 ^ 55 := by
    rw [r₅, k₄.1 _ (by decide), g₃, k₂.1 _ (by decide), r₁, r₄, hw0, show 64 - 9 = 55 from rfl]
    have := (word s.mem base (T (2 * j + 1))).isLt
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [m₆, hm₅, (writeW_outside _ _ _ (by rw [T_eq]; omega)).word (by rw [T_eq, T_eq]; omega) (by rw [T_eq]; omega),
      m₃, word_writeW_self]; exact hrax
  · rw [m₆, word_writeW_self, hrcx]
  · rw [g₆, k₅.1 _ (by decide), r₄, hw0]
  · refine ⟨fun r hr => ?_, by rw [rd₆, k₅.2.2.1, k₄.2.2.1, rd₃, k₂.2.2.1, k₁.2.2.1],
      by rw [wr₆, k₅.2.2.2, k₄.2.2.2, wr₃, k₂.2.2.2, k₁.2.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₆, k₅.1 r (by simpa using hr.2), k₄.1 r (by simpa using hr.1), g₃, k₂.1 r (by simpa using hr.1),
      k₁.1 r (by simpa using hr.2)]
  · exact (O₃.mono (by rw [T_eq, T_eq]; omega) (by rw [T_eq, T_eq]; omega)).trans
      (O₆.mono (Nat.le_refl _) (by omega))

/-- The pairs `k - 1, …, 0` of `P_lo >> 55`, from `rax` holding word `2k`
(`w (2k)`), the words below `w`: each word `j < 2k` replaced by its step. -/
theorem redLoop_ok {base : Addr} (hZ : 4096 ≤ Z) (w : Nat → BitVec 64) :
    ∀ k ≤ 4, ∀ s₀ : State, Scr s₀ base Z → s₀.gpr .rax = w (2 * k) →
      (∀ j < 2 * k, word s₀.mem base (T j) = w j) →
      WP isa (.block ((List.range k).reverse.flatMap redPair)) s₀ fun s =>
        (∀ j < 2 * k, (word s.mem base (T j)).toNat = 512 * ((w (j + 1)).toNat % 2 ^ 55) + (w j).toNat / 2 ^ 55) ∧
        KeepRegs [.rax, .rcx] s₀ s ∧ Outside base (T 0) (16 * k) s₀.mem s.mem
  | 0, _, _, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, hk, s₀, hs, hx, hw => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.flatMap_cons,
      WP.block_append_iff]
    refine WP.mono (redPair_ok hZ hs (j := k) (by omega) hx) fun s₁ ⟨e1, e0, ra, kk, O⟩ => ?_
    have hs₁ : Scr s₁ base Z := hs.of_keepRegs' kk (by decide)
    have hw₁ : ∀ j < 2 * k, word s₁.mem base (T j) = w j := fun j hj => by
      rw [O.word (by rw [T_eq, T_eq]; omega) (by rw [T_eq]; omega)]; exact hw j (by omega)
    refine WP.mono (redLoop_ok hZ w k (by omega) s₁ hs₁ (by rw [ra, hw (2 * k) (by omega)]) hw₁)
      fun s ⟨e, kk', O'⟩ => ⟨fun j hj => ?_, kk.trans kk', ?_⟩
    · have hk1 : word s.mem base (T (2 * k + 1)) = word s₁.mem base (T (2 * k + 1)) :=
        O'.word (by rw [T_eq, T_eq]; omega) (by rw [T_eq]; omega)
      have hk0 : word s.mem base (T (2 * k)) = word s₁.mem base (T (2 * k)) :=
        O'.word (by rw [T_eq, T_eq]; omega) (by rw [T_eq]; omega)
      rcases Nat.lt_or_ge j (2 * k) with hj' | hj'
      · exact e j hj'
      · rcases Nat.lt_or_ge j (2 * k + 1) with hj'' | hj''
        · obtain rfl : j = 2 * k := by omega
          rw [hk0, e0, hw (2 * k + 1) (by omega), hw (2 * k) (by omega)]
        · obtain rfl : j = 2 * k + 1 := by omega
          rw [hk1, e1, hw (2 * k + 1) (by omega), show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
    · rw [show 16 * (k + 1) = 16 * k + 16 by omega]
      exact (O.mono (by rw [T_eq, T_eq]; omega) (by rw [T_eq, T_eq]; omega)).trans
        (O'.mono (Nat.le_refl _) (by omega))

/-- `adc xAcc (9 + i), [T i]` for `i < n`: `[T 0 …]` added to `xAcc 9 …` with the carry. -/
theorem adcChain_ok {s₀ : State} {base : Addr} (hZ : 4096 ≤ Z) (hs : Scr s₀ base Z) {c₀ : Bool} (hc : s₀.cf = some c₀) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).map fun i => .alu .adc (xAcc (9 + i)) (.mem (sc (T i))))) s₀
      fun s => ∃ c, s.cf = some c ∧
        hval (xg s) 9 n + (2 ^ 64) ^ n * c.toNat = hval (xg s₀) 9 n + tsum s₀.mem base 0 n + c₀.toNat ∧
        (∀ j, 9 + n ≤ j → j < 18 → xg s j = xg s₀ j) ∧ Keeps xRegs s₀ s
  | 0, _ => WP.block_nil ⟨c₀, hc, by simp [hval, tsum], fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  | n + 1, hn => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (adcChain_ok hZ hs hc n (by omega)) fun s ⟨c, cf, e, u, kk⟩ => ?_
    have hsS : Scr s base Z := hs.of_keeps kk (by decide)
    refine WP.mono (adcS_ok s (xAcc (9 + n)) (sc_ok hZ hsS (d := T n) (by rw [T_eq]; omega)) cf)
      fun s' ⟨c', cf', e', k'⟩ => ⟨c', cf', ?_, fun j h1 h2 => ?_, kk.trans (k'.mono ?_)⟩
    · have hlo : hval (xg s') 9 n = hval (xg s) 9 n := hval_congr fun j h1 h2 => by
        simp only [xg]; rw [k'.1 _ (by simpa using xAcc_ne_of (by omega) (by omega))]
      rw [hval_succ_last, hval_succ_last, hlo, ← u (9 + n) (by omega) (by omega)]
      have ht : tsum s₀.mem base 0 (n + 1) = tsum s₀.mem base 0 n + (2 ^ 64) ^ n * (word s₀.mem base (T n)).toNat := by
        rw [tsum_eq, tsum_eq, wordsVal_succ_last, show T 0 + 8 * n = T n by rw [T_eq, T_eq]]
      rw [ht]
      rw [kk.2.1] at e'
      change xg s' (9 + n) + 2 ^ 64 * c'.toNat = xg s (9 + n) + _ + c.toNat at e'
      rw [pow64_succ' n]
      generalize (2 ^ 64) ^ n = Q at *
      have e'' : Q * (xg s' (9 + n) + 2 ^ 64 * c'.toNat) = Q * (xg s (9 + n) + (word s₀.mem base (T n)).toNat + c.toNat) := by
        rw [e']
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_add] at e''
      grind
    · simp only [xg]; rw [k'.1 _ (by simpa using (xAcc_ne_of (show 9 + n < j by omega) (by omega)).symm)]
      exact u j (by omega) h2
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact (xAcc_ne _).2.2.2.2


/-- CF set to `carry`. -/
theorem carryS_ok (s : State) (carry : Bool) :
    WP isa (.block (if carry then [.alu32 .xor .rdx (.reg .rdx), .alu .cmp .rdx (.imm (-1))]
      else [.alu32 .xor .rdx (.reg .rdx)])) s fun s' => s'.cf = some carry ∧ Keeps [.rdx] s s' := by
  cases carry with
  | false => exact WP.mono (xorZ_ok s .rdx) fun s' ⟨_, cf, _, k⟩ => ⟨cf, k⟩
  | true =>
    show WP isa (.block ([.alu32 .xor .rdx (.reg .rdx)] ++ [.alu .cmp .rdx (.imm (-1))])) s _
    rw [WP.block_append_iff]
    exact WP.mono (xorZ_ok s .rdx) fun s₁ ⟨z, _, _, k₁⟩ =>
      WP.mono (cmpM1_ok s₁ .rdx z) fun s₂ ⟨cf, _, k₂⟩ => ⟨cf, k₁.trans (k₂.mono (by simp))⟩

/-- What `redS` leaves: `P_hi + (P₀ mod 2⁵⁵) 2⁴⁶⁶ + ⌊P_lo / 2⁵⁵⌋`. -/
def redQ (s : State) (base : Addr) : Nat :=
  hval (xg s) 9 8 + (word s.mem base (T 0)).toNat % 2 ^ 55 * 2 ^ 466 + tsum s.mem base 0 9 / 2 ^ 55

/-- `redS`: `redQ` plus one if `carry`, into `xWin 9`, for word 16 below `2¹⁸`, if that fits. -/
theorem redS_ok {s : State} {base : Addr} (hZ : 4096 ≤ Z) (hs : Scr s base Z) (carry : Bool) (h16 : xg s 16 < 2 ^ 18)
    (hB : redQ s base + 1 < 2 ^ 576) :
    WP isa (.block (redS carry)) s fun s' =>
      hval (xg s') 9 9 = redQ s base + carry.toNat ∧ KeepRegs (.rax :: .rcx :: .rdx :: xRegs) s s' ∧
        Outside base (T 0) 64 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [redS]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (redPre_ok hZ hs h16) fun s₁ ⟨a₁, r14₁, r15₁, k₁⟩ => ?_
  have hs₁ : Scr s₁ base Z := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (redLoop_ok hZ (fun j => word s.mem base (T j)) 4 (by omega) s₁ hs₁ (by rw [a₁])
    (fun j _ => by rw [k₁.2.1])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ : Scr s₂ base Z := hs₁.of_keepRegs' k₂ (by decide)
  rw [WP.block_append_iff, show [Instr.mov .rax (.mem (sc (T 8))), .shift .shr .rax 55] =
    [.mov .rax (.mem (sc (T 8)))] ++ [.shift .shr .rax 55] from rfl, WP.block_append_iff]
  refine WP.mono (movR_ok s₂ .rax (sc_ok hZ hs₂ (d := T 8) (by t_omega))) fun s₂' ⟨a₂, _, _, k₂'⟩ => ?_
  have hs₂' : Scr s₂' base Z := hs₂.of_keeps k₂' (by decide)
  refine WP.mono (shrS_ok s₂' .rax (n := 55) (by omega)) fun s₃ ⟨a₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (carryS_ok s₃ carry) fun s₄ ⟨cf₄, k₄⟩ => ?_
  have hs₄ : Scr s₄ base Z := (hs₂'.of_keeps k₃ (by decide)).of_keeps k₄ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (adcChain_ok hZ hs₄ cf₄ 8 (by omega)) fun s₅ ⟨c₅, cf₅, e₅, u₅, k₅⟩ => ?_
  refine WP.mono (adcS_ok s₅ (xAcc 17) (src := .reg .rax) rfl cf₅) fun s₆ ⟨c₆, cf₆, e₆, k₆⟩ => ⟨?_, ?_, ?_⟩
  · -- The registers.
    have hm₁ : s₁.mem = s.mem := k₁.2.1
    have x4 : ∀ j, xg s₄ j = xg s₁ j := fun j => by
      simp only [xg]
      rw [k₄.1 _ (by simpa using (xAcc_ne j).2.2.1), k₃.1 _ (by simpa using (xAcc_ne j).1),
        k₂'.1 _ (by simpa using (xAcc_ne j).1),
        k₂.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
                     exact ⟨(xAcc_ne j).1, (xAcc_ne j).2.1⟩)]
    have x1 : ∀ j, 9 ≤ j → j < 16 → xg s₁ j = xg s j := fun j h1 h2 => by
      simp only [xg]
      rw [k₁.1 _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        refine ⟨(xAcc_ne j).1, (xAcc_ne j).2.1, ?_, ?_⟩
        · exact xAcc_ne_of (show j < 16 by omega) (by omega)
        · exact xAcc_ne_of (show j < 17 by omega) (by omega))]
    have h₁ : hval (xg s₁) 9 8 = hval (xg s) 9 7 + (2 ^ 64) ^ 7 * xg s₁ 16 := by
      rw [hval_succ_last, hval_congr fun j h1 h2 => x1 j h1 (by omega)]
    have h₄ : hval (xg s₄) 9 8 = hval (xg s₁) 9 8 := hval_congr fun j _ _ => x4 j
    have h₆ : hval (xg s₆) 9 9 = hval (xg s₅) 9 8 + (2 ^ 64) ^ 8 * xg s₆ 17 := by
      rw [hval_succ_last, hval_congr fun j h1 h2 => by
        simp only [xg]; rw [k₆.1 _ (by simpa using xAcc_ne_of (show j < 17 by omega) (by omega))]]
      rfl
    have h16' : xg s₁ 16 = xg s 16 + (word s.mem base (T 0)).toNat % 2 ^ 46 * 2 ^ 18 := r14₁
    have h17 : xg s₅ 17 = (word s.mem base (T 0)).toNat / 2 ^ 46 % 512 := by
      rw [u₅ 17 (by omega) (by omega), x4]; exact r15₁
    have hrax : (s₅.gpr .rax).toNat = (word s.mem base (T 8)).toNat / 2 ^ 55 := by
      rw [k₅.1 _ (by decide), k₄.1 _ (by decide), a₃, a₂,
        O₂.word (by rw [T_eq, T_eq]; omega) (by rw [T_eq]; omega), hm₁]
    change xg s₆ 17 + 2 ^ 64 * c₆.toNat = xg s₅ 17 + (s₅.gpr .rax).toNat + c₅.toNat at e₆
    rw [h17, hrax] at e₆
    -- The temporary area.
    have ht₄ : tsum s₄.mem base 0 8 = tsum s₂.mem base 0 8 := by rw [k₄.2.1, k₃.2.1, k₂'.2.1]
    have hT : tsum s₂.mem base 0 8 = (512 * ((word s.mem base (T 1)).toNat % 2 ^ 55) +
        (word s.mem base (T 0)).toNat / 2 ^ 55) + 2 ^ 64 * ((512 * ((word s.mem base (T 2)).toNat % 2 ^ 55) +
        (word s.mem base (T 1)).toNat / 2 ^ 55) + 2 ^ 64 * ((512 * ((word s.mem base (T 3)).toNat % 2 ^ 55) +
        (word s.mem base (T 2)).toNat / 2 ^ 55) + 2 ^ 64 * ((512 * ((word s.mem base (T 4)).toNat % 2 ^ 55) +
        (word s.mem base (T 3)).toNat / 2 ^ 55) + 2 ^ 64 * ((512 * ((word s.mem base (T 5)).toNat % 2 ^ 55) +
        (word s.mem base (T 4)).toNat / 2 ^ 55) + 2 ^ 64 * ((512 * ((word s.mem base (T 6)).toNat % 2 ^ 55) +
        (word s.mem base (T 5)).toNat / 2 ^ 55) + 2 ^ 64 * ((512 * ((word s.mem base (T 7)).toNat % 2 ^ 55) +
        (word s.mem base (T 6)).toNat / 2 ^ 55) + 2 ^ 64 * (512 * ((word s.mem base (T 8)).toNat % 2 ^ 55) +
        (word s.mem base (T 7)).toNat / 2 ^ 55))))))) := by
      simp only [tsum, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero]
      rw [e₂ 0 (by omega), e₂ 1 (by omega), e₂ 2 (by omega), e₂ 3 (by omega), e₂ 4 (by omega), e₂ 5 (by omega),
        e₂ 6 (by omega), e₂ 7 (by omega)]
    rw [ht₄, hT, h₄, h₁, h16'] at e₅
    rw [h₆]
    unfold redQ at hB ⊢
    rw [hval_succ_last (xg s) 9 7] at hB ⊢
    simp only [tsum, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hB ⊢
    generalize hval (xg s) 9 7 = H at *
    have := Bool.toNat_le c₆; have := Bool.toNat_le c₅
    omega
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, not_or] at hr
      obtain ⟨hra, hrc, hrd, hrx⟩ := hr
      have hx : ∀ j, r ≠ xAcc j := fun j h => hrx (h ▸ (xAcc_ne j).2.2.2.2)
      rw [k₆.1 r (by simpa using hx 17), k₅.1 r hrx, k₄.1 r (by simpa using hrd), k₃.1 r (by simpa using hra),
        k₂'.1 r (by simpa using hra),
        k₂.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hra, hrc⟩),
        k₁.1 r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hra, hrc, hx 16, hx 17⟩)]
    · rw [k₆.2.2.1, k₅.2.2.1, k₄.2.2.1, k₃.2.2.1, k₂'.2.2.1, k₂.rd, k₁.2.2.1]
    · rw [k₆.2.2.2, k₅.2.2.2, k₄.2.2.2, k₃.2.2.2, k₂'.2.2.2, k₂.wr, k₁.2.2.2]
  · rw [k₆.2.1, k₅.2.1, k₄.2.1, k₃.2.1, k₂'.2.1, ← k₁.2.1]; exact O₂

end VG.Proof.Weierstrass.X86_64.P521F
