module

public import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
import VerifiedGarbage.Proof.Dsa.X86.PowCallFrame
import VerifiedGarbage.Proof.Mont.X86.WindowSelect
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Dsa.X86.Comb.PowerDigits
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Dsa.X86.Comb.Setup
import VerifiedGarbage.Proof.Mont.X86.PublicPowerTiming
import VerifiedGarbage.Proof.Mont.X86.CombDigitMath
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # The product of two powers of DSA's verification on IA-32

Untrusted: everything here is checked by Lean. `Pow.core2` computes
`g^u · y^v mod m` in one pass over both exponents (`core2_ok`), and two runs
of it from the same stack pointer and working space leak the same trace
(`core2_relCT`); its context's setup branches on the top bit of the
modulus, which the runs share (`CoreIn2`).

The numbers it keeps between its pieces are *cells* of the working space
(`Cell`): the four entries (`R` in `cellR`, `g R` in slot 5, `y R` in slot 4,
`g y R` in `cellGY`), the result (slot 6), the selected entry (slot 7) and
the two exponents. Each piece keeps the state of the exponentiation
(`Pow.St`) and every cell but the one it writes (`Kept`).
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.Pow

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow
open VG.Proof.Rsa.MontMul (scratchBytes)

/-! ## Cells -/

/-- The numbers `core2` keeps between its pieces. -/
inductive Cell where
  | y | g | acc | sel | r | gy | u | v
  deriving DecidableEq

/-- A cell's offset in the working space. -/
def Cell.off (n : Nat) : Cell → Nat
  | .y => slot n 4 | .g => slot n 5 | .acc => slot n 6 | .sel => slot n 7
  | .r => cellR n | .gy => cellGY n | .u => slot n 8 | .v => exp2 n

/-- A cell's 32-bit words: an exponent's `e`, a residue's `2 n`. -/
def Cell.len (n e : Nat) : Cell → Nat
  | .u | .v => e
  | _ => 2 * n

/-- Every cell but `w` has the same value in `m₂` as in `m₁`. -/
def Kept (n e : Nat) (base : Addr) (w : Option Cell) (m₁ m₂ : Mem) : Prop :=
  ∀ c : Cell, some c ≠ w → val32 m₂ base (c.off n) (c.len n e) = val32 m₁ base (c.off n) (c.len n e)

theorem cell_bound {n e : Nat} (he : e ≤ 2 * n) (c : Cell) :
    slot n 3 ≤ c.off n ∧ c.off n + 4 * c.len n e ≤ contextBytes n := by
  cases c <;> simp only [Cell.off, Cell.len, slot_lin, cellR, cellGY, exp2, contextBytes] <;> omega

theorem cell_sep {n e : Nat} (he : e ≤ 2 * n) {c c' : Cell} (h : c ≠ c') :
    c.off n + 4 * c.len n e ≤ c'.off n ∨ c'.off n + 4 * c'.len n e ≤ c.off n := by
  cases c <;> cases c' <;> first
    | exact absurd rfl h
    | (simp only [Cell.off, Cell.len, slot_lin, cellR, cellGY, exp2]; omega)

namespace Kept

variable {n e : Nat} {base : Addr} {w : Option Cell} {m₁ m₂ : Mem}

theorem y (K : Kept n e base w m₁ m₂) (h : w ≠ some .y) :
    wordsVal m₂ base (slot n 4) n = wordsVal m₁ base (slot n 4) n := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32]; exact K .y (Ne.symm h)

theorem g (K : Kept n e base w m₁ m₂) (h : w ≠ some .g) :
    wordsVal m₂ base (slot n 5) n = wordsVal m₁ base (slot n 5) n := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32]; exact K .g (Ne.symm h)

theorem acc (K : Kept n e base w m₁ m₂) (h : w ≠ some .acc) :
    wordsVal m₂ base (slot n 6) n = wordsVal m₁ base (slot n 6) n := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32]; exact K .acc (Ne.symm h)

theorem sel (K : Kept n e base w m₁ m₂) (h : w ≠ some .sel) :
    wordsVal m₂ base (slot n 7) n = wordsVal m₁ base (slot n 7) n := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32]; exact K .sel (Ne.symm h)

theorem r (K : Kept n e base w m₁ m₂) (h : w ≠ some .r) :
    wordsVal m₂ base (cellR n) n = wordsVal m₁ base (cellR n) n := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32]; exact K .r (Ne.symm h)

theorem gy (K : Kept n e base w m₁ m₂) (h : w ≠ some .gy) :
    wordsVal m₂ base (cellGY n) n = wordsVal m₁ base (cellGY n) n := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32]; exact K .gy (Ne.symm h)

theorem u (K : Kept n e base w m₁ m₂) (h : w ≠ some .u) :
    val32 m₂ base (slot n 8) e = val32 m₁ base (slot n 8) e := K .u (Ne.symm h)

theorem v (K : Kept n e base w m₁ m₂) (h : w ≠ some .v) :
    val32 m₂ base (exp2 n) e = val32 m₁ base (exp2 n) e := K .v (Ne.symm h)

end Kept

/-- A write within the cell `w` keeps the others. -/
theorem kept_out {n e len : Nat} {base : Addr} {m₁ m₂ : Mem} (w : Cell)
    (O : Outside base (w.off n) len m₁ m₂) (hl : len ≤ 4 * w.len n e) (he : e ≤ 2 * n)
    (hz : contextBytes n ≤ 2 ^ 64) : Kept n e base (some w) m₁ m₂ := by
  intro c hc
  have hcw : c ≠ w := fun h => hc (congrArg some h)
  have b := (cell_bound he c).2
  rcases cell_sep he hcw with h | h
  · exact O.val32 (.inl h) (by omega)
  · exact O.val32 (.inr (by omega)) (by omega)

/-- A write of the header's window word keeps every cell. -/
theorem kept_hdr {n e : Nat} {base : Addr} {m₁ m₂ : Mem} (O : Outside base 4 4 m₁ m₂) (he : e ≤ 2 * n)
    (hz : contextBytes n ≤ 2 ^ 64) : Kept n e base none m₁ m₂ := by
  intro c _
  have b := cell_bound he c
  have := slot_header n 3
  exact O.val32 (.inr (by omega)) (by omega)

theorem scratch_below {n : Nat} (hn : 6 ≤ n) : calleeScratch n + scratchBytes n ≤ slot n 3 := by
  simp only [calleeScratch, scratchBytes, slot_lin]; omega

/-- A multiplication into the cell `w`, a slot, keeps the others. -/
theorem kept_mul {n e size : Nat} {base : Addr} {sp : BitVec 32} {m₁ m₂ : Mem} (w : Cell)
    (hw : w.len n e = 2 * n)
    (O : OutsS base sp [(w.off n, 8 * n), (calleeScratch n, scratchBytes n)] m₁ m₂)
    (R : CallRoom sp base size) (nw : base.toNat + size ≤ 2 ^ 32) (cb : contextBytes n ≤ size)
    (hn : 6 ≤ n) (he : e ≤ 2 * n) : Kept n e base (some w) m₁ m₂ := by
  intro c hc
  have hcw : c ≠ w := fun h => hc (congrArg some h)
  have b := cell_bound he c
  have sb := scratch_below hn
  refine O.val32 R nw (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · dsimp only
    rcases cell_sep he hcw with h | h
    · exact .inl h
    · exact .inr (by omega)
  · dsimp only; omega

/-! ## The pieces -/

theorem shr31_nat (x : BitVec 32) : (x >>> 31).toNat = x.toNat / 2 ^ 31 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The top bit of `j + 1` words: the bit their double carries out. -/
theorem top_bit32 (m : Mem) (base : Addr) (d j : Nat) :
    val32 m base d (j + 1) * 2 / 2 ^ (32 * (j + 1)) = w32 m base (d + 4 * j) / 2 ^ 31 := by
  have hP : 0 < 2 ^ (32 * j) := Nat.two_pow_pos _
  have hV := val32_lt m base d j
  have hq : val32 m base d j * 2 / 2 ^ (32 * j) < 2 := (Nat.div_lt_iff_lt_mul hP).2 (by omega)
  rw [val32_succ, pow32_succ, Nat.mul_comm (2 ^ 32), ← Nat.div_div_eq_div_mul, Nat.add_mul,
    Nat.mul_assoc, Nat.add_mul_div_left _ _ hP]
  generalize val32 m base d j * 2 / 2 ^ (32 * j) = q at hq
  omega

/-- The window word: the top bit of `u`, and twice that of `v`. -/
theorem digit2_ok {s : State} {base : Addr} {size n e : Nat} (hs : Scr s base size) (he : 0 < e)
    (hu : slot n 8 + 4 * e ≤ size) (hv : exp2 n + 4 * e ≤ size) :
    WP isa (.block (digit2 n e)) s fun t => Outside base 4 4 s.mem t.mem ∧
      w32 t.mem base 4 = w32 s.mem base (slot n 8 + 4 * (e - 1)) / 2 ^ 31 +
        2 * (w32 s.mem base (exp2 n + 4 * (e - 1)) / 2 ^ 31) ∧ Keeps [.eax, .ecx] s t := by
  have h8 := slot_header n 8
  unfold digit2 windowOffset
  refine wp_movS (readSrc_sc hs (by omega)) fun s₁ u₁ _ => ?_
  refine wp_shr (by decide) fun s₂ u₂ _ => ?_
  refine wp_addS rfl fun s₃ u₃ _ => ?_
  have k₃ : Keeps [.eax, .ecx] s s₃ :=
    ((u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))
  have m₃ : s₃.mem = s.mem := u₃.mem.trans (u₂.mem.trans u₁.mem)
  have hs₃ := hs.of_keeps k₃ (by decide)
  refine wp_movS (readSrc_sc hs₃ (by omega)) fun s₄ u₄ _ => ?_
  refine wp_shr (by decide) fun s₅ u₅ _ => ?_
  refine wp_addS rfl fun s₆ u₆ _ => ?_
  have k₆ : Keeps [.eax, .ecx] s s₆ :=
    ((k₃.trans (u₄.keeps.mono (by decide))).trans (u₅.keeps.mono (by decide))).trans (u₆.keeps.mono (by decide))
  have m₆ : s₆.mem = s.mem := u₆.mem.trans (u₅.mem.trans (u₄.mem.trans m₃))
  have hs₆ := hs.of_keeps k₆ (by decide)
  refine wp_storeS (hs₆.ea (d := 4) (by omega)) (hs₆.write (d := 4) (n := 4) (by omega)) fun t mt =>
    WP.block_nil ⟨?_, ?_, k₆.trans (mt.keeps _)⟩
  · rw [mt.mem, m₆]; exact writeW32_outside _ _ _ (by decide)
  · have hV : (s₂.gpr .eax).toNat = w32 s.mem base (exp2 n + 4 * (e - 1)) / 2 ^ 31 := by
      rw [u₂.gpr, shr31_nat, u₁.gpr]
    have hU : (s₅.gpr .ecx).toNat = w32 s.mem base (slot n 8 + 4 * (e - 1)) / 2 ^ 31 := by
      rw [u₅.gpr, shr31_nat, u₄.gpr, m₃]
    have e3 : s₃.gpr .eax = s₂.gpr .eax + s₂.gpr .eax := u₃.gpr
    have e5 : s₅.gpr .eax = s₃.gpr .eax := (u₅.other .eax (by decide)).trans (u₄.other .eax (by decide))
    have e6 : s₆.gpr .eax = s₅.gpr .eax + s₅.gpr .ecx := u₆.gpr
    have bV : w32 s.mem base (exp2 n + 4 * (e - 1)) < 2 ^ 32 := BitVec.isLt _
    have bU : w32 s.mem base (slot n 8 + 4 * (e - 1)) < 2 ^ 32 := BitVec.isLt _
    show (t.mem.readW (off base 4) 32).toNat = _
    rw [mt.mem, Mem.readW_writeW_self32, e6, e5, e3, BitVec.toNat_add, BitVec.toNat_add, hV, hU]
    omega

/-- Slot 7 = the entry at `o` where the window is `j`. -/
theorem pick_ok {s : State} {base : Addr} {size n j o : Nat} (hs : Scr s base size) (hn : 0 < n)
    (h7 : slot n 7 + 8 * n ≤ size) (ho : o + 8 * n ≤ size)
    (sep : slot n 7 + 8 * n ≤ o ∨ o + 8 * n ≤ slot n 7) (hw : w32 s.mem base 4 < 32) (hj : j < 32) :
    WP isa (pick n j o) s fun t => Outside base (slot n 7) (8 * n) s.mem t.mem ∧
      wordsVal t.mem base (slot n 7) n = wordsVal s.mem base (if w32 s.mem base 4 = j then o else slot n 7) n ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have h7' := slot_header n 7
  unfold pick
  refine WP.seq (WP.mono (windowMask_ok hs (by omega) hw hj) fun u ⟨M, C, K⟩ => ?_)
  refine WP.mono (selectsW_ok (hs.of_keeps K (by decide)) (decide (w32 s.mem base 4 = j))
    (by rw [C]; simp only [decide_eq_true_eq]) (by omega) (by omega) (by omega) (by omega) (.inl rfl)
    (.inr (by omega))) fun t ⟨O, V, K'⟩ => ?_
  refine ⟨?_, ?_, (K.mono (by decide)).trans (K'.mono (by decide))⟩
  · rw [M] at O; simpa only [show 4 * (2 * n) = 8 * n by omega] using O
  · rw [wordsVal_eq_val32, V, M, wordsVal_eq_val32]
    simp only [decide_eq_true_eq]

/-- The offset of the entry of window `d`. -/
def entryOff (n d : Nat) : Nat :=
  if d = 1 then slot n 5 else if d = 2 then slot n 4 else if d = 3 then cellGY n else cellR n

/-- Slot 7 = the window's entry. -/
theorem select2_ok {s : State} {base : Addr} {size n : Nat} (hs : Scr s base size) (hn : 0 < n)
    (cb : contextBytes n ≤ size) (hw : w32 s.mem base 4 < 4) :
    WP isa (select2 n) s fun t => Outside base (slot n 7) (8 * n) s.mem t.mem ∧
      wordsVal t.mem base (slot n 7) n = wordsVal s.mem base (entryOff n (w32 s.mem base 4)) n ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have nw := hs.nowrap
  have q : slot n 3 + 16 * n + 8 = slot n 4 ∧ slot n 4 + 16 * n + 8 = slot n 5 ∧
      slot n 5 + 2 * (16 * n + 8) = slot n 7 ∧ slot n 7 + 2 * (16 * n + 8) = contextBytes n ∧ 64 ≤ slot n 3 := by
    simp only [slot_lin, contextBytes]; omega
  -- A later piece reads the entries and the window as `s` has them.
  have rd : ∀ {u : State} {o : Nat}, Outside base (slot n 7) (8 * n) s.mem u.mem →
      o + 8 * n ≤ slot n 7 → wordsVal u.mem base o n = wordsVal s.mem base o n :=
    fun O ho => O.wordsVal (.inl ho) (by omega)
  have wd : ∀ {u : State}, Outside base (slot n 7) (8 * n) s.mem u.mem → w32 u.mem base 4 = w32 s.mem base 4 :=
    fun O => O.w32 (.inl (by omega)) (by omega)
  unfold select2 cellR cellGY
  refine WP.seq (WP.mono (copyWords_ok hs hn (by omega) (by omega) (.inr (.inr (by omega))))
    fun u₀ ⟨V₀, O₀, K₀⟩ => ?_)
  refine WP.seq (WP.mono (pick_ok (o := slot n 5) (hs.of_keeps K₀ (by decide)) hn (by omega) (by omega)
    (.inr (by omega)) (by rw [wd O₀]; omega) (by decide)) fun u₁ ⟨O₁, V₁, K₁⟩ => ?_)
  have O₀₁ := O₀.trans O₁
  have K₀₁ := K₀.trans K₁
  refine WP.seq (WP.mono (pick_ok (o := slot n 4) (hs.of_keeps K₀₁ (by decide)) hn (by omega) (by omega)
    (.inr (by omega)) (by rw [wd O₀₁]; omega) (by decide)) fun u₂ ⟨O₂, V₂, K₂⟩ => ?_)
  have O₀₂ := O₀₁.trans O₂
  have K₀₂ := K₀₁.trans K₂
  refine WP.mono (pick_ok (o := slot n 3 + 8 * n) (hs.of_keeps K₀₂ (by decide)) hn (by omega) (by omega)
    (.inr (by omega)) (by rw [wd O₀₂]; omega) (by decide)) fun t ⟨O₃, V₃, K₃⟩ => ?_
  refine ⟨O₀₂.trans O₃, ?_, K₀₂.trans K₃⟩
  rw [V₃, wd O₀₂]
  unfold entryOff cellGY cellR
  by_cases h3 : w32 s.mem base 4 = 3
  · rw [ite_eq_left h3, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h3, rd O₀₂ (by omega)]
  rw [ite_eq_right h3, V₂, wd O₀₁]
  by_cases h2 : w32 s.mem base 4 = 2
  · rw [ite_eq_left h2, ite_eq_right (by omega), ite_eq_left h2, rd O₀₁ (by omega)]
  rw [ite_eq_right h2, V₁, wd O₀]
  by_cases h1 : w32 s.mem base 4 = 1
  · rw [ite_eq_left h1, ite_eq_left h1, rd O₀ (by omega)]
  rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, V₀]

section
variable {n m size e : Nat} {base : Addr} {s₀ : State}

theorem St.hz {t : State} (S : St n m size base s₀ t) : contextBytes n ≤ 2 ^ 64 := by
  have := S.ctx.size_le
  have := S.ctx.scr.nowrap
  omega

/-- A piece between calls that writes within slots 1 to 8, or the header's
window word, keeps the state. -/
theorem St.write {t u : State} (S : St n m size base s₀ t) {rs : List Reg} (K : Keeps rs t u)
    (hrs : ∀ r ∈ rs, r ∈ powerClob) {d len : Nat} (O : Outside base d len t.mem u.mem)
    (hd : (slot n 1 ≤ d ∧ d + len ≤ contextBytes n) ∨ (d = 4 ∧ len = 4)) : St n m size base s₀ u := by
  have q : slot n 0 + 8 * n ≤ slot n 1 ∧ slot n 0 = 64 := by simp only [slot_lin]; omega
  have C : Context n m base size u := S.ctx.outside_keep K
    (fun hh => by have := hrs _ hh; revert this; decide) (fun hh => by have := hrs _ hh; revert this; decide) O
    (by rcases hd with ⟨h1, _⟩ | ⟨rfl, rfl⟩ <;> omega) (by rcases hd with ⟨h1, _⟩ | ⟨rfl, rfl⟩ <;> omega)
  refine S.next C (K.mono hrs) (rs := [(d, len)]) (OutsS.of_outs (Outs.of_outside O (by simp))) fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  rcases hd with ⟨h1, h2⟩ | ⟨rfl, rfl⟩
  · exact ⟨(slot n 1, contextBytes n - slot n 1), List.mem_cons_of_mem _ (List.mem_cons_self ..), h1,
      by dsimp only; omega⟩
  · exact ⟨(0, 8), List.mem_cons_self .., by decide, by decide⟩

/-- A piece between calls that writes within the cell `w`. -/
theorem St.cell {t u : State} (S : St n m size base s₀ t) (he : e ≤ 2 * n) {rs : List Reg} (K : Keeps rs t u)
    (hrs : ∀ r ∈ rs, r ∈ powerClob) (w : Cell) {len : Nat} (O : Outside base (w.off n) len t.mem u.mem)
    (hl : len ≤ 4 * w.len n e) :
    St n m size base s₀ u ∧ Kept n e base (some w) t.mem u.mem ∧ w32 u.mem base 4 = w32 t.mem base 4 := by
  have b := cell_bound he w
  have h3 := slot_le (n := n) (i := 1) (j := 3) (by decide)
  have hd := slot_header n 3
  exact ⟨S.write K hrs O (.inl ⟨by omega, by omega⟩), kept_out w O hl he S.hz, O.w32 (.inl (by omega)) (by omega)⟩

/-- A multiplication into the cell `w`, slot `o`. -/
theorem mulC_ok {t : State} {o a b : Nat} (S : St n m size base s₀ t) (hn : 6 ≤ n) (he : e ≤ 2 * n) (w : Cell)
    (hwo : w.off n = slot n o) (hwl : w.len n e = 2 * n)
    (ho : 4 ≤ o) (ho7 : o ≤ 7) (ha : 4 ≤ a) (ha7 : a ≤ 7) (hb : 4 ≤ b) (hb7 : b ≤ 7)
    (hB : wordsVal t.mem base (slot n b) n < m) :
    WP isa (VG.Impl.Dsa.X86.Pow.mul n o a b) t fun u => St n m size base s₀ u ∧ u.gpr .esi = t.gpr .esi ∧
      wordsVal u.mem base (slot n o) n < m ∧
      wordsVal u.mem base (slot n o) n * 2 ^ (64 * n) % m =
        wordsVal t.mem base (slot n a) n * wordsVal t.mem base (slot n b) n % m ∧
      Kept n e base (some w) t.mem u.mem ∧ w32 u.mem base 4 = w32 t.mem base 4 := by
  have h := S.ctx
  have cb := h.size_le
  have nw := h.scr.nowrap
  refine WP.mono (mul_ok h S.room' (by omega) ho ho7 ha ha7 hb hb7 hB) fun u ⟨cs, rd, wr, O, L, V⟩ => ?_
  have K : Keeps powerClob t u :=
    ⟨fun r hr => cs r (by revert hr; cases r <;> simp [powerClob, calleeSaved]), rd, wr⟩
  have lo := Nat.mul_le_mul_right (16 * n + 8) ho
  have hi := Nat.mul_le_mul_right (16 * n + 8) ho7
  have C : Context n m base size u := Context.outsS_keep h S.room' K (by decide) (by decide) O
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [calleeScratch, slot_lin] <;> omega_arith)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [calleeScratch, slot_lin] <;> omega_using [])
  rw [S.esp] at O
  have b8 := slot_bound (n := n) (i := 8) (by decide)
  simp only [stride] at b8
  refine ⟨S.next C K O fun r hr => ⟨(slot n 1, contextBytes n - slot n 1),
      List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩,
    cs .esi (by decide), L, V,
    kept_mul w hwl (show OutsS base (s₀.gpr .esp) [(w.off n, 8 * n), (calleeScratch n, scratchBytes n)] t.mem u.mem by
      rw [hwo]; exact O) S.room nw cb hn he, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [contextBytes, calleeScratch, scratchBytes, slot_lin] at b8 ⊢ <;> omega_arith
  · exact congrArg BitVec.toNat (O.readW32 S.room nw (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [calleeScratch, slot_lin] <;> omega_using [])
      (by simp only [contextBytes, slot_lin] at cb; omega_using [cb]))

/-- One in the cell `w`. -/
theorem oneC_ok {t : State} (S : St n m size base s₀ t) (he : e ≤ 2 * n) (w : Cell) (hw : w.len n e = 2 * n) :
    WP isa (one n (w.off n)) t fun u => St n m size base s₀ u ∧
      wordsVal u.mem base (w.off n) n = 1 ∧ Kept n e base (some w) t.mem u.mem := by
  have b := cell_bound he w
  have cb := S.ctx.size_le
  refine WP.mono (one_ok S.ctx.scr S.ctx.modulus.n0 (by omega)) fun u ⟨O, V, K⟩ => ?_
  obtain ⟨Su, Ku, _⟩ := S.cell he K (by decide) w O (by omega)
  exact ⟨Su, V, Ku⟩

/-- A copy of the cell `src` into the cell `dst`. -/
theorem copyC_ok {t : State} (S : St n m size base s₀ t) (he : e ≤ 2 * n) (src dst : Cell)
    (hs : src.len n e = 2 * n) (hd : dst.len n e = 2 * n) (hne : dst ≠ src) :
    WP isa (copyWords n (src.off n) (dst.off n)) t fun u => St n m size base s₀ u ∧
      wordsVal u.mem base (dst.off n) n = wordsVal t.mem base (src.off n) n ∧
      Kept n e base (some dst) t.mem u.mem ∧ w32 u.mem base 4 = w32 t.mem base 4 := by
  have bs := cell_bound he src
  have bd := cell_bound he dst
  have cb := S.ctx.size_le
  have sep := cell_sep he hne
  refine WP.mono (copyWords_ok S.ctx.scr S.ctx.modulus.n0 (by omega) (by omega) (.inr (by omega)))
    fun u ⟨V, O, K⟩ => ?_
  obtain ⟨Su, Ku, W⟩ := S.cell he K (by decide) dst O (by omega)
  exact ⟨Su, V, Ku, W⟩

/-- The window word from the exponents' top bits. -/
theorem digitC_ok {t : State} (S : St n m size base s₀ t) (he0 : 0 < e) (he : e ≤ 2 * n) :
    WP isa (.block (digit2 n e)) t fun u => St n m size base s₀ u ∧ u.gpr .esi = t.gpr .esi ∧
      w32 u.mem base 4 = val32 t.mem base (slot n 8) e * 2 / 2 ^ (32 * e) +
        2 * (val32 t.mem base (exp2 n) e * 2 / 2 ^ (32 * e)) ∧ Kept n e base none t.mem u.mem := by
  have bu : slot n 8 + 4 * e ≤ contextBytes n := (cell_bound he .u).2
  have bv : exp2 n + 4 * e ≤ contextBytes n := (cell_bound he .v).2
  have cb := S.ctx.size_le
  refine WP.mono (digit2_ok S.ctx.scr he0 (by omega) (by omega)) fun u ⟨O, V, K⟩ => ?_
  refine ⟨S.write K (by decide) O (.inr ⟨rfl, rfl⟩), K.1 .esi (by decide), ?_, kept_hdr O he S.hz⟩
  obtain ⟨j, rfl⟩ : ∃ j, e = j + 1 := ⟨e - 1, by omega⟩
  rw [V, top_bit32, top_bit32]
  rfl

/-- The selected entry in slot 7. -/
theorem selectC_ok {t : State} (S : St n m size base s₀ t) (he : e ≤ 2 * n) (hw : w32 t.mem base 4 < 4) :
    WP isa (select2 n) t fun u => St n m size base s₀ u ∧ u.gpr .esi = t.gpr .esi ∧
      wordsVal u.mem base (slot n 7) n = wordsVal t.mem base (entryOff n (w32 t.mem base 4)) n ∧
      Kept n e base (some .sel) t.mem u.mem := by
  refine WP.mono (select2_ok S.ctx.scr S.ctx.modulus.n0 S.ctx.size_le hw) fun u ⟨O, V, K⟩ => ?_
  obtain ⟨Su, Ku, _⟩ := S.cell he K (by decide) .sel O (Nat.le_of_eq (by show 8 * n = 4 * (2 * n); omega))
  exact ⟨Su, K.1 .esi (by decide), V, Ku⟩

/-- The exponent in the cell `w` shifted up by a bit. -/
theorem shiftC_ok {t : State} (S : St n m size base s₀ t) (he0 : 0 < e) (he : e ≤ 2 * n) (w : Cell)
    (hw : w.len n e = e) :
    WP isa (Comb.shiftOne e (w.off n)) t fun u => St n m size base s₀ u ∧ u.gpr .esi = t.gpr .esi ∧
      val32 u.mem base (w.off n) e = val32 t.mem base (w.off n) e * 2 % 2 ^ (32 * e) ∧
      Kept n e base (some w) t.mem u.mem := by
  have b := cell_bound he w
  have cb := S.ctx.size_le
  refine WP.mono (shiftOne_ok S.ctx.scr he0 (by omega)) fun u ⟨O, V, K⟩ => ?_
  obtain ⟨Su, Ku, _⟩ := S.cell he K (by decide) w O (by omega)
  exact ⟨Su, K.1 .esi (by decide), V, Ku⟩

end

/-! ## The arithmetic of the pass

With `k` bits of each exponent left, `ru` and `rv`, an iteration takes the
result `A` to `A² g^bu y^bv` for their top bits `bu` and `bv`, and leaves the
`k - 1` bits below them: `A^(2^k) g^ru y^rv` does not change (`joint_step`).
The exponents' words hold those bits at the top (`ru 2^i`, after `i`
iterations): their double carries the top bit out (`top_step`).
-/

theorem joint_step (A g y ru rv k : Nat) (hk : 0 < k) :
    (A * A * (g ^ (ru / 2 ^ (k - 1)) * y ^ (rv / 2 ^ (k - 1)))) ^ 2 ^ (k - 1) *
      g ^ (ru % 2 ^ (k - 1)) * y ^ (rv % 2 ^ (k - 1)) = A ^ 2 ^ k * g ^ ru * y ^ rv := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hA : A ^ 2 ^ (j + 1) = (A * A) ^ 2 ^ j := by
    rw [Nat.pow_succ, Nat.mul_comm, Nat.pow_mul, Nat.pow_two]
  generalize 2 ^ j = P at hA ⊢
  have hu : g ^ ru = (g ^ (ru / P)) ^ P * g ^ (ru % P) := by
    rw [← Nat.pow_mul, ← Nat.pow_add, Nat.mul_comm, Nat.div_add_mod]
  have hv : y ^ rv = (y ^ (rv / P)) ^ P * y ^ (rv % P) := by
    rw [← Nat.pow_mul, ← Nat.pow_add, Nat.mul_comm, Nat.div_add_mod]
  rw [hA, hu, hv]
  simp only [Nat.mul_pow]
  ac_rfl

theorem top_step (r i k W : Nat) (h : W = i + k) (hk : 0 < k) :
    r * 2 ^ i * 2 / 2 ^ W = r / 2 ^ (k - 1) ∧ r * 2 ^ i * 2 % 2 ^ W = r % 2 ^ (k - 1) * 2 ^ (i + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  subst h
  rw [Nat.add_sub_cancel, show r * 2 ^ i * 2 = r * 2 ^ (i + 1) by rw [Nat.pow_succ, Nat.mul_assoc],
    show 2 ^ (i + (j + 1)) = 2 ^ j * 2 ^ (i + 1) by rw [← Nat.pow_add]; congr 1; omega]
  exact ⟨Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _), Nat.mul_mod_mul_right _ _ _⟩

theorem Kept.refl (n e : Nat) (base : Addr) (w : Option Cell) (m : Mem) : Kept n e base w m m := fun _ _ => rfl

theorem Kept.trans {n e : Nat} {base : Addr} {w : Option Cell} {m₁ m₂ m₃ : Mem} (h₁ : Kept n e base w m₁ m₂)
    (h₂ : Kept n e base w m₂ m₃) : Kept n e base w m₁ m₃ := fun c hc => (h₂ c hc).trans (h₁ c hc)

/-- The entries of `core2`: `R`, `g R`, `y R` and `g y R` modulo `m`. -/
structure Tab (n m : Nat) (base : Addr) (g y : Nat) (mem : Mem) : Prop where
  rR : wordsVal mem base (cellR n) n = 2 ^ (64 * n) % m
  gR : wordsVal mem base (slot n 5) n = g * 2 ^ (64 * n) % m
  yR : wordsVal mem base (slot n 4) n = y * 2 ^ (64 * n) % m
  gyR : wordsVal mem base (cellGY n) n = g * y * 2 ^ (64 * n) % m

theorem Tab.keep {n m e : Nat} {base : Addr} {g y : Nat} {mem mem' : Mem} {w : Option Cell}
    (T : Tab n m base g y mem) (K : Kept n e base w mem mem')
    (hw : w = none ∨ w = some .acc ∨ w = some .sel ∨ w = some .u ∨ w = some .v) : Tab n m base g y mem' := by
  rcases hw with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨(K.r (by decide)).trans T.rR, (K.g (by decide)).trans T.gR, (K.y (by decide)).trans T.yR,
      (K.gy (by decide)).trans T.gyR⟩

theorem Tab.entry {n m : Nat} {base : Addr} {g y : Nat} {mem : Mem} (T : Tab n m base g y mem) {d : Nat}
    (hd : d < 4) : wordsVal mem base (entryOff n d) n = g ^ (d % 2) * y ^ (d / 2) * 2 ^ (64 * n) % m := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · simpa [entryOff] using T.rR
  · simpa [entryOff] using T.gR
  · simpa [entryOff] using T.yR
  · simpa [entryOff] using T.gyR

section
variable {n m size e : Nat} {base : Addr} {s₀ : State}

/-- `k` squarings of slot 4, as `squarings_ok`, with the cells they keep. -/
theorem squaringsC_ok {t : State} (hn : 6 ≤ n) (he : e ≤ 2 * n) (j : Nat) :
    ∀ k, St n m size base s₀ t →
    wordsVal t.mem base (slot n 4) n = 2 ^ (64 * n + n * 2 ^ j) % m →
    WP isa (squarings n k) t fun u => St n m size base s₀ u ∧
      wordsVal u.mem base (slot n 4) n = 2 ^ (64 * n + n * 2 ^ (j + k)) % m ∧
      Kept n e base (some .y) t.mem u.mem
  | 0, S, hx => WP.block_nil ⟨S, hx, Kept.refl _ _ _ _ _⟩
  | k + 1, S, hx => by
    refine WP.seq (WP.mono (squaringsC_ok hn he j k S hx) fun u ⟨Su, xu, Ku⟩ => ?_)
    refine WP.mono (mulC_ok (e := e) (o := 4) (a := 4) (b := 4) Su hn he .y rfl rfl (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by rw [xu]; exact Nat.mod_lt _ (by have := Su.ctx.gt_one; omega)))
      fun w ⟨Sw, _, L, P, K, _⟩ => ⟨Sw, ?_, Ku.trans K⟩
    rw [square_value Su.ctx.coprime xu P L, show j + (k + 1) = (j + k) + 1 from rfl, Nat.pow_succ,
      Nat.mul_comm (2 ^ (j + k)) 2, Nat.mul_left_comm]

/-- The entries, from `R²`, `g` and `y`. -/
theorem table2_ok {t : State} {g y : Nat} (S : St n m size base s₀ t) (hn : 6 ≤ n) (he : e ≤ 2 * n)
    (hr2 : wordsVal t.mem base (slot n 4) n = 2 ^ (128 * n) % m)
    (hg : wordsVal t.mem base (slot n 5) n = g) (hy : wordsVal t.mem base (slot n 7) n = y) :
    WP isa (table2 n) t fun u => St n m size base s₀ u ∧ Tab n m base g y u.mem ∧
      wordsVal u.mem base (slot n 6) n = 2 ^ (64 * n) % m ∧
      val32 u.mem base (slot n 8) e = val32 t.mem base (slot n 8) e ∧
      val32 u.mem base (exp2 n) e = val32 t.mem base (exp2 n) e := by
  have cop := S.ctx.coprime
  have hm1 := S.ctx.gt_one
  have mpos : 0 < m := by omega
  obtain RR : 2 ^ (128 * n) = 2 ^ (64 * n) * 2 ^ (64 * n) := by rw [← Nat.pow_add]; congr 1; omega
  unfold table2
  refine WP.seq (WP.mono (mulC_ok (e := e) (o := 5) (a := 5) (b := 4) S hn he .g rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [hr2]; exact Nat.mod_lt _ mpos))
    fun s₁ ⟨S₁, _, L₁, P₁, K₁, _⟩ => ?_)
  obtain g₁ : wordsVal s₁.mem base (slot n 5) n = g * 2 ^ (64 * n) % m := by
    obtain v := VG.Proof.Bignum.mont_cancel cop (o := wordsVal s₁.mem base (slot n 5) n) (c := g * 2 ^ (64 * n)) (by
      rw [P₁, hr2, hg, Nat.mul_mod_mod, RR, Nat.mul_assoc])
    rwa [Nat.mod_eq_of_lt L₁] at v
  obtain x₁ : wordsVal s₁.mem base (slot n 4) n = 2 ^ (128 * n) % m := by rw [K₁.y (by decide), hr2]
  refine WP.seq (WP.mono (mulC_ok (e := e) (o := 7) (a := 7) (b := 4) S₁ hn he .sel rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [x₁]; exact Nat.mod_lt _ mpos))
    fun s₂ ⟨S₂, _, L₂, P₂, K₂, _⟩ => ?_)
  obtain y₂ : wordsVal s₂.mem base (slot n 7) n = y * 2 ^ (64 * n) % m := by
    obtain v := VG.Proof.Bignum.mont_cancel cop (o := wordsVal s₂.mem base (slot n 7) n) (c := y * 2 ^ (64 * n)) (by
      rw [P₂, x₁, K₁.sel (by decide), hy, Nat.mul_mod_mod, RR, Nat.mul_assoc])
    rwa [Nat.mod_eq_of_lt L₂] at v
  refine WP.seq (WP.mono (oneC_ok (e := e) S₂ he .acc rfl) fun s₃ ⟨S₃, O₃, K₃⟩ => ?_)
  have o₃ : wordsVal s₃.mem base (slot n 6) n = 1 := O₃
  obtain x₃ : wordsVal s₃.mem base (slot n 4) n = 2 ^ (128 * n) % m := by
    rw [K₃.y (by decide), K₂.y (by decide), x₁]
  refine WP.seq (WP.mono (mulC_ok (e := e) (o := 6) (a := 4) (b := 6) S₃ hn he .acc rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [o₃]; exact hm1))
    fun s₄ ⟨S₄, _, L₄, P₄, K₄, _⟩ => ?_)
  obtain r₄ : wordsVal s₄.mem base (slot n 6) n = 2 ^ (64 * n) % m := by
    obtain v := VG.Proof.Dsa.mont_decode cop (A := wordsVal s₃.mem base (slot n 4) n) (a := 2 ^ (64 * n))
      (by rw [x₃, Nat.mod_mod, RR]) (by rw [P₄, o₃])
    rwa [Nat.mod_eq_of_lt L₄] at v
  refine WP.seq (WP.mono (copyC_ok (e := e) S₄ he .acc .r rfl rfl (by decide)) fun s₅ ⟨S₅, V₅, K₅, _⟩ => ?_)
  obtain r₅ : wordsVal s₅.mem base (cellR n) n = 2 ^ (64 * n) % m := V₅.trans r₄
  obtain g₅ : wordsVal s₅.mem base (slot n 5) n = g * 2 ^ (64 * n) % m := by
    rw [K₅.g (by decide), K₄.g (by decide), K₃.g (by decide), K₂.g (by decide), g₁]
  obtain y₅ : wordsVal s₅.mem base (slot n 7) n = y * 2 ^ (64 * n) % m := by
    rw [K₅.sel (by decide), K₄.sel (by decide), K₃.sel (by decide), y₂]
  refine WP.seq (WP.mono (mulC_ok (e := e) (o := 4) (a := 5) (b := 7) S₅ hn he .y rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [y₅]; exact Nat.mod_lt _ mpos))
    fun s₆ ⟨S₆, _, L₆, P₆, K₆, _⟩ => ?_)
  obtain gy₆ : wordsVal s₆.mem base (slot n 4) n = g * y * 2 ^ (64 * n) % m := by
    obtain v := VG.Proof.Dsa.mont_product cop (a := g) (b := y) (by rw [g₅, Nat.mod_mod]) (by rw [y₅, Nat.mod_mod]) P₆
    rwa [Nat.mod_eq_of_lt L₆] at v
  refine WP.seq (WP.mono (copyC_ok (e := e) S₆ he .y .gy rfl rfl (by decide)) fun s₇ ⟨S₇, V₇, K₇, _⟩ => ?_)
  obtain gy₇ : wordsVal s₇.mem base (cellGY n) n = g * y * 2 ^ (64 * n) % m := V₇.trans gy₆
  refine WP.mono (copyC_ok (e := e) S₇ he .sel .y rfl rfl (by decide)) fun u ⟨Su, Vu, Ku, _⟩ => ?_
  have yu : wordsVal u.mem base (slot n 4) n = wordsVal s₇.mem base (slot n 7) n := Vu
  refine ⟨Su, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [Ku.r (by decide), K₇.r (by decide), K₆.r (by decide), r₅]
  · rw [Ku.g (by decide), K₇.g (by decide), K₆.g (by decide), g₅]
  · rw [yu, K₇.sel (by decide), K₆.sel (by decide), y₅]
  · rw [Ku.gy (by decide), gy₇]
  · rw [Ku.acc (by decide), K₇.acc (by decide), K₆.acc (by decide), K₅.acc (by decide), r₄]
  · rw [Ku.u (by decide), K₇.u (by decide), K₆.u (by decide), K₅.u (by decide), K₄.u (by decide),
      K₃.u (by decide), K₂.u (by decide), K₁.u (by decide)]
  · rw [Ku.v (by decide), K₇.v (by decide), K₆.v (by decide), K₅.v (by decide), K₄.v (by decide),
      K₃.v (by decide), K₂.v (by decide), K₁.v (by decide)]

/-- An iteration, with `k` bits of each exponent left after `i`. -/
theorem step2_ok {t : State} {g y A ru rv i k : Nat} (S : St n m size base s₀ t) (hn : 6 ≤ n) (he0 : 0 < e)
    (he : e ≤ 2 * n) (T : Tab n m base g y t.mem)
    (hA : wordsVal t.mem base (slot n 6) n = A * 2 ^ (64 * n) % m)
    (hU : val32 t.mem base (slot n 8) e = ru * 2 ^ i) (hV : val32 t.mem base (exp2 n) e = rv * 2 ^ i)
    (hik : 32 * e = i + k) (hk : 0 < k) (hru : ru < 2 ^ k) (hrv : rv < 2 ^ k)
    (hk32 : k < 2 ^ 32) (hc : t.gpr .esi = BitVec.ofNat 32 k) :
    WP isa (step2 n e) t fun u => St n m size base s₀ u ∧ Tab n m base g y u.mem ∧
      u.gpr .esi = BitVec.ofNat 32 (k - 1) ∧ u.zf = some (decide (k = 1)) ∧
      wordsVal u.mem base (slot n 6) n =
        A * A * (g ^ (ru / 2 ^ (k - 1)) * y ^ (rv / 2 ^ (k - 1))) * 2 ^ (64 * n) % m ∧
      val32 u.mem base (slot n 8) e = ru % 2 ^ (k - 1) * 2 ^ (i + 1) ∧
      val32 u.mem base (exp2 n) e = rv % 2 ^ (k - 1) * 2 ^ (i + 1) := by
  have cop := S.ctx.coprime
  have hm1 := S.ctx.gt_one
  have mpos : 0 < m := by omega
  obtain ⟨tu₁, tu₂⟩ := top_step ru i k (32 * e) hik hk
  obtain ⟨tv₁, tv₂⟩ := top_step rv i k (32 * e) hik hk
  have e2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]
  have bu : ru / 2 ^ (k - 1) < 2 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by omega)
  have bv : rv / 2 ^ (k - 1) < 2 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by omega)
  generalize ru / 2 ^ (k - 1) = du at tu₁ bu ⊢
  generalize rv / 2 ^ (k - 1) = dv at tv₁ bv ⊢
  unfold step2
  refine WP.seq (WP.mono (mulC_ok (e := e) (o := 6) (a := 6) (b := 6) S hn he .acc rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [hA]; exact Nat.mod_lt _ mpos))
    fun s₁ ⟨S₁, i₁, L₁, P₁, K₁, _⟩ => ?_)
  obtain a₁ : wordsVal s₁.mem base (slot n 6) n = A * A * 2 ^ (64 * n) % m := by
    obtain v := VG.Proof.Dsa.mont_product cop (a := A) (b := A) (by rw [hA, Nat.mod_mod]) (by rw [hA, Nat.mod_mod]) P₁
    rwa [Nat.mod_eq_of_lt L₁] at v
  obtain T₁ := T.keep K₁ (.inr (.inl rfl))
  refine WP.seq (WP.mono (digitC_ok S₁ he0 he) fun s₂ ⟨S₂, i₂, D₂, K₂⟩ => ?_)
  obtain d₂ : w32 s₂.mem base 4 = du + 2 * dv := by
    rw [D₂, K₁.u (by decide), K₁.v (by decide), hU, hV, tu₁, tv₁]
  obtain T₂ := T₁.keep K₂ (.inl rfl)
  refine WP.seq (WP.mono (selectC_ok (e := e) S₂ he (by rw [d₂]; omega)) fun s₃ ⟨S₃, i₃, V₃, K₃⟩ => ?_)
  obtain sel₃ : wordsVal s₃.mem base (slot n 7) n = g ^ du * y ^ dv * 2 ^ (64 * n) % m := by
    rw [V₃, T₂.entry (d := w32 s₂.mem base 4) (by rw [d₂]; omega), d₂, show (du + 2 * dv) % 2 = du by omega,
      show (du + 2 * dv) / 2 = dv by omega]
  obtain a₃ : wordsVal s₃.mem base (slot n 6) n = A * A * 2 ^ (64 * n) % m := by
    rw [K₃.acc (by decide), K₂.acc (by decide), a₁]
  obtain T₃ := T₂.keep K₃ (.inr (.inr (.inl rfl)))
  refine WP.seq (WP.mono (mulC_ok (e := e) (o := 6) (a := 6) (b := 7) S₃ hn he .acc rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [sel₃]; exact Nat.mod_lt _ mpos))
    fun s₄ ⟨S₄, i₄, L₄, P₄, K₄, _⟩ => ?_)
  obtain a₄ : wordsVal s₄.mem base (slot n 6) n = A * A * (g ^ du * y ^ dv) * 2 ^ (64 * n) % m := by
    obtain v := VG.Proof.Dsa.mont_product cop (a := A * A) (b := g ^ du * y ^ dv)
      (by rw [a₃, Nat.mod_mod]) (by rw [sel₃, Nat.mod_mod]) P₄
    rwa [Nat.mod_eq_of_lt L₄] at v
  obtain T₄ := T₃.keep K₄ (.inr (.inl rfl))
  refine WP.seq (WP.mono (shiftC_ok S₄ he0 he .u rfl) fun s₅ ⟨S₅, i₅, U₅, K₅⟩ => ?_)
  have u₅ : val32 s₅.mem base (slot n 8) e = val32 s₄.mem base (slot n 8) e * 2 % 2 ^ (32 * e) := U₅
  refine WP.seq (WP.mono (shiftC_ok S₅ he0 he .v rfl) fun s₆ ⟨S₆, i₆, V₆, K₆⟩ => ?_)
  have v₆ : val32 s₆.mem base (exp2 n) e = val32 s₅.mem base (exp2 n) e * 2 % 2 ^ (32 * e) := V₆
  obtain T₆ := (T₄.keep K₅ (.inr (.inr (.inr (.inl rfl))))).keep K₆ (.inr (.inr (.inr (.inr rfl))))
  obtain c₆ : s₆.gpr .esi = BitVec.ofNat 32 k := by rw [i₆, i₅, i₄, i₃, i₂, i₁, hc]
  refine wp_subS rfl fun v uv _ => ?_
  refine wp_cmpS rfl fun u fu zu => WP.block_nil ?_
  obtain mu : u.mem = s₆.mem := fu.mem.trans uv.mem
  obtain ku : Keeps powerClob s₆ u := (uv.keeps.mono (by decide)).trans (fu.keeps _)
  obtain Cu : Context n m base size u := ⟨S₆.ctx.scr.of_keeps ku (by decide), S₆.ctx.size_le,
    mu ▸ S₆.ctx.modulus, S₆.ctx.gt_one, mu ▸ S₆.ctx.inverse⟩
  refine ⟨⟨Cu, S₆.room, S₆.keeps.trans ku, mu ▸ S₆.mem⟩, mu ▸ T₆, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fu.gpr, uv.gpr, c₆, counter_sub hk32 hk]
  · rw [zu, uv.gpr, c₆, counter_sub hk32 hk, counter_zero hk32 hk]
  · rw [mu, K₆.acc (by decide), K₅.acc (by decide), a₄]
  · rw [mu, K₆.u (by decide), u₅, K₄.u (by decide), K₃.u (by decide), K₂.u (by decide), K₁.u (by decide), hU, tu₂]
  · rw [mu, v₆, K₅.v (by decide), K₄.v (by decide), K₃.v (by decide), K₂.v (by decide), K₁.v (by decide), hV, tv₂]

/-- After `i` iterations: the result `A`, and the bits of the exponents
left, `ru` and `rv`, at the top of their words. -/
structure Loop2 (n m size e : Nat) (g y target i : Nat) (base : Addr) (s₀ t : State) : Prop where
  st : St n m size base s₀ t
  tab : Tab n m base g y t.mem
  counter : t.gpr .esi = BitVec.ofNat 32 (32 * e - i)
  value : ∃ A ru rv, wordsVal t.mem base (slot n 6) n = A * 2 ^ (64 * n) % m ∧
    val32 t.mem base (slot n 8) e = ru * 2 ^ i ∧ val32 t.mem base (exp2 n) e = rv * 2 ^ i ∧
    ru < 2 ^ (32 * e - i) ∧ rv < 2 ^ (32 * e - i) ∧
    A ^ 2 ^ (32 * e - i) * g ^ ru * y ^ rv % m = target

theorem loop2_ok {t : State} {g y : Nat} (S : St n m size base s₀ t) (hn : 6 ≤ n) (he0 : 0 < e)
    (he : e ≤ 2 * n) (T : Tab n m base g y t.mem)
    (hA : wordsVal t.mem base (slot n 6) n = 2 ^ (64 * n) % m)
    (hk32 : 32 * e < 2 ^ 32) (hc : t.gpr .esi = BitVec.ofNat 32 (32 * e)) :
    WP isa (.loop (step2 n e) .ne) t
      (Loop2 n m size e g y (g ^ val32 t.mem base (slot n 8) e * y ^ val32 t.mem base (exp2 n) e % m)
        (32 * e) base s₀) := by
  generalize htg : g ^ val32 t.mem base (slot n 8) e * y ^ val32 t.mem base (exp2 n) e % m = target
  obtain init : Loop2 n m size e g y target 0 base s₀ t :=
    ⟨S, T, by rw [Nat.sub_zero]; exact hc, 1, val32 t.mem base (slot n 8) e, val32 t.mem base (exp2 n) e,
      by rw [Nat.one_mul]; exact hA, by rw [Nat.pow_zero, Nat.mul_one], by rw [Nat.pow_zero, Nat.mul_one],
      by rw [Nat.sub_zero]; exact val32_lt _ _ _ _, by rw [Nat.sub_zero]; exact val32_lt _ _ _ _,
      by rw [Nat.one_pow, Nat.one_mul]; exact htg⟩
  refine WP.loop (M := isa)
    (fun k u => ∃ i, k = 32 * e - i ∧ i < 32 * e ∧ Loop2 n m size e g y target i base s₀ u)
    ?_ (32 * e) t ⟨0, rfl, by omega, init⟩
  rintro k u ⟨i, rfl, hi, I⟩
  obtain ⟨A, ru, rv, hA', hU, hV, bu, bv, hT⟩ := I.value
  obtain ⟨j, hj⟩ : ∃ j, 32 * e - i = j + 1 := ⟨32 * e - i - 1, by omega⟩
  have hj' : 32 * e - (i + 1) = j := by omega
  have cnt₀ := I.counter
  rw [hj] at bu bv hT cnt₀ ⊢
  refine WP.mono (step2_ok (i := i) (k := j + 1) I.st hn he0 he I.tab hA' hU hV (by omega) (by omega) bu bv
    (by omega) cnt₀) fun w ⟨S', T', cnt, zf, A', U', V'⟩ => ?_
  rw [Nat.add_sub_cancel] at cnt A' U' V'
  obtain next : Loop2 n m size e g y target (i + 1) base s₀ w := by
    refine ⟨S', T', by rw [hj']; exact cnt, _, _, _, A', U', V', ?_, ?_, ?_⟩
    · rw [hj']; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · rw [hj']; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · have := joint_step A g y ru rv (j + 1) (by omega)
      rw [Nat.add_sub_cancel] at this
      rw [hj', this]; exact hT
  by_cases hdone : i + 1 = 32 * e
  · refine .inl ⟨?_, ?_⟩
    · have eq : j + 1 = 1 := by omega
      simp only [eval, zf, eq, decide_true, Option.map_some, Bool.not_true]
    · rw [hdone] at next
      exact next
  · refine .inr ⟨?_, 32 * e - (i + 1), by omega, i + 1, rfl, by omega, next⟩
    obtain ne : j + 1 ≠ 1 := by omega
    simp only [eval, zf, decide_eq_false ne, Option.map_some, Bool.not_false]

theorem Loop2.finished {g y target : Nat} {t : State} (I : Loop2 n m size e g y target (32 * e) base s₀ t) :
    wordsVal t.mem base (slot n 6) n = target * 2 ^ (64 * n) % m := by
  obtain ⟨A, ru, rv, hA, _, _, bu, bv, hT⟩ := I.value
  simp only [Nat.sub_self, Nat.pow_zero] at bu bv hT
  obtain rfl : ru = 0 := by omega
  obtain rfl : rv = 0 := by omega
  simp only [Nat.pow_one, Nat.pow_zero, Nat.mul_one] at hT
  rw [hA, Nat.mul_mod A, hT, Nat.mul_mod_mod]

end

/-! ## The product of two powers -/

theorem core2_ok {s : State} {base : Addr} {size n e m : Nat}
    (hs : Scr s base size) (R : CallRoom (s.gpr .esp) base size) (hz : contextBytes n ≤ size)
    (hn : 6 ≤ n) (hn48 : n ≤ 48) (he : 0 < e) (hen : e ≤ 2 * n)
    (hv : wordsVal s.mem base (slot n 0) n = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (core2 n e) s fun t =>
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) e *
          wordsVal s.mem base (slot n 7) n ^ val32 s.mem base (exp2 n) e % m ∧
      OutsS base (s.gpr .esp) (coreRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  have nw := hs.nowrap
  unfold core2 setup2
  refine WP.seq (WP.seq (WP.mono (VG.Proof.Dsa.X86.Comb.seed_ok hs (by omega) (by omega) hz hv hm1 hodd)
    fun u ⟨Cu, _, Xu, Ou, Ku⟩ => ?_))
  obtain Su : St n m size base s u := ⟨Cu, R, Ku, (OutsS.of_outs Ou).core (setupRanges_core n)⟩
  -- The setup writes the header and slots 1 to 4.
  obtain keep₀ : ∀ (c : Cell), slot n 5 ≤ c.off n →
      val32 u.mem base (c.off n) (c.len n e) = val32 s.mem base (c.off n) (c.len n e) := by
    intro c hc
    have b := (cell_bound hen c).2
    apply Ou.val32
    · simp only [setupRanges, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      simp only [slot_lin] at hc ⊢
      omega
    · omega
  refine WP.mono (squaringsC_ok (e := e) hn hen 0 6 Su (by
    rw [Xu, Nat.pow_zero, Nat.mul_one, show 64 * n + n = 65 * n by omega])) fun w ⟨Sw, Xw, Kw⟩ => ?_
  have q : slot n 5 ≤ slot n 7 ∧ slot n 5 ≤ slot n 8 ∧ slot n 5 ≤ exp2 n := by
    simp only [slot_lin, exp2]; omega
  have gw : wordsVal w.mem base (slot n 5) n = wordsVal s.mem base (slot n 5) n := by
    rw [Kw.g (by decide), wordsVal_eq_val32, wordsVal_eq_val32]; exact keep₀ .g (Nat.le_refl _)
  have yw : wordsVal w.mem base (slot n 7) n = wordsVal s.mem base (slot n 7) n := by
    rw [Kw.sel (by decide), wordsVal_eq_val32, wordsVal_eq_val32]; exact keep₀ .sel q.1
  have uw : val32 w.mem base (slot n 8) e = val32 s.mem base (slot n 8) e := (Kw.u (by decide)).trans (keep₀ .u q.2.1)
  have vw : val32 w.mem base (exp2 n) e = val32 s.mem base (exp2 n) e := (Kw.v (by decide)).trans (keep₀ .v q.2.2)
  refine WP.seq (WP.mono (table2_ok (e := e) Sw hn hen (by
    rw [Xw, show 64 * n + n * 2 ^ (0 + 6) = 128 * n by rw [show (2 : Nat) ^ (0 + 6) = 64 from rfl]; omega]) gw yw)
    fun v ⟨Sv, Tv, Av, Uv, Vv⟩ => ?_)
  refine WP.seq (wp_movS rfl fun v₁ u₁ _ => WP.block_nil ?_)
  obtain k₁ : Keeps powerClob v v₁ := u₁.keeps.mono (by decide)
  obtain S₁ : St n m size base s v₁ := ⟨⟨Sv.ctx.scr.of_keeps k₁ (by decide), Sv.ctx.size_le,
    u₁.mem ▸ Sv.ctx.modulus, Sv.ctx.gt_one, u₁.mem ▸ Sv.ctx.inverse⟩, Sv.room, Sv.keeps.trans k₁, u₁.mem ▸ Sv.mem⟩
  refine WP.seq (WP.mono (loop2_ok S₁ hn he hen (u₁.mem ▸ Tv) (by rw [u₁.mem]; exact Av) (by omega) u₁.gpr)
    fun x I => ?_)
  refine WP.mono (finish_ok I.st (by omega) I.finished (Nat.mod_lt _ (by omega))) fun t ⟨St, V⟩ =>
    ⟨?_, St.mem, St.keeps⟩
  rw [V, u₁.mem, Uv, Vv, uw, vw]

/-! ## The trace

Two runs of `core2` from the same stack pointer and working space leak the
same trace. As for `core` (`Wk`), what each piece needs of a run each piece
keeps (`Wc`): the state `St`, the counter where the code uses it, and the
cells that a later call takes as its second operand below the modulus. The
pieces between calls are checked by the taint analysis, whose result does
not depend on the offsets (`check_of_erase_eq`); the calls are related by
`mul_relCT`.
-/

section
variable {n e : Nat} {base : Addr} {sp : BitVec 32}

/-- A run of `core2`: its state `St` from a start at `sp`, the counter `cnt`
in `esi` where known, and the cells `cs` below the modulus. -/
def Wc (n : Nat) (base : Addr) (sp : BitVec 32) (cnt : Option Nat) (cs : List Cell) (u : State) : Prop :=
  ∃ size m s₀, St n m size base s₀ u ∧ s₀.gpr .esp = sp ∧
    (∀ c, cnt = some c → u.gpr .esi = BitVec.ofNat 32 c) ∧
    ∀ x ∈ cs, wordsVal u.mem base (x.off n) n < m

theorem Wc.agree {cnt : Option Nat} {cs : List Cell} {s t : State} (W₁ : Wc n base sp cnt cs s)
    (W₂ : Wc n base sp cnt cs t) : VG.X86.Taint.Agree (workspaceTaint cnt.isSome) s t := by
  obtain ⟨_, _, _, S₁, _, c₁, _⟩ := W₁
  obtain ⟨_, _, _, S₂, _, c₂, _⟩ := W₂
  have edi : s.gpr .edi = t.gpr .edi :=
    BitVec.eq_of_toNat_eq (S₁.ctx.scr.edi_toNat.trans S₂.ctx.scr.edi_toNat.symm)
  cases cnt with
  | none => exact agree_regs (rs := [.edi]) fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact edi
  | some c =>
    refine agree_regs (rs := [.edi, .esi]) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact edi
    · rw [c₁ c rfl, c₂ c rfl]

/-- A piece the taint analysis checks, for a run that also meets `X`. -/
theorem wc_taint {cnt : Option Nat} {cs : List Cell} {c : Prog isa} {X F : State → Prop}
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (hT : (VG.Taint.check taint (workspaceTaint cnt.isSome) c hc).isSome = true)
    (hw : ∀ u, Wc n base sp cnt cs u → X u → WP isa c u F) :
    RelCT isa (Both fun u => Wc n base sp cnt cs u ∧ X u) c (Both F) :=
  relCT_both (RelCT.taint _ (fun _ _ h => Wc.agree h.1.1 h.2.1) hT) fun u h => hw u h.1 h.2

/-- The run after a piece that writes the cell `w` (or none): the cells of
`cs'` are `w`, below the modulus, or cells of `cs` that it keeps. -/
theorem wc_set {size m : Nat} {s₀ u v : State} {cnt : Option Nat} {cs cs' : List Cell} {w : Option Cell}
    (Sv : St n m size base s₀ v) (hsp : s₀.gpr .esp = sp)
    (cv : ∀ c, cnt = some c → v.gpr .esi = BitVec.ofNat 32 c)
    (B : ∀ x ∈ cs, wordsVal u.mem base (x.off n) n < m) (hcs : ∀ x ∈ cs, x.len n e = 2 * n)
    (K : Kept n e base w u.mem v.mem)
    (hnew : ∀ x ∈ cs', some x = w → wordsVal v.mem base (x.off n) n < m)
    (hcs' : ∀ x ∈ cs', some x = w ∨ (x ∈ cs ∧ some x ≠ w)) : Wc n base sp cnt cs' v := by
  refine ⟨size, m, s₀, Sv, hsp, cv, fun x hx => ?_⟩
  rcases hcs' x hx with h | ⟨hx', hxw⟩
  · exact hnew x hx h
  · have k := K x hxw
    rw [hcs x hx'] at k
    rw [wordsVal_eq_val32, k, ← wordsVal_eq_val32]
    exact B x hx'

/-- A multiplication into the cell `w` (slot `o`) by the cell `wb` (slot `b`). -/
theorem wc_mul {cnt : Option Nat} {cs cs' : List Cell} (hn : 6 ≤ n) (he : e ≤ 2 * n) {o a b : Nat} (w wb : Cell)
    (hwo : w.off n = slot n o) (hwl : w.len n e = 2 * n) (hbo : wb.off n = slot n b)
    (ho : 4 ≤ o) (ho7 : o ≤ 7) (ha : 4 ≤ a) (ha7 : a ≤ 7) (hb4 : 4 ≤ b) (hb7 : b ≤ 7) (hb : wb ∈ cs)
    (hcs : ∀ x ∈ cs, x.len n e = 2 * n) (hcs' : ∀ x ∈ cs', some x = some w ∨ (x ∈ cs ∧ some x ≠ some w)) :
    RelCT isa (Both (Wc n base sp cnt cs)) (VG.Impl.Dsa.X86.Pow.mul n o a b) (Both (Wc n base sp cnt cs')) := by
  refine relCT_both ((mul_relCT (base := base) sp (by omega) ho ho7 ha ha7 hb4 hb7).mono
    (fun _ _ h => ⟨?_, ?_⟩) fun _ _ h => h) ?_
  · obtain ⟨size, m, s₀, S, e', _, B⟩ := h.1
    exact ⟨size, m, S.ctx, e' ▸ S.room, S.esp.trans e', by rw [← hbo]; exact B wb hb⟩
  · obtain ⟨size, m, s₀, S, e', _, B⟩ := h.2
    exact ⟨size, m, S.ctx, e' ▸ S.room, S.esp.trans e', by rw [← hbo]; exact B wb hb⟩
  intro u ⟨size, m, s₀, S, e', c, B⟩
  refine WP.mono (mulC_ok S hn he w hwo hwl ho ho7 ha ha7 hb4 hb7 (by rw [← hbo]; exact B wb hb))
    fun v ⟨Sv, iv, L, _, K, _⟩ => wc_set Sv e' (fun c' h => by rw [iv]; exact c c' h) B hcs K
      (fun x _ hx => by obtain rfl := Option.some.inj hx; rw [hwo]; exact L) hcs'

theorem digit2_check (n e : Nat) :
    (VG.Taint.check taint (workspaceTaint true) (.block (digit2 n e)) (.block [])).isSome = true :=
  (congrArg Option.isSome (check_of_erase_eq (.block (digit2 n e)) (.block (digit2 1 1)) (workspaceTaint true)
    (.block []) rfl rfl rfl)).trans (by kernel_rfl)

def copyHint (counter : Bool) : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint (workspaceTaint counter) (Code.erase (copyWords 1 0 0))

theorem copy_check (counter : Bool) (n src dst : Nat) :
    (VG.Taint.check taint (workspaceTaint counter) (copyWords n src dst) (copyHint counter)).isSome = true :=
  (congrArg Option.isSome (check_of_erase_eq (copyWords n src dst) (copyWords 1 0 0) (workspaceTaint counter)
    (copyHint counter) rfl (by cases counter <;> rfl) (by cases counter <;> kernel_rfl))).trans
    (by cases counter <;> kernel_rfl)

def select2Hint : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (select2 1))

theorem select2_check (n : Nat) :
    (VG.Taint.check taint (workspaceTaint true) (select2 n) select2Hint).isSome = true :=
  (congrArg Option.isSome (check_of_erase_eq (select2 n) (select2 1) (workspaceTaint true) select2Hint rfl rfl
    (by kernel_rfl))).trans (by kernel_rfl)

def shiftOneHint : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint (workspaceTaint true) (Code.erase (Comb.shiftOne 1 0))

theorem shiftOne_check (k o : Nat) :
    (VG.Taint.check taint (workspaceTaint true) (Comb.shiftOne k o) shiftOneHint).isSome = true :=
  (congrArg Option.isSome (check_of_erase_eq (Comb.shiftOne k o) (Comb.shiftOne 1 0) (workspaceTaint true)
    shiftOneHint rfl rfl (by kernel_rfl))).trans (by kernel_rfl)

/-- Cells that are not exponents hold `2 n` words. -/
theorem res_len {cs : List Cell} (h : ∀ x ∈ cs, x ≠ Cell.u ∧ x ≠ Cell.v) : ∀ x ∈ cs, x.len n e = 2 * n := by
  intro x hx
  have := h x hx
  cases x <;> first | rfl | exact absurd rfl this.1 | exact absurd rfl this.2

/-- The cells an iteration keeps below the modulus: the entries and the result. -/
abbrev loopCells : List Cell := [.y, .g, .r, .gy, .acc]

theorem loopCells_len (x : Cell) (hx : x ∈ loopCells) : x.len n e = 2 * n := by
  simp only [loopCells, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem entry_lt {m : Nat} {mem : Mem} (B : ∀ x ∈ loopCells, wordsVal mem base (x.off n) n < m) (d : Nat) :
    wordsVal mem base (entryOff n d) n < m := by
  unfold entryOff
  split
  · exact B .g (by decide)
  split
  · exact B .y (by decide)
  split
  · exact B .gy (by decide)
  · exact B .r (by decide)

/-- The entries. -/
theorem wc_table (hn : 6 ≤ n) (he : e ≤ 2 * n) :
    RelCT isa (Both (Wc n base sp none [.y])) (table2 n) (Both (Wc n base sp none loopCells)) := by
  have none_cnt : ∀ {u : State} (c : Nat), (none : Option Nat) = some c → u.gpr .esi = BitVec.ofNat 32 c :=
    fun _ h => nomatch h
  unfold table2
  refine VG.RelCT.seq (wc_mul (cs' := [.y, .g]) hn he .g .y rfl rfl rfl (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (res_len (by decide)) (by decide)) ?_
  refine VG.RelCT.seq (wc_mul (cs' := [.y, .g, .sel]) hn he .sel .y rfl rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (res_len (by decide)) (by decide)) ?_
  refine VG.RelCT.seq (((wc_taint (cnt := none) (cs := [.y, .g, .sel]) (X := fun _ => True)
    (F := Wc n base sp none [.acc, .y, .g, .sel]) (hc := oneHint false)
    (by rw [show (none : Option Nat).isSome = false from rfl, one_check]; rfl) fun u W _ => ?_)).mono
    (fun _ _ h => ⟨⟨h.1, trivial⟩, ⟨h.2, trivial⟩⟩) fun _ _ h => h) ?_
  · obtain ⟨size, m, s₀, S, e', _, B⟩ := W
    exact WP.mono (oneC_ok (e := e) S he .acc rfl) fun v ⟨Sv, O, K⟩ => wc_set Sv e' none_cnt B (res_len (by decide)) K
      (fun x _ hx => by obtain rfl := Option.some.inj hx; rw [O]; exact S.ctx.gt_one) (by decide)
  refine VG.RelCT.seq (wc_mul (cs' := [.acc, .y, .g, .sel]) hn he .acc .acc rfl rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (res_len (by decide)) (by decide)) ?_
  refine VG.RelCT.seq (((wc_taint (cnt := none) (cs := [.acc, .y, .g, .sel]) (X := fun _ => True)
    (F := Wc n base sp none [.r, .acc, .y, .g, .sel]) (hc := copyHint false)
    (copy_check false n _ _) fun u W _ => ?_)).mono
    (fun _ _ h => ⟨⟨h.1, trivial⟩, ⟨h.2, trivial⟩⟩) fun _ _ h => h) ?_
  · obtain ⟨size, m, s₀, S, e', _, B⟩ := W
    exact WP.mono (copyC_ok (e := e) S he .acc .r rfl rfl (by decide)) fun v ⟨Sv, V, K, _⟩ =>
      wc_set Sv e' none_cnt B (res_len (by decide)) K
        (fun x _ hx => by obtain rfl := Option.some.inj hx; rw [V]; exact B .acc (by decide)) (by decide)
  refine VG.RelCT.seq (wc_mul (cs' := [.r, .acc, .y, .g, .sel]) hn he .y .sel rfl rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (res_len (by decide)) (by decide)) ?_
  refine VG.RelCT.seq (((wc_taint (cnt := none) (cs := [.r, .acc, .y, .g, .sel]) (X := fun _ => True)
    (F := Wc n base sp none [.gy, .r, .acc, .y, .g, .sel]) (hc := copyHint false)
    (copy_check false n _ _) fun u W _ => ?_)).mono
    (fun _ _ h => ⟨⟨h.1, trivial⟩, ⟨h.2, trivial⟩⟩) fun _ _ h => h) ?_
  · obtain ⟨size, m, s₀, S, e', _, B⟩ := W
    exact WP.mono (copyC_ok (e := e) S he .y .gy rfl rfl (by decide)) fun v ⟨Sv, V, K, _⟩ =>
      wc_set Sv e' none_cnt B (res_len (by decide)) K
        (fun x _ hx => by obtain rfl := Option.some.inj hx; rw [V]; exact B .y (by decide)) (by decide)
  refine ((wc_taint (cnt := none) (cs := [.gy, .r, .acc, .y, .g, .sel]) (X := fun _ => True)
    (F := Wc n base sp none loopCells) (hc := copyHint false)
    (copy_check false n _ _) fun u W _ => ?_)).mono
    (fun _ _ h => ⟨⟨h.1, trivial⟩, ⟨h.2, trivial⟩⟩) fun _ _ h => h
  obtain ⟨size, m, s₀, S, e', _, B⟩ := W
  exact WP.mono (copyC_ok (e := e) S he .sel .y rfl rfl (by decide)) fun v ⟨Sv, V, K, _⟩ =>
    wc_set Sv e' none_cnt B (res_len (by decide)) K
      (fun x _ hx => by obtain rfl := Option.some.inj hx; rw [V]; exact B .sel (by decide)) (by decide)

theorem wc_start2 (e' : Nat) :
    RelCT isa (Both (Wc n base sp none loopCells)) (.block [.mov .esi (.imm (BitVec.ofNat 32 e'))])
      (Both (Wc n base sp (some e') loopCells)) :=
  (wc_taint (cnt := none) (cs := loopCells) (X := fun _ => True) (hc := .block []) rfl fun u W _ =>
    wp_movS rfl fun v U _ => WP.block_nil (by
      obtain ⟨size, m, s₀, S, hsp, _, B⟩ := W
      have K : Keeps powerClob u v := U.keeps.mono (by decide)
      refine ⟨size, m, s₀, ⟨⟨S.ctx.scr.of_keeps K (by decide), S.ctx.size_le, U.mem ▸ S.ctx.modulus, S.ctx.gt_one,
        U.mem ▸ S.ctx.inverse⟩, S.room, S.keeps.trans K, U.mem ▸ S.mem⟩, hsp, fun c h => ?_, fun b hb => ?_⟩
      · cases h; exact U.gpr
      · rw [U.mem]; exact B b hb)).mono (fun _ _ h => ⟨⟨h.1, trivial⟩, ⟨h.2, trivial⟩⟩) fun _ _ h => h

theorem wc_step2 {j : Nat} (hn : 6 ≤ n) (he0 : 0 < e) (he : e ≤ 2 * n) (hj : 0 < j) (hj32 : j < 2 ^ 32) :
    RelCT isa (Both (Wc n base sp (some j) loopCells)) (step2 n e)
      (Both fun u => Wc n base sp (some (j - 1)) loopCells u ∧ u.zf = some (decide (j = 1))) := by
  have tr : ∀ s t : State, Both (Wc n base sp (some j) loopCells) s t →
      Both (fun u => Wc n base sp (some j) loopCells u ∧ True) s t := fun _ _ h => ⟨⟨h.1, trivial⟩, ⟨h.2, trivial⟩⟩
  have same : ∀ x ∈ loopCells, some x = some Cell.acc ∨ (x ∈ loopCells ∧ some x ≠ some Cell.acc) := by decide
  unfold step2
  refine VG.RelCT.seq (wc_mul (cs' := loopCells) hn he .acc .acc rfl rfl rfl (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) loopCells_len same) ?_
  refine VG.RelCT.seq ((wc_taint (cnt := some j) (cs := loopCells) (X := fun _ => True)
    (F := fun u => Wc n base sp (some j) loopCells u ∧ w32 u.mem base 4 < 4) (hc := .block [])
    (digit2_check n e) fun u W _ => ?_).mono tr fun _ _ h => h) ?_
  · obtain ⟨size, m, s₀, S, hsp, c, B⟩ := W
    refine WP.mono (digitC_ok S he0 he) fun v ⟨Sv, iv, D, K⟩ =>
      ⟨wc_set Sv hsp (fun c' h => by rw [iv]; exact c c' h) B loopCells_len K (fun x _ hx => nomatch hx) (by decide), ?_⟩
    have b₁ : val32 u.mem base (slot n 8) e * 2 / 2 ^ (32 * e) < 2 :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by have := val32_lt u.mem base (slot n 8) e; omega)
    have b₂ : val32 u.mem base (exp2 n) e * 2 / 2 ^ (32 * e) < 2 :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by have := val32_lt u.mem base (exp2 n) e; omega)
    rw [D]; omega
  refine VG.RelCT.seq (wc_taint (cnt := some j) (cs := loopCells) (F := Wc n base sp (some j) (.sel :: loopCells))
    (hc := select2Hint) (select2_check n) fun u W hw => ?_) ?_
  · obtain ⟨size, m, s₀, S, hsp, c, B⟩ := W
    exact WP.mono (selectC_ok (e := e) S he hw) fun v ⟨Sv, iv, V, K⟩ =>
      wc_set Sv hsp (fun c' h => by rw [iv]; exact c c' h) B loopCells_len K
        (fun x _ hx => by obtain rfl := Option.some.inj hx; rw [show Cell.off n .sel = slot n 7 from rfl, V]; exact entry_lt B _)
        (by decide)
  refine VG.RelCT.seq (wc_mul (cs := .sel :: loopCells) (cs' := loopCells) hn he .acc .sel rfl rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun x hx => by
      simp only [loopCells, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) (by decide)) ?_
  refine VG.RelCT.seq ((wc_taint (cnt := some j) (cs := loopCells) (X := fun _ => True)
    (F := Wc n base sp (some j) loopCells) (hc := shiftOneHint) (shiftOne_check e _) fun u W _ => ?_).mono tr
    fun _ _ h => h) ?_
  · obtain ⟨size, m, s₀, S, hsp, c, B⟩ := W
    exact WP.mono (shiftC_ok S he0 he .u rfl) fun v ⟨Sv, iv, _, K⟩ =>
      wc_set Sv hsp (fun c' h => by rw [iv]; exact c c' h) B loopCells_len K (fun x hm hx => by
        obtain rfl := Option.some.inj hx; exact absurd hm (by decide)) (by decide)
  refine VG.RelCT.seq ((wc_taint (cnt := some j) (cs := loopCells) (X := fun _ => True)
    (F := Wc n base sp (some j) loopCells) (hc := shiftOneHint) (shiftOne_check e _) fun u W _ => ?_).mono tr
    fun _ _ h => h) ?_
  · obtain ⟨size, m, s₀, S, hsp, c, B⟩ := W
    exact WP.mono (shiftC_ok S he0 he .v rfl) fun v ⟨Sv, iv, _, K⟩ =>
      wc_set Sv hsp (fun c' h => by rw [iv]; exact c c' h) B loopCells_len K (fun x hm hx => by
        obtain rfl := Option.some.inj hx; exact absurd hm (by decide)) (by decide)
  refine (wc_taint (cnt := some j) (cs := loopCells) (X := fun _ => True) (hc := .block [])
    (show (VG.Taint.check taint (workspaceTaint true) _ _).isSome = true from rfl) fun u W _ => ?_).mono tr
    fun _ _ h => h
  obtain ⟨size, m, s₀, S, hsp, c, B⟩ := W
  have hc := c j rfl
  refine wp_subS rfl fun v uv _ => ?_
  refine wp_cmpS rfl fun w fw zw => WP.block_nil ?_
  have mw : w.mem = u.mem := fw.mem.trans uv.mem
  have kw : Keeps powerClob u w := (uv.keeps.mono (by decide)).trans (fw.keeps _)
  refine ⟨⟨size, m, s₀, ⟨⟨S.ctx.scr.of_keeps kw (by decide), S.ctx.size_le, mw ▸ S.ctx.modulus, S.ctx.gt_one,
    mw ▸ S.ctx.inverse⟩, S.room, S.keeps.trans kw, mw ▸ S.mem⟩, hsp, fun c' h => ?_, fun b hb => ?_⟩, ?_⟩
  · cases h; rw [fw.gpr, uv.gpr, hc, counter_sub hj32 hj]
  · rw [mw]; exact B b hb
  · rw [zw, uv.gpr, hc, counter_sub hj32 hj, counter_zero hj32 hj]

theorem wc_loop2 (hn : 6 ≤ n) (he0 : 0 < e) (he : e ≤ 2 * n) (j : Nat) :
    RelCT isa (fun s t => 0 < j ∧ j < 2 ^ 32 ∧ Both (Wc n base sp (some j) loopCells) s t)
      (.loop (step2 n e) .ne) (Both (Wc n base sp (some 0) loopCells)) := by
  refine VG.RelCT.loop (M := isa)
    (I := fun j s t => 0 < j ∧ j < 2 ^ 32 ∧ Both (Wc n base sp (some j) loopCells) s t) (fun j => ?_) j
  by_cases hj : 0 < j ∧ j < 2 ^ 32
  · refine (wc_step2 hn he0 he hj.1 hj.2).mono (fun _ _ h => h.2.2) ?_
    rintro s t ⟨⟨W₁, z₁⟩, ⟨W₂, z₂⟩⟩
    have e₁ : isa.eval .ne s = some (!decide (j = 1)) := by show s.zf.map (!·) = _; rw [z₁]; rfl
    have e₂ : isa.eval .ne t = some (!decide (j = 1)) := by show t.zf.map (!·) = _; rw [z₂]; rfl
    refine ⟨e₁.trans e₂.symm, fun h => ?_, fun h => ?_⟩
    · rw [e₁] at h
      have d : j = 1 := by simpa using h
      rw [d] at W₁ W₂
      exact ⟨W₁, W₂⟩
    · rw [e₁] at h
      have : j ≠ 1 := by simpa using h
      exact ⟨j - 1, by omega, by omega, by omega, W₁, W₂⟩
  · exact VG.RelCT.of_false fun _ _ h => hj ⟨h.1, h.2.1⟩

/-- What `core2` needs of a run on entry: as `CoreIn`, with the working
space's size and the modulus, which two runs share: the modulus is public. -/
def CoreIn2 (n : Nat) (base : Addr) (sp : BitVec 32) (size m : Nat) (u : State) : Prop :=
  Scr u base size ∧ CallRoom sp base size ∧ u.gpr .esp = sp ∧ contextBytes n ≤ size ∧
    wordsVal u.mem base (slot n 0) n = m ∧ 1 < m ∧ m % 2 = 1

theorem contextStart_check (n : Nat) :
    VG.Taint.check taint (workspaceTaint false) (contextStart n)
      (.seq (workspaceTaint false) (.block []) (oneHint false)) = some (zerosTaint false) :=
  exponent_check_seq taint (setupInverse_taint false (slot n 0) 0) (by rfl) (one_check false n (slot n 3))

/-- The context's seed: its branch is on the top word of the modulus, which
the two runs share. -/
theorem seed_relCT {size m : Nat} (hn : 0 < n) :
    RelCT isa (Both (CoreIn2 n base sp size m)) (VG.Impl.Dsa.X86.Comb.seed n) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  simp only [stride] at b0
  by_cases hsz : contextBytes n ≤ size
  case neg => exact VG.RelCT.of_false fun _ _ h => hsz h.1.2.2.2.1
  unfold VG.Impl.Dsa.X86.Comb.seed
  refine RelCT.seq (R := fun (s t : State) => Context n m base size s ∧ Context n m base size t) ?_ ?_
  · intro s t tr ur sf tf ⟨⟨hs, _, _, hz, hv, hm1, hodd⟩, ⟨ht, _, _, _, hv', _, _⟩⟩ Es Et
    have DI : s.gpr .edi = t.gpr .edi := BitVec.eq_of_toNat_eq (hs.edi_toNat.trans ht.edi_toNat.symm)
    exact ⟨((RelCT.taint (A := taint) (hc := .seq (workspaceTaint false) (.block []) (oneHint false))
        (workspaceTaint false)
        (fun (a b : State) (h : a.gpr .edi = b.gpr .edi) => agree_regs (rs := [.edi]) fun r hr => by
          obtain rfl := List.mem_singleton.mp hr; exact h)
        (by rw [contextStart_check]; rfl)) _ _ _ _ _ _ DI Es Et).1,
      (wp_result (contextStart_ok hs hn hz hv hm1 hodd) Es).1,
      (wp_result (contextStart_ok ht hn hz hv' hm1 hodd) Et).1⟩
  · apply (publicPower_relCT (contextMod n) (slot n 2) (slot n 4) base size (by
      change slot n 0 + 4 * (2 * n - 1) + 4 ≤ size
      omega)).mono
    · intro s t ⟨S, T⟩
      refine ⟨S.scr, T.scr, ?_⟩
      change w32 s.mem base (slot n 0 + 4 * (2 * n - 1)) = w32 t.mem base (slot n 0 + 4 * (2 * n - 1))
      rw [← VG.Proof.Mont.X86.Comb.val32_word (by omega : 2 * n - 1 < 2 * n),
        ← VG.Proof.Mont.X86.Comb.val32_word (by omega : 2 * n - 1 < 2 * n),
        ← wordsVal_eq_val32, ← wordsVal_eq_val32,
        show wordsVal s.mem base (slot n 0) n = m from S.modulus.val,
        show wordsVal t.mem base (slot n 0) n = m from T.modulus.val]
    · exact fun _ _ h => h

theorem wk_seed2 {size m : Nat} (hn : 2 ≤ n) (hn48 : n ≤ 48) :
    RelCT isa (Both (CoreIn2 n base sp size m)) (VG.Impl.Dsa.X86.Comb.seed n) (Both (Wk n base sp none [4])) := by
  have W : ∀ u, CoreIn2 n base sp size m u → WP isa (VG.Impl.Dsa.X86.Comb.seed n) u (Wk n base sp none [4]) := by
    intro u ⟨hs, R, e', hz, hv, hm1, hodd⟩
    refine WP.mono (VG.Proof.Dsa.X86.Comb.seed_ok hs (by omega) (by omega) hz hv hm1 hodd)
      fun v ⟨Cv, _, Xv, Ov, Kv⟩ => ?_
    rw [← e'] at R
    refine ⟨size, m, u, ⟨Cv, R, Kv, (OutsS.of_outs Ov).core (setupRanges_core n)⟩, e', ?_, fun b hb => ?_⟩
    · intro c h; cases h
    · rw [List.mem_singleton.mp hb, Xv]
      exact Nat.mod_lt _ (by omega)
  intro s t tr ur sf tf H E F
  exact ⟨(seed_relCT (by omega) _ _ _ _ _ _ H E F).1, wp_result (W s H.1) E, wp_result (W t H.2) F⟩

theorem core2_relCT {size m : Nat} (hn : 6 ≤ n) (hn48 : n ≤ 48) (he : 0 < e) (hen : e ≤ 2 * n) :
    RelCT isa (Both (CoreIn2 n base sp size m)) (core2 n e) (fun _ _ => True) := by
  have toWc : ∀ u : State, Wk n base sp none [4] u → Wc n base sp none [.y] u := by
    rintro u ⟨size, m, s₀, S, hsp, c, B⟩
    exact ⟨size, m, s₀, S, hsp, c, fun x hx => by rw [List.mem_singleton.mp hx]; exact B 4 (by simp)⟩
  have toWk : ∀ u : State, Wc n base sp (some 0) loopCells u → Wk n base sp (some 0) [] u := by
    rintro u ⟨size, m, s₀, S, hsp, c, _⟩
    exact ⟨size, m, s₀, S, hsp, c, fun _ h => nomatch h⟩
  unfold core2 setup2
  refine VG.RelCT.seq (VG.RelCT.seq (wk_seed2 (by omega) hn48) (wk_squarings (by omega) 6)) ?_
  refine VG.RelCT.seq ((wc_table hn hen).mono (fun _ _ h => ⟨toWc _ h.1, toWc _ h.2⟩) fun _ _ h => h) ?_
  refine VG.RelCT.seq (wc_start2 (32 * e)) ?_
  refine VG.RelCT.seq ((wc_loop2 hn he hen (32 * e)).mono (fun _ _ h => ⟨by omega, by omega, h⟩) fun _ _ h => h) ?_
  exact (wk_finish (base := base) (sp := sp) (cnt := some 0) (by omega)).mono
    (fun _ _ h => ⟨toWk _ h.1, toWk _ h.2⟩) fun _ _ h => h

end

/-! ## In a stage of DSA's schedule

A stage calls its helper from a stack with `Room`, 108 bytes: `core2`'s
multiplications, called from the stage itself, use 96 of them. -/

theorem Room.callRoom {sp : BitVec 32} {base : Addr} {size : Nat} (H : Room sp base size)
    (nw : base.toNat + size ≤ 2 ^ 32) : CallRoom sp base size := by
  obtain ⟨h108, _⟩ := id H
  refine ⟨by omega, fun x h₁ h₂ => ?_⟩
  have := zone_ofs' H nw (k := 96) (by decide) h₁
  simp only [Region.Contains, ofs] at h₂ this
  omega

theorem OutsS.stackOuts {sp : BitVec 32} {base : Addr} {size : Nat} {rs : List (Nat × Nat)} {m₁ m₂ : Mem}
    (O : OutsS base sp rs m₁ m₂) (H : Room sp base size) (nw : base.toNat + size ≤ 2 ^ 32)
    (hu : VG.Impl.Dsa.Layout.usedBytes ≤ size) : StackOuts base sp rs m₁ m₂ := by
  obtain ⟨h108, _⟩ := id H
  intro x hx hs
  refine O x hx fun hz => ?_
  rcases hs with h | h
  · have := zone_ofs' H nw (k := 96) (by decide) hz
    omega
  · exact h (VG.X86.below_sub (by decide) h108 x hz)

end VG.Proof.Dsa.X86.Pow
