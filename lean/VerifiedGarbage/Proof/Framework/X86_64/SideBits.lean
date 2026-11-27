module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChecks
public import VerifiedGarbage.Impl.Scrub.X86_64
import VerifiedGarbage.Proof.Framework.InlineMatch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# What a cleanup asks of every instruction, in one match (x86-64)

The side conditions of a cleanup (`scrubSideG`) ask of every
instruction of the code its level (`Instr.vecLevelR`), whether it loads
MXCSR (`loadsMxcsr`) or writes a vector register (`writesVec`), and whether
it writes each of the registers the cleanup leaves (`Taint.clobbers`): a
match on the instruction each, and one for every register, of which the
kernel evaluates every one at every instruction. `sideBits` is all of them
in one number, a bit for each register and one for each other fact, made by
one match whose cases are closed (`inline_match%`), and the conditions are
masks of it (`sideOk`).
-/

@[expose] public section

namespace VG.X86_64

namespace SideBits

open VG.Impl.Scrub.X86_64 (writesVec)

/-- A register's bit. -/
def regBit (r : Reg) : Nat := Nat.pow 2 r.ctorIdx

def optBit : Option Reg → Nat
  | none => 0
  | some r => regBit r

/-- The registers an instruction writes. -/
def clobBits (i : Instr) : Nat :=
  match i with
  | .mul _ => Nat.lor (regBit .rax) (regBit .rdx)
  | .mulx hi lo _ => Nat.lor (regBit hi) (regBit lo)
  | .push _ | .alloc _ | .free _ => regBit .rsp
  | .pop d _ => Nat.lor (regBit .rsp) (regBit d)
  | i => optBit (Taint.dstOf i)

/-- Bit 16: it writes a vector register. -/
def vecBit (i : Instr) : Nat :=
  match writesVec i with
  | true => 65536
  | false => 0

/-- Bits 17 and 18: its level (`vecLevel`) is at least 1, 2. -/
def levelBits (i : Instr) : Nat :=
  match i.vecLevel with
  | 0 => 0
  | 1 => 131072
  | _ => 393216

/-- `levelBits`, but `ldmxcsr`'s is bit 19 alone. -/
def levelMx : Instr → Nat
  | .ldmxcsr _ => 524288
  | i => levelBits i

def bitsFn (i : Instr) : Nat := Nat.lor (clobBits i) (Nat.lor (vecBit i) (levelMx i))

end SideBits

open SideBits VG.Impl.Scrub.X86_64 in
/-- What the side conditions ask of an instruction: its registers' bits, bit 16
if it writes a vector register, bits 17 and 18 if its level is at least 1, 2,
and bit 19 if it loads MXCSR. -/
def sideBits : Instr → Nat :=
  inline_match% bitsFn clobBits optBit Taint.dstOf vecBit writesVec levelMx levelBits Instr.vecLevel

namespace SideBits

open VG.Impl.Scrub.X86_64 (writesVec)

theorem sideBits_eq (i : Instr) : sideBits i = bitsFn i := by cases i <;> rfl

theorem land_eq_zero {a b : Nat} : Nat.beq (Nat.land a b) 0 = true ↔ ∀ n, b.testBit n = true → a.testBit n = false := by
  rw [Nat.beq_eq]
  show a &&& b = 0 ↔ _
  constructor
  · intro h n hb
    have := congrArg (·.testBit n) h
    simp only [Nat.testBit_and, hb, Bool.and_true, Nat.zero_testBit] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro n
    rw [Nat.testBit_and, Nat.zero_testBit]
    cases hb : b.testBit n with
    | false => exact Bool.and_false _
    | true => rw [h n hb]; rfl

theorem idx_inj {a b : Reg} (h : a.ctorIdx = b.ctorIdx) : a = b := by
  rw [← Reg.ofNat_ctorIdx a, h, Reg.ofNat_ctorIdx]

theorem idx_lt (r : Reg) : r.ctorIdx < 16 := by cases r <;> decide

theorem testBit_regBit (r : Reg) (n : Nat) : (regBit r).testBit n = decide (r.ctorIdx = n) := by
  show (2 ^ r.ctorIdx).testBit n = _
  exact Nat.testBit_two_pow

theorem testBit_regBit_reg (r q : Reg) : (regBit r).testBit q.ctorIdx = (q == r) := by
  rw [testBit_regBit, Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]
  exact ⟨fun h => (idx_inj h).symm, fun h => by rw [h]⟩

theorem testBit_lor (a b n : Nat) : (Nat.lor a b).testBit n = (a.testBit n || b.testBit n) := Nat.testBit_or ..

theorem testBit_optBit (o : Option Reg) (q : Reg) : (optBit o).testBit q.ctorIdx = (o == some q) := by
  cases o with
  | none => exact Nat.zero_testBit _
  | some r =>
    rw [optBit, testBit_regBit_reg, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    exact ⟨fun h => by rw [h], fun h => (Option.some.inj h).symm⟩

theorem testBit_clobBits (i : Instr) (q : Reg) : (clobBits i).testBit q.ctorIdx = Taint.clobbers i q := by
  unfold clobBits Taint.clobbers
  split <;> simp only [testBit_lor, testBit_regBit_reg, testBit_optBit]

theorem optBit_high (o : Option Reg) {n : Nat} (hn : 16 ≤ n) : (optBit o).testBit n = false := by
  cases o with
  | none => exact Nat.zero_testBit _
  | some r => rw [optBit, testBit_regBit]; have := idx_lt r; exact decide_eq_false (by omega_using [this, hn])

theorem clobBits_high (i : Instr) {n : Nat} (hn : 16 ≤ n) : (clobBits i).testBit n = false := by
  have h (r : Reg) : (regBit r).testBit n = false := optBit_high (some r) hn
  unfold clobBits
  split <;> simp only [testBit_lor, h, optBit_high _ hn, Bool.or_self]

theorem testBit_levelMx (i : Instr) : ∀ n, n < 16 ∨ n = 16 → (levelMx i).testBit n = false := by
  have h (i : Instr) (n : Nat) (hn : n < 16 ∨ n = 16) : (levelBits i).testBit n = false := by
    unfold levelBits
    split
    · exact Nat.zero_testBit n
    · show (2 ^ 17).testBit n = false
      rw [Nat.testBit_two_pow]; exact decide_eq_false (by omega_using [hn])
    · have : ∀ n < 17, (393216 : Nat).testBit n = false := by decide
      exact this n (by omega_using [hn])
  intro n hn
  unfold levelMx
  split
  · show (2 ^ 19).testBit n = false
    rw [Nat.testBit_two_pow]; exact decide_eq_false (by omega_using [hn])
  · exact h _ n hn

theorem levelR_le (i : Instr) : i.vecLevelR ≤ 2 := by
  unfold Instr.vecLevelR Instr.vecLevel; split
  · decide
  · split <;> decide

theorem testBit_level (i : Instr) : (levelMx i).testBit 17 = decide (1 ≤ i.vecLevelR) ∧
    (levelMx i).testBit 18 = decide (2 ≤ i.vecLevelR) ∧ (levelMx i).testBit 19 = loadsMxcsr i := by
  have b0 : ∀ n, (0 : Nat).testBit n = false := Nat.zero_testBit
  have b1 : (131072 : Nat).testBit 17 = true ∧ (131072 : Nat).testBit 18 = false ∧
      (131072 : Nat).testBit 19 = false := by decide
  have b2 : (393216 : Nat).testBit 17 = true ∧ (393216 : Nat).testBit 18 = true ∧
      (393216 : Nat).testBit 19 = false := by decide
  have b3 : (524288 : Nat).testBit 17 = false ∧ (524288 : Nat).testBit 18 = false ∧
      (524288 : Nat).testBit 19 = true := by decide
  unfold Instr.vecLevelR
  cases hm : loadsMxcsr i with
  | true =>
    have hi : levelMx i = 524288 := by
      unfold loadsMxcsr at hm
      split at hm
      · rfl
      · cases hm
    rw [hi, ite_eq_left rfl]; exact b3
  | false =>
    have hi : levelMx i = levelBits i := by
      unfold levelMx
      split
      · cases hm
      · rfl
    rw [hi, ite_eq_right (by decide)]
    have hl : i.vecLevel ≤ 2 := by unfold Instr.vecLevel; split <;> decide
    unfold levelBits
    split
    · rename_i h; rw [h]; exact ⟨b0 _, b0 _, b0 _⟩
    · rename_i h; rw [h]; exact b1
    · rename_i h0 h1
      obtain h : i.vecLevel = 2 := by omega_using [hl, h0, h1]
      rw [h]; exact b2

theorem testBit_vecBit (i : Instr) (n : Nat) : (vecBit i).testBit n = (decide (n = 16) && writesVec i) := by
  unfold vecBit
  split
  · rename_i h
    show (2 ^ 16).testBit n = _
    rw [Nat.testBit_two_pow, h, Bool.and_true]
    exact decide_eq_decide.mpr eq_comm
  · rename_i h; rw [h, Bool.and_false]; exact Nat.zero_testBit n

theorem testBit_reg (i : Instr) (q : Reg) : (sideBits i).testBit q.ctorIdx = Taint.clobbers i q := by
  have hq := idx_lt q
  rw [sideBits_eq, bitsFn, testBit_lor, testBit_lor, testBit_clobBits, testBit_vecBit,
    testBit_levelMx i _ (.inl hq), decide_eq_false (by omega_using [hq]), Bool.false_and, Bool.or_false,
    Bool.or_false]

theorem testBit_vec (i : Instr) : (sideBits i).testBit 16 = writesVec i := by
  rw [sideBits_eq, bitsFn, testBit_lor, testBit_lor, clobBits_high i (by decide), testBit_vecBit,
    testBit_levelMx i _ (.inr rfl), Bool.false_or, Bool.or_false]; rfl

theorem testBit_lv (i : Instr) : (sideBits i).testBit 17 = decide (1 ≤ i.vecLevelR) ∧
    (sideBits i).testBit 18 = decide (2 ≤ i.vecLevelR) ∧ (sideBits i).testBit 19 = loadsMxcsr i := by
  have h := testBit_level i
  have e (n : Nat) (hn : 17 ≤ n) : (sideBits i).testBit n = (levelMx i).testBit n := by
    rw [sideBits_eq, bitsFn, testBit_lor, testBit_lor, clobBits_high i (by omega_using [hn]), testBit_vecBit,
      decide_eq_false (by omega_using [hn]), Bool.false_and, Bool.false_or, Bool.false_or]
  exact ⟨(e 17 (by decide)).trans h.1, (e 18 (by decide)).trans h.2.1, (e 19 (by decide)).trans h.2.2⟩

/-- The bits of a level above `k`. -/
def levelMask (k : Nat) : Nat := Nat.lor (if k < 1 then 131072 else 0) (if k < 2 then 262144 else 0)

theorem testBit_levelMask (k n : Nat) : (levelMask k).testBit n =
    (decide (n = 17) && decide (k < 1) || decide (n = 18) && decide (k < 2)) := by
  have h1 : (131072 : Nat).testBit n = decide (n = 17) := by
    show (2 ^ 17).testBit n = _; rw [Nat.testBit_two_pow]; exact decide_eq_decide.mpr eq_comm
  have h2 : (262144 : Nat).testBit n = decide (n = 18) := by
    show (2 ^ 18).testBit n = _; rw [Nat.testBit_two_pow]; exact decide_eq_decide.mpr eq_comm
  rw [levelMask, testBit_lor]
  by_cases a : k < 1 <;> by_cases b : k < 2 <;> simp only [a, b, ite_true, ite_false, h1, h2, Nat.zero_testBit,
    decide_true, decide_false, Bool.and_true, Bool.and_false]

/-- The registers' bits. -/
def regsMask (rs : List Reg) : Nat := rs.foldr (fun r acc => Nat.lor (regBit r) acc) 0

theorem testBit_regsMask (rs : List Reg) (n : Nat) :
    (regsMask rs).testBit n = true ↔ ∃ r ∈ rs, r.ctorIdx = n := by
  induction rs with
  | nil =>
    have e : (regsMask []).testBit n = false := Nat.zero_testBit n
    rw [e]
    exact ⟨fun h => (Bool.false_ne_true h).elim, fun ⟨_, h, _⟩ => (List.not_mem_nil h).elim⟩
  | cons r rs ih =>
    rw [regsMask, List.foldr_cons, testBit_lor, Bool.or_eq_true, testBit_regBit, decide_eq_true_iff]
    rw [regsMask] at ih
    rw [ih]
    simp only [List.mem_cons, exists_eq_or_imp]

/-- The instruction has none of the bits `m`. -/
def none (m : Nat) (i : Instr) : Bool := Nat.beq (Nat.land (sideBits i) m) 0

theorem none_or (a b : Nat) (i : Instr) : none (Nat.lor a b) i = (none a i && none b i) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, none, none, none, land_eq_zero, land_eq_zero, land_eq_zero]
  simp only [testBit_lor, Bool.or_eq_true]
  exact ⟨fun h => ⟨fun n hn => h n (.inl hn), fun n hn => h n (.inr hn)⟩, fun h n hn => hn.elim (h.1 n) (h.2 n)⟩

theorem none_level (k : Nat) (i : Instr) : none (levelMask k) i = decide (i.vecLevelR ≤ k) := by
  rw [Bool.eq_iff_iff, none, land_eq_zero, decide_eq_true_iff]
  obtain ⟨h1, h2, _⟩ := testBit_lv i
  have hl := levelR_le i
  simp only [testBit_levelMask, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    have a1 : k < 1 → ¬ 1 ≤ i.vecLevelR := fun hk => of_decide_eq_false (h1.symm.trans (h 17 (.inl ⟨rfl, hk⟩)))
    have a2 : k < 2 → ¬ 2 ≤ i.vecLevelR := fun hk => of_decide_eq_false (h2.symm.trans (h 18 (.inr ⟨rfl, hk⟩)))
    omega_using [a1, a2, hl]
  · rintro h n (⟨rfl, hk⟩ | ⟨rfl, hk⟩)
    · rw [h1]; exact decide_eq_false (by omega_using [h, hk])
    · rw [h2]; exact decide_eq_false (by omega_using [h, hk])

theorem none_mx (i : Instr) : none 524288 i = !loadsMxcsr i := by
  rw [Bool.eq_iff_iff, none, land_eq_zero, ← (testBit_lv i).2.2, Bool.not_eq_true']
  have e (n : Nat) : (524288 : Nat).testBit n = true ↔ n = 19 := by
    show (2 ^ 19).testBit n = true ↔ _
    rw [Nat.testBit_two_pow, decide_eq_true_iff]; exact eq_comm
  simp only [e, forall_eq]

theorem none_vec (i : Instr) : none 65536 i = !writesVec i := by
  rw [Bool.eq_iff_iff, none, land_eq_zero, ← testBit_vec i, Bool.not_eq_true']
  have e (n : Nat) : (65536 : Nat).testBit n = true ↔ n = 16 := by
    show (2 ^ 16).testBit n = true ↔ _
    rw [Nat.testBit_two_pow, decide_eq_true_iff]; exact eq_comm
  simp only [e, forall_eq]

theorem none_regs (rs : List Reg) (i : Instr) : none (regsMask rs) i = rs.all fun r => !Taint.clobbers i r := by
  rw [Bool.eq_iff_iff, none, land_eq_zero, List.all_eq_true]
  simp only [testBit_regsMask, Bool.not_eq_true', ← testBit_reg i]
  exact ⟨fun h r hr => h _ ⟨r, hr, rfl⟩, fun h n ⟨r, hr, e⟩ => e ▸ h r hr⟩

theorem none_zero (i : Instr) : none 0 i = true := by
  rw [none, land_eq_zero]; intro n h; rw [Nat.zero_testBit] at h; cases h

end SideBits

/-- The instruction's level is at most `k`, it writes no vector register
unless `vec`, and none of the registers `kept`. -/
def sideOk (k : Nat) (vec : Bool) (kept : List Reg) : Instr → Bool :=
  SideBits.none (Nat.lor (SideBits.levelMask k)
    (Nat.lor (bif vec then 0 else 65536) (SideBits.regsMask kept)))

open VG.Impl.Scrub.X86_64 in
theorem sideOk_eq (k : Nat) (vec : Bool) (kept : List Reg) : sideOk k vec kept = fun i =>
    decide (i.vecLevelR ≤ k) && (vec || !writesVec i) && kept.all fun r => !Taint.clobbers i r := by
  funext i
  rw [sideOk, SideBits.none_or, SideBits.none_or, SideBits.none_level, SideBits.none_regs, Bool.and_assoc]
  cases vec
  · rw [Bool.cond_false, SideBits.none_vec, Bool.false_or]
  · rw [Bool.cond_true, SideBits.none_zero, Bool.true_or]

end VG.X86_64
