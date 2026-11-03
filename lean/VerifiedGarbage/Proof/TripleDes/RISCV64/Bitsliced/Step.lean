module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Machine
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Sbox
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Pass
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit
meta import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
meta import VerifiedGarbage.Proof.TripleDes.RISCV64.Bitsliced.Machine
meta import VerifiedGarbage.Proof.TripleDes.Bitslice.Pass

/-!
# One S-box of a bitsliced round on RISC-V, and the exchange of the halves

`sboxStep_ok`: the code of S-box `j` (its inputs, the key's bits `inBit j i`
of `a5` as masks XORed with the words of `E`; its circuit; XORing its
outputs into their words) does to the state words what `step` does.
`swapHalves_ok`: the exchange of the halves does what `swapW` does.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Bitsliced

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.TripleDes.RISCV64.Bitslice
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step sboxIn sboxOut outIdx partner swapW)

theorem runBlock_cat_some {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  rw [VG.Interleave.runBlock_append, h₁, Option.bind_some, h₂]

/-- The all-zero or all-one word. -/
def maskVal (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

/-- Bit `c` of `q` shifted to the top and arithmetically back. -/
theorem bit_mask (q : BitVec 64) {c : Nat} (hc : c < 64) :
    (q <<< (63 - c)).sshiftRight 63 = maskVal (q.getLsbD c) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last]
  have key : (q <<< (63 - c)).getLsbD 63 = q.getLsbD c := by
    rw [BitVec.getLsbD_shiftLeft]
    simp only [show (63 : Nat) < 64 by decide, decide_true, Bool.true_and,
      show ¬ (63 < 63 - c) by omega, decide_false, Bool.not_false, show 63 - (63 - c) = c by omega]
  rw [show (if 63 + i < 64 then (q <<< (63 - c)).getLsbD (63 + i) else (q <<< (63 - c)).getLsbD (64 - 1)) =
    (q <<< (63 - c)).getLsbD 63 by split; (congr 1; omega); rfl, key]
  unfold maskVal
  cases q.getLsbD c
  · simp
  · simp only [ite_true, BitVec.getLsbD_allOnes, hi, decide_true, show ¬ 64 ≤ i by omega, decide_false,
      Bool.not_false, Bool.and_true]

theorem getLsbD_mask (b : Bool) {p : Nat} (hp : p < 64) : (maskVal b).getLsbD p = b := by
  cases b
  · simp [maskVal]
  · simp only [maskVal, ite_true, BitVec.getLsbD_allOnes, hp, decide_true]

/-! ## Inputs -/

theorem inReg_ne : ∀ i < 6, inReg i ≠ .a5 ∧ inReg i ≠ .a6 ∧ inReg i ≠ .s0 ∧ inReg i ≠ .a1 ∧
    inReg i ≠ .a2 ∧ inReg i ≠ .a3 ∧ inReg i ≠ .a4 := by decide

theorem inReg_inj : ∀ a < 6, ∀ b < 6, inReg a = inReg b → a = b := by decide

theorem slot_al {s : State} (h : Room s) {w : Nat} (hw : w < 64) :
    (s.gpr .s0 + BitVec.ofNat 64 (stOff w)).toNat % 8 = 0 :=
  wordAddr_al h.al w (by omega)

theorem slot_rd {s : State} (h : Room s) {w : Nat} (hw : w < 64) :
    InRegions (s.rd ++ s.wr) (s.gpr .s0 + BitVec.ofNat 64 (stOff w)) 8 :=
  let ⟨r, hr, hc⟩ := slot_in h (k := w) (by omega); ⟨r, List.mem_append_right _ hr, hc⟩

/-- One input into `q`: key bit `b` of `a5` as a mask, XORed with state word `w`. -/
theorem inputStep_run' {s : State} (h : Room s) {q : Reg} (h6 : q ≠ .a6) (h0 : q ≠ .s0)
    {b w : Nat} (hb : b < 48) (hw : w < 64) :
    ∃ s', runBlock isa [.shift .sll .d q key (63 - b), .shift .sra .d q q 63,
        .load .d tmp base (stOff w), .logic .xor q q tmp] s = some s' ∧
      s'.gpr q = maskVal ((s.gpr .a5).getLsbD b) ^^^ sl s w ∧
      (∀ r, r ≠ q → r ≠ .a6 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  let s₁ := s.write q (s.gpr .a5 <<< (63 - b))
  have e₁ : exec (.shift .sll .d q .a5 (63 - b)) s = some s₁ := exec_shift_d (by omega)
  let s₂ := s₁.write q ((s₁.gpr q).sshiftRight 63)
  have e₂ : exec (.shift .sra .d q q 63) s₁ = some s₂ := exec_shift_d (by decide)
  have g0 : s₂.gpr .s0 = s.gpr .s0 := by
    simp only [s₂, s₁, RegUpd.gpr_write, Ne.symm h0, ite_false]
  let s₃ := s₂.write .a6 (s₂.mem.readW (s₂.gpr .s0 + BitVec.ofNat 64 (stOff w)) 64)
  have e₃ : exec (.load .d .a6 .s0 (stOff w)) s₂ = some s₃ :=
    exec_load_d (by unfold stOff; omega) (by rw [g0]; exact slot_al h hw) (by rw [g0]; exact slot_rd h hw)
  let s₄ := s₃.write q (s₃.gpr q ^^^ s₃.gpr .a6)
  have e₄ : exec (.logic .xor q q .a6) s₃ = some s₄ := exec_logic
  refine ⟨s₄, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  · rw [runBlock_cons, show key = .a5 from rfl, e₁, runStep_some, runBlock_cons, e₂, runStep_some,
      runBlock_cons, show base = .s0 from rfl, show tmp = .a6 from rfl, e₃, runStep_some, runBlock_cons, e₄,
      runStep_some, runBlock_nil]
  · have g0' : s₂.mem = s.mem := rfl
    simp only [s₄, s₃, RegUpd.gpr_write, ite_true, h6, ite_false, g0, g0']
    simp only [s₂, s₁, RegUpd.gpr_write, ite_true]
    rw [bit_mask _ (by omega)]
    rfl
  · simp only [s₄, s₃, s₂, s₁, RegUpd.gpr_write, h1, h2, ite_false]

/-- One input: key bit `b` of `a5` as a mask, XORed with state word `w`. -/
theorem inputStep_run {s : State} (h : Room s) {i : Nat} (hi : i < 6) {b w : Nat} (hb : b < 48)
    (hw : w < 64) :
    ∃ s', runBlock isa [.shift .sll .d (inReg i) key (63 - b), .shift .sra .d (inReg i) (inReg i) 63,
        .load .d tmp base (stOff w), .logic .xor (inReg i) (inReg i) tmp] s = some s' ∧
      s'.gpr (inReg i) = maskVal ((s.gpr .a5).getLsbD b) ^^^ sl s w ∧
      (∀ r, r ≠ inReg i → r ≠ .a6 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨-, h6, h0, -⟩ := inReg_ne i hi
  exact inputStep_run' h h6 h0 hb hw

def inputsN (ρ : Role) (j n : Nat) : List Instr := (List.range n).flatMap (inputStep ρ j)

theorem inputCode_eq (ρ : Role) (j : Nat) : inputCode ρ j = inputsN ρ j 6 := rfl

theorem inputsN_succ (ρ : Role) (j n : Nat) :
    inputsN ρ j (n + 1) = inputsN ρ j n ++ inputStep ρ j n := by
  simp only [inputsN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem readWord_lt : ∀ ρ : Role, ∀ j < 8, ∀ i < 6, readWord ρ (eBit (inBit j i)) < 64 := by
  intro ρ; cases ρ <;> lit_decide

theorem inputsN_ok (ρ : Role) {j : Nat} (hj : j < 8) {n : Nat} (hn : n ≤ 6) {s : State} (h : Room s) :
    ∃ s', runBlock isa (inputsN ρ j n) s = some s' ∧
      (∀ m < n, s'.gpr (inReg m) = maskVal ((s.gpr .a5).getLsbD (inBit j m)) ^^^
        sl s (readWord ρ (eBit (inBit j m)))) ∧
      (∀ r, (∀ m < n, r ≠ inReg m) → r ≠ .a6 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun m hm => by omega, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, in₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ih (by omega)
    have g0 : s₁.gpr .s0 = s.gpr .s0 := o₁ _ (fun m hm => (inReg_ne m (by omega)).2.2.1.symm) (by decide)
    have g5 : s₁.gpr .a5 = s.gpr .a5 := o₁ _ (fun m hm => (inReg_ne m (by omega)).1.symm) (by decide)
    have h₁ : Room s₁ := h.congr g0 wr₁
    obtain ⟨s₂, run₂, q₂, o₂, m₂, rd₂, wr₂, sp₂⟩ :=
      inputStep_run h₁ (i := n) (by omega) (b := inBit j n) (w := readWord ρ (eBit (inBit j n)))
        (by unfold inBit; omega) (readWord_lt ρ j hj n (by omega))
    refine ⟨s₂, ?_, fun m hm => ?_, fun r hr h6 => ?_, m₂.trans m₁, rd₂.trans rd₁, wr₂.trans wr₁,
      sp₂.trans sp₁⟩
    · rw [inputsN_succ]; exact runBlock_cat_some run₁ run₂
    · by_cases he : m = n
      · subst he
        rw [q₂, g5]
        simp only [sl, m₁, g0]
      · have hne : inReg m ≠ inReg n := by
          intro e; exact he (inReg_inj _ (by omega) _ (by omega) e)
        rw [o₂ _ hne (inReg_ne m (by omega)).2.1, in₁ m (by omega)]
    · rw [o₂ _ (hr n (by omega)) h6, o₁ _ (fun m hm => hr m (by omega)) h6]

/-! ## Outputs -/

/-- S-box `j`'s output registers. -/
def outRegs (j : Nat) : List Reg := (List.range 4).map (outReg j)

def outPost (ρ : Role) (j : Nat) (e : Env Nat) : Bool :=
  (List.range 64).all fun k => e.slot k ==
    some (match outIdx ρ j k with
      | some i => 2 ^ k ^^^ 2 ^ (64 + i)
      | none => 2 ^ k)

theorem output_check : ∀ ρ : Role, ∀ j < 8,
    check (vars 64) varsCfg (fun _ => none) (outputCode ρ j) (varEnv (outRegs j)) (outPost ρ j) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem outIdx_lt (ρ : Role) (j x i : Nat) (h : outIdx ρ j x = some i) : i < 4 := by
  have := List.mem_of_find?_eq_some h
  simpa using this

/-- What the outputs' code writes: `a6`. -/
theorem outputCode_dst : ∀ ρ : Role, ∀ j < 8,
    ((outputCode ρ j).all fun i => dst i == none || dst i == some .a6) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem outputs_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) :
    ∃ s', runBlock isa (outputCode ρ j) s = some s' ∧
      (∀ k < 64, sl s' k = match outIdx ρ j k with
        | some i => sl s k ^^^ s.gpr (outReg j i)
        | none => sl s k) ∧
      (∀ r, r ≠ .a6 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [stR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun (outRegs j) (output_check ρ j hj) h
  simp only [outPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  refine ⟨s', hrun, fun k hk => ?_, fun r hr => p.other r ?_, p.rd, p.wr, p.sp, p.frame⟩
  · rw [varRel_slot p.rel hk (hpost k hk)]
    split
    · rename_i i hi
      have hi4 := outIdx_lt ρ j k i hi
      rw [xorSet_two_pow_xor (by simp [varN, outRegs]; omega) (by simp [varN, outRegs]; omega)]
      have e1 : ¬ 64 + i < 64 := by omega
      simp only [varVals, hk, ite_true, e1, ite_false, Nat.add_sub_cancel_left, outRegs]
      simp [List.getD_eq_getElem?_getD, hi4]
    · rw [xorSet_two_pow _ (by simp [varN]; omega)]
      simp only [varVals, hk, ite_true]
  · have hd := List.all_eq_true.mp (outputCode_dst ρ j hj)
    have : (outputCode ρ j).all (fun i => dst i != some r) = true := List.all_eq_true.mpr fun i hi => by
      have := hd i hi
      simp only [Bool.or_eq_true, beq_iff_eq] at this
      rcases this with e | e <;> rw [e] <;> simp [Ne.symm hr]
    simp [this]

/-! ## One S-box -/

/-- The registers an S-box step leaves alone. -/
def stepKept : List Reg := [.s0, .a1, .a2, .a3, .a4, .a5]

theorem stepKept_in : ∀ r ∈ stepKept, r ∈ sboxKept ∧ r ≠ .a6 ∧ ∀ m < 6, r ≠ inReg m := by decide

theorem sboxStep_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) (k : BitVec 48)
    (hkey : ∀ b < 48, (s.gpr .a5).getLsbD b = k.getLsbD b) :
    ∃ s', runBlock isa (sboxStep ρ j) s = some s' ∧
      (∀ x < 64, words s' x = step ρ k j (words s) x) ∧
      (∀ r ∈ stepKept, s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [stR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, in₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := inputsN_ok ρ hj (Nat.le_refl 6) h
  obtain ⟨s₂, run₂, out₂, rd₂, wr₂, sp₂, m₂, o₂⟩ := sbox_ok j hj s₁
  have k₂ : ∀ r ∈ stepKept, s₂.gpr r = s.gpr r := fun r hr => by
    obtain ⟨hs, h6, hm⟩ := stepKept_in r hr
    rw [o₂ r hs, o₁ r hm h6]
  have g0 : s₂.gpr .s0 = s.gpr .s0 := k₂ _ (by decide)
  have h₂ : Room s₂ := h.congr g0 (wr₂.trans wr₁)
  obtain ⟨s₃, run₃, sl₃, o₃, rd₃, wr₃, sp₃, f₃⟩ := outputs_ok ρ hj h₂
  have sl₂ : ∀ x, sl s₂ x = sl s x := fun x => by simp only [sl, m₂, m₁, g0]
  have hin : ∀ i < 6, s₁.gpr (inReg i) =
      maskVal (k.getLsbD (inBit j i)) ^^^ sl s (readWord ρ (eBit (inBit j i))) := by
    intro i hi
    rw [in₁ i hi, hkey _ (by unfold inBit; omega)]
  refine ⟨s₃, ?_, fun x hx => ?_, fun r hr => ?_, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁), ?_⟩
  · rw [sboxStep, inputCode_eq]; exact runBlock_cat_some (runBlock_cat_some run₁ run₂) run₃
  · simp only [words]
    rw [sl₃ _ hx]
    simp only [VG.Proof.TripleDes.Bitslice.step]
    rcases hidx : outIdx ρ j x with _ | i
    · exact sl₂ x
    · have hi4 := outIdx_lt ρ j x i hidx
      dsimp only
      rw [sl₂ x]
      congr 1
      apply BitVec.eq_of_getLsbD_eq
      intro p hp
      rw [out₂ i hi4 p hp]
      simp only [sboxOut, getLsbD_ofBits, hp, decide_true, Bool.true_and]
      congr 2
      apply BitVec.eq_of_getLsbD_eq
      intro i' hi'
      simp only [inputAt, sboxIn, getLsbD_ofBits, hi', decide_true, Bool.true_and, hin i' hi',
        BitVec.getLsbD_xor, getLsbD_mask _ hp]
      rw [Bool.xor_comm]
  · rw [o₃ r (stepKept_in r hr).2.1, k₂ r hr]
  · have : stR s₂ = stR s := by simp only [stR, g0]
    rw [this] at f₃
    rw [show s₂.mem = s.mem from m₂.trans m₁] at f₃
    exact f₃

/-! ## The exchange of the halves -/

/-- The word that goes into word `k`. -/
def swapSlot (k : Nat) : Nat := match partner k with | some y => y | none => k

def swapPost (e : Env Nat) : Bool :=
  (List.range 64).all fun k => e.slot k == some (2 ^ swapSlot k)

theorem swap_check :
    check (vars 64) varsCfg (fun _ => none) swapHalves (varEnv []) swapPost = true := by
  lit_decide

theorem swapSlot_lt : ∀ k < 64, swapSlot k < 64 := by lit_decide

theorem swapHalves_dst : (swapHalves.all fun i => dst i == none || dst i == some .t0 ||
    dst i == some .t1) = true := by lit_decide

theorem swapHalves_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa swapHalves s = some s' ∧ (∀ x < 64, words s' x = swapW (words s) x) ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [stR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun [] swap_check h
  simp only [swapPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  have key : ∀ k < 64, sl s' k = sl s (swapSlot k) := by
    intro k hk
    rw [varRel_slot p.rel hk (hpost k hk), xorSet_two_pow _ (by simp [varN]; exact swapSlot_lt k hk)]
    simp only [varVals, swapSlot_lt k hk, ite_true]
  refine ⟨s', hrun, fun x hx => ?_, fun r h0 h1 => p.other r ?_, p.rd, p.wr, p.sp, p.frame⟩
  · simp only [words]
    rw [key _ hx]
    simp only [swapW, swapSlot]
    rcases partner x with _ | y <;> rfl
  · have hd := List.all_eq_true.mp swapHalves_dst
    have : swapHalves.all (fun i => dst i != some r) = true := List.all_eq_true.mpr fun i hi => by
      have := hd i hi
      simp only [Bool.or_eq_true, beq_iff_eq] at this
      rcases this with (e | e) | e <;> rw [e] <;> simp [Ne.symm h0, Ne.symm h1]
    simp [this]

end VG.Proof.TripleDes.RISCV64.Bitsliced
