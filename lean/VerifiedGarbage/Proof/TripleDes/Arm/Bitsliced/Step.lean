module

public import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.Machine
public import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.Sbox
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Pass
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
meta import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.Machine
meta import VerifiedGarbage.Proof.TripleDes.Arm.Bitsliced.Sbox
meta import VerifiedGarbage.Proof.TripleDes.Bitslice.Pass

/-!
# One S-box of a bitsliced round on ARMv7, and the exchange of the halves

`sboxStep_ok`: the code of S-box `j` (the round key's words, in words 72 and
73 of the working space, into `r0` and `r1`; its inputs, the key's bits
`inBit j i` as masks XORed with the words of `E`; its circuit; XORing its
outputs into their words) does to the state words what `step` does, and
writes only the spilled words and the state words. `swapHalves_ok`: the
exchange of the halves does what `swapW` does.
-/

@[expose] public section

namespace VG.Proof.TripleDes.Arm.Bitsliced

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.TripleDes.Arm.Bitslice
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step sboxIn sboxOut outIdx partner swapW)
open VG.Proof.X25519.Arm (dpVal op2_imm op2_reg op2_lsr)

/-- The all-zero or all-one word. -/
def maskVal (b : Bool) : BitVec 32 := if b then BitVec.allOnes 32 else 0

/-- Bit `c` of `x`, isolated and shifted down. -/
theorem bit_iso (x : BitVec 32) {c : Nat} (hc : c < 32) :
    (x &&& BitVec.ofNat 32 (2 ^ c)) >>> c = if x.getLsbD c then 1#32 else 0#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
  by_cases h0 : i = 0
  · subst h0
    rw [Nat.add_zero, decide_eq_true hc, decide_eq_true rfl, Bool.and_self, Bool.and_true]
    cases x.getLsbD c <;> rfl
  · rw [decide_eq_false (by omega_using [h0] : ¬ c = c + i), Bool.and_false, Bool.and_false]
    have h2 : (1#32).getLsbD i = false := by
      rw [BitVec.getLsbD_one, decide_eq_false h0, Bool.and_false]
    cases x.getLsbD c
    · exact (BitVec.getLsbD_zero).symm
    · exact h2.symm

/-- Bit `c` of `x`, isolated, shifted down and subtracted from zero. -/
theorem bit_mask (x : BitVec 32) {c : Nat} (hc : c < 32) :
    0#32 - ((x &&& BitVec.ofNat 32 (2 ^ c)) >>> c) = maskVal (x.getLsbD c) := by
  rw [bit_iso x hc, maskVal]
  cases x.getLsbD c <;> decide

theorem getLsbD_mask (b : Bool) {p : Nat} (hp : p < 32) : (maskVal b).getLsbD p = b := by
  cases b
  · simp [maskVal]
  · simp only [maskVal, ite_true, BitVec.getLsbD_allOnes, hp, decide_true]

theorem pow_encodable : ∀ c < 32, encodable (BitVec.ofNat 32 (2 ^ c)) = true := by decide

theorem shrOp_eval (s : State) (r : Reg) {c : Nat} (hc : c < 32) :
    (shrOp r c).eval s = some (s.gpr r >>> c) := by
  unfold shrOp
  split
  · rename_i h; subst h; rw [op2_reg, BitVec.ushiftRight_zero]
  · rename_i h; exact op2_lsr ⟨by omega_using [h], by omega_using [hc]⟩

/-! ## Inputs -/

theorem inReg_ne : ∀ i < 6, inReg i ≠ .r3 ∧ inReg i ≠ .r2 ∧ inReg i ≠ .r10 ∧ inReg i ≠ .r0 ∧
    inReg i ≠ .r1 := by decide

theorem inReg_inj : ∀ a < 6, ∀ b < 6, inReg a = inReg b → a = b := by decide

/-- The round key's words and zero. -/
theorem keyRegs_run {s : State} (h : Room s) :
    ∃ s', runBlock isa keyRegs s = some s' ∧ s'.gpr .r0 = fw s 72 ∧ s'.gpr .r1 = fw s 73 ∧
      s'.gpr .r2 = 0 ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e₁ := exec_ldr (s := s) (t := .r0) (n := .r3) (off := kloOff) (by decide) (slot_rd h (by decide))
  let s₁ := s.setReg .r0 (s.mem.readW (State.addr (s.gpr .r3 + BitVec.ofNat 32 kloOff)) 32)
  have e₂ := exec_ldr (s := s₁) (t := .r1) (n := .r3) (off := khiOff) (by decide) (slot_rd h (by decide))
  let s₂ := s₁.setReg .r1 (s₁.mem.readW (State.addr (s₁.gpr .r3 + BitVec.ofNat 32 khiOff)) 32)
  have e₃ := exec_mov (s := s₂) (d := .r2) (o := .imm 0) (op2_imm (by decide))
  refine ⟨s₂.setReg .r2 0, ?_, rfl, rfl, rfl, fun r h0 h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  · rw [keyRegs, runBlock_cons, show klo = .r0 from rfl, show base = .r3 from rfl, e₁, runStep_some,
      runBlock_cons, show khi = .r1 from rfl, e₂, runStep_some, runBlock_cons, show zero = .r2 from rfl,
      e₃, runStep_some, runBlock_nil]
  · simp only [s₂, s₁, RegUpd.gpr_setReg, h0, h1, h2, ite_false]

/-- One input into `q`: bit `c` of `kr` as a mask, XORed with the word at `off`. -/
theorem inputAt_run {s : State} (h : Room s) (hz : s.gpr .r2 = 0) {q kr : Reg} (h3 : q ≠ .r3)
    (h2 : q ≠ .r2) (h10 : q ≠ .r10) {c off : Nat} (hc : c < 32) (ho : off + 4 ≤ 1024) :
    ∃ s', runBlock isa (inputAt q kr c off) s = some s' ∧
      s'.gpr q = maskVal ((s.gpr kr).getLsbD c) ^^^
        s.mem.readW (State.addr (s.gpr .r3 + BitVec.ofNat 32 off)) 32 ∧
      (∀ r, r ≠ q → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  have e₁ := exec_dp (s := s) (op := .and) (d := q) (n := kr) (op2_imm (pow_encodable c hc))
  let s₁ := s.setReg q (dpVal .and (s.gpr kr) (BitVec.ofNat 32 (2 ^ c)))
  have e₂ := exec_dp (s := s₁) (op := .sub) (d := q) (n := .r2) (shrOp_eval s₁ q hc)
  let s₂ := s₁.setReg q (dpVal .sub (s₁.gpr .r2) (s₁.gpr q >>> c))
  have g3 : s₂.gpr .r3 = s.gpr .r3 := by
    simp only [s₂, s₁, RegUpd.gpr_setReg, Ne.symm h3, ite_false]
  have e₃ := exec_ldr (s := s₂) (t := .r10) (n := .r3) (off := off) (by omega_using [ho])
    (by rw [g3]; exact slot_rd h ho)
  let s₃ := s₂.setReg .r10 (s₂.mem.readW (State.addr (s₂.gpr .r3 + BitVec.ofNat 32 off)) 32)
  have e₄ := exec_dp (s := s₃) (op := .eor) (d := q) (n := q) (op2_reg s₃ .r10)
  refine ⟨s₃.setReg q (dpVal .eor (s₃.gpr q) (s₃.gpr .r10)), ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl,
    rfl⟩
  · rw [inputAt, runBlock_cons, e₁, runStep_some, runBlock_cons, show zero = .r2 from rfl, e₂,
      runStep_some, runBlock_cons, show tmp = .r10 from rfl, show base = .r3 from rfl, e₃, runStep_some,
      runBlock_cons, e₄, runStep_some, runBlock_nil]
  · have g2 : s₁.gpr .r2 = 0 := by
      simp only [s₁, RegUpd.gpr_setReg, Ne.symm h2, ite_false, hz]
    have gq : s₃.gpr q = maskVal ((s.gpr kr).getLsbD c) := by
      simp only [s₃, RegUpd.gpr_setReg, h10, ite_false]
      simp only [s₂, RegUpd.gpr_setReg_self, g2, dpVal]
      simp only [s₁, RegUpd.gpr_setReg_self, dpVal]
      exact bit_mask _ hc
    have gt : s₃.gpr .r10 = s.mem.readW (State.addr (s.gpr .r3 + BitVec.ofNat 32 off)) 32 := by
      simp only [s₃, RegUpd.gpr_setReg_self, g3]
      rfl
    rw [RegUpd.gpr_setReg_self, gq, gt]
    rfl
  · simp only [s₃, s₂, s₁, RegUpd.gpr_setReg, h1, h2, ite_false]

def inputsN (ρ : Role) (j n : Nat) : List Instr := (List.range n).flatMap (inputStep ρ j)

theorem inputCode_eq (ρ : Role) (j : Nat) : inputCode ρ j = inputsN ρ j 6 := rfl

theorem inputsN_succ (ρ : Role) (j n : Nat) :
    inputsN ρ j (n + 1) = inputsN ρ j n ++ inputStep ρ j n := by
  simp only [inputsN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem readWord_lt : ∀ ρ : Role, ∀ j < 8, ∀ i < 6, readWord ρ (eBit (inBit j i)) < 64 := by
  intro ρ; cases ρ <;> lit_decide

/-- The register of the key word with S-box `j`'s input `m`. -/
def keyReg (j m : Nat) : Reg := if inBit j m < 32 then klo else khi

theorem keyReg_ne (j m : Nat) : ∀ i < 6, keyReg j m ≠ inReg i := by
  unfold keyReg; split <;> decide

theorem inputsN_ok (ρ : Role) {j : Nat} (hj : j < 8) {n : Nat} (hn : n ≤ 6) {s : State} (h : Room s)
    (hz : s.gpr .r2 = 0) :
    ∃ s', runBlock isa (inputsN ρ j n) s = some s' ∧
      (∀ m < n, s'.gpr (inReg m) = maskVal ((s.gpr (keyReg j m)).getLsbD (inBit j m % 32)) ^^^
        words s (readWord ρ (eBit (inBit j m)))) ∧
      (∀ r, (∀ m < n, r ≠ inReg m) → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun m hm => by omega, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, in₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ih (by omega_using [hn])
    have g3 : s₁.gpr .r3 = s.gpr .r3 :=
      o₁ _ (fun m hm => (inReg_ne m (by omega_using [hn, hm])).1.symm) (by decide)
    have g2 : s₁.gpr .r2 = s.gpr .r2 :=
      o₁ _ (fun m hm => (inReg_ne m (by omega_using [hn, hm])).2.1.symm) (by decide)
    have gk : s₁.gpr (keyReg j n) = s.gpr (keyReg j n) :=
      o₁ _ (fun m hm => keyReg_ne j n m (by omega_using [hn, hm])) (by unfold keyReg; split <;> decide)
    have h₁ : Room s₁ := h.congr g3 wr₁
    obtain ⟨i3, i2, i10, -⟩ := inReg_ne n (by omega_using [hn])
    have hw := readWord_lt ρ j hj n (by omega_using [hn])
    obtain ⟨s₂, run₂, q₂, o₂, m₂, rd₂, wr₂, sp₂⟩ :=
      inputAt_run h₁ (g2.trans hz) (q := inReg n) (kr := keyReg j n) i3 i2 i10 (c := inBit j n % 32)
        (off := stOff (readWord ρ (eBit (inBit j n)))) (Nat.mod_lt _ (by decide))
        (by unfold stOff spills; omega_using [hw])
    refine ⟨s₂, ?_, fun m hm => ?_, fun r hr h10 => ?_, m₂.trans m₁, rd₂.trans rd₁, wr₂.trans wr₁,
      sp₂.trans sp₁⟩
    · rw [inputsN_succ]; exact runBlock_cat_some run₁ run₂
    · by_cases he : m = n
      · subst he
        rw [q₂, gk, m₁, g3]
        rfl
      · have hne : inReg m ≠ inReg n := by
          intro e; exact he (inReg_inj _ (by omega_using [hn, hm]) _ (by omega_using [hn]) e)
        rw [o₂ _ hne (inReg_ne m (by omega_using [hn, hm])).2.2.1, in₁ m (by omega_using [hm, he])]
    · rw [o₂ _ (hr n (by omega_using [])) h10, o₁ _ (fun m hm => hr m (by omega_using [hm])) h10]

/-! ## Outputs -/

/-- S-box `j`'s output registers. -/
def outRegs (j : Nat) : List Reg := (List.range 4).map (outReg j)

def outPost (ρ : Role) (j : Nat) (e : Env Nat) : Bool :=
  (List.range 64).all fun k => e.slot (spills + k) ==
    some (match outIdx ρ j k with
      | some i => 2 ^ k ^^^ 2 ^ (64 + i)
      | none => 2 ^ k)

theorem output_check : ∀ ρ : Role, ∀ j < 8,
    check (vars 32) varsCfg (fun _ => none) (outputCode ρ j) (varEnv (outRegs j)) (outPost ρ j) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem outIdx_lt (ρ : Role) (j x i : Nat) (h : outIdx ρ j x = some i) : i < 4 := by
  have := List.mem_of_find?_eq_some h
  simpa using this

theorem outputs_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) :
    ∃ s', runBlock isa (outputCode ρ j) s = some s' ∧
      (∀ k < 64, words s' k = match outIdx ρ j k with
        | some i => words s k ^^^ s.gpr (outReg j i)
        | none => words s k) ∧
      s'.gpr .r3 = s.gpr .r3 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [stR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun (outRegs j) (output_check ρ j hj) h
  simp only [outPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  refine ⟨s', hrun, fun k hk => ?_, p.base, p.rd, p.wr, p.sp, p.frame⟩
  rw [varRel_word p.rel hk (hpost k hk)]
  split
  · rename_i i hi
    have hi4 := outIdx_lt ρ j k i hi
    rw [xorSet_two_pow_xor (by simp [varN, outRegs]; omega_using [hk])
      (by simp [varN, outRegs]; omega_using [hi4])]
    have e1 : ¬ 64 + i < 64 := by omega_using []
    simp only [varVals, hk, ite_true, e1, ite_false, Nat.add_sub_cancel_left, outRegs]
    simp [List.getD_eq_getElem?_getD, hi4]
  · rw [xorSet_two_pow _ (by simp [varN]; omega_using [hk])]
    simp only [varVals, hk, ite_true]

/-! ## One S-box -/

theorem sboxStep_eq (ρ : Role) (j : Nat) :
    sboxStep ρ j = keyRegs ++ (inputsN ρ j 6 ++ (sboxCode j ++ outputCode ρ j)) := by
  simp only [sboxStep, inputCode_eq, List.append_assoc]

/-- The key `k`'s low and high words. -/
structure KeyWords (lo hi : BitVec 32) (k : BitVec 48) : Prop where
  lo : ∀ b < 32, lo.getLsbD b = k.getLsbD b
  hi : ∀ b < 16, hi.getLsbD b = k.getLsbD (32 + b)

theorem sboxStep_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) (k : BitVec 48)
    (hkey : KeyWords (fw s 72) (fw s 73) k) :
    ∃ s', runBlock isa (sboxStep ρ j) s = some s' ∧
      (∀ x < 64, words s' x = step ρ k j (words s) x) ∧ s'.gpr .r3 = s.gpr .r3 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [stR s] s.mem s'.mem := by
  obtain ⟨s₀, run₀, k0, k1, z₀, o₀, m₀, rd₀, wr₀, sp₀⟩ := keyRegs_run h
  have g₀ : s₀.gpr .r3 = s.gpr .r3 := o₀ _ (by decide) (by decide) (by decide)
  have h₀ : Room s₀ := h.congr g₀ wr₀
  obtain ⟨s₁, run₁, in₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := inputsN_ok ρ hj (Nat.le_refl 6) h₀ z₀
  have g₁ : s₁.gpr .r3 = s.gpr .r3 :=
    (o₁ _ (fun m hm => (inReg_ne m hm).1.symm) (by decide)).trans g₀
  have h₁ : Room s₁ := h.congr g₁ (wr₁.trans wr₀)
  obtain ⟨s₂, run₂, out₂, rd₂, wr₂, sp₂, g₂', f₂⟩ := sbox_ok j hj (h₁.ok rfl (by decide) rfl)
  have g₂ : s₂.gpr .r3 = s.gpr .r3 := g₂'.trans g₁
  have h₂ : Room s₂ := h.congr g₂ (wr₂.trans (wr₁.trans wr₀))
  obtain ⟨s₃, run₃, w₃, g₃, rd₃, wr₃, sp₃, f₃⟩ := outputs_ok ρ hj h₂
  have mem₁ : s₁.mem = s.mem := m₁.trans m₀
  have f₂' : Frame [headR s spills] s.mem s₂.mem := by
    have : slotRegion sboxCfg s₁ = headR s spills := by simp only [slotRegion, sboxCfg, headR, g₁]
    rw [this, mem₁] at f₂; exact f₂
  have w₂ : ∀ x < 64, words s₂ x = words s x := fun x hx => by
    simp only [words, fw, g₂]
    exact fw_frame h f₂' (Nat.le_add_right _ _) (by unfold spills; omega_using [hx])
  have kbit : ∀ i < 6, (s₀.gpr (keyReg j i)).getLsbD (inBit j i % 32) = k.getLsbD (inBit j i) := by
    intro i hi
    have hb : inBit j i < 48 := by unfold inBit; omega_using [hi]
    unfold keyReg
    split
    · rename_i hlt
      rw [show klo = .r0 from rfl, k0, Nat.mod_eq_of_lt hlt]; exact hkey.lo _ hlt
    · rename_i hge
      rw [show khi = .r1 from rfl, k1, show inBit j i % 32 = inBit j i - 32 by omega_using [hb, hge],
        hkey.hi _ (by omega_using [hb, hge])]
      congr 1; omega_using [hge]
  have hin : ∀ i < 6, s₁.gpr (inReg i) =
      maskVal (k.getLsbD (inBit j i)) ^^^ words s (readWord ρ (eBit (inBit j i))) := by
    intro i hi
    rw [in₁ i hi, kbit i hi]
    simp only [words, fw, m₀, g₀]
  refine ⟨s₃, ?_, fun x hx => ?_, g₃.trans g₂, rd₃.trans (rd₂.trans (rd₁.trans rd₀)),
    wr₃.trans (wr₂.trans (wr₁.trans wr₀)), sp₃.trans (sp₂.trans (sp₁.trans sp₀)), ?_⟩
  · rw [sboxStep_eq]
    exact runBlock_cat_some run₀ (runBlock_cat_some run₁ (runBlock_cat_some run₂ run₃))
  · rw [w₃ _ hx]
    simp only [VG.Proof.TripleDes.Bitslice.step]
    rcases hidx : outIdx ρ j x with _ | i
    · exact w₂ x hx
    · have hi4 := outIdx_lt ρ j x i hidx
      dsimp only
      rw [w₂ x hx]
      congr 1
      apply BitVec.eq_of_getLsbD_eq
      intro p hp
      rw [out₂ i hi4 p hp]
      simp only [sboxOut, getLsbD_ofBits, hp, decide_true, Bool.true_and]
      congr 2
      apply BitVec.eq_of_getLsbD_eq
      intro i' hi'
      simp only [inputsAt, sboxIn, getLsbD_ofBits, hi', decide_true, Bool.true_and, hin i' hi',
        BitVec.getLsbD_xor, getLsbD_mask _ hp]
      rw [Bool.xor_comm]
  · refine (f₂'.sub fun r hr => ?_).trans (by rw [← stR_congr g₂]; exact f₃)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by unfold spills; omega_using [])⟩

/-! ## The exchange of the halves -/

/-- The word that goes into word `k`. -/
def swapSlot (k : Nat) : Nat := match partner k with | some y => y | none => k

def swapPost (e : Env Nat) : Bool :=
  (List.range 64).all fun k => e.slot (spills + k) == some (2 ^ swapSlot k)

theorem swap_check :
    check (vars 32) varsCfg (fun _ => none) swapHalves (varEnv []) swapPost = true := by
  lit_decide

theorem swapSlot_lt : ∀ k < 64, swapSlot k < 64 := by lit_decide

theorem swapHalves_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa swapHalves s = some s' ∧ (∀ x < 64, words s' x = swapW (words s) x) ∧
      s'.gpr .r3 = s.gpr .r3 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [stR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun [] swap_check h
  simp only [swapPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  have key : ∀ k < 64, words s' k = words s (swapSlot k) := by
    intro k hk
    rw [varRel_word p.rel hk (hpost k hk), xorSet_two_pow _ (by simp [varN]; exact swapSlot_lt k hk)]
    simp only [varVals, swapSlot_lt k hk, ite_true]
  refine ⟨s', hrun, fun x hx => ?_, p.base, p.rd, p.wr, p.sp, p.frame⟩
  rw [key _ hx]
  simp only [swapW, swapSlot]
  rcases partner x with _ | y <;> rfl

end VG.Proof.TripleDes.Arm.Bitsliced
