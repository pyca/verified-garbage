module

public import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.Machine
public import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.Sbox
public import VerifiedGarbage.Proof.TripleDes.Bitslice.Pass
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.TripleDes.Bitslice.LayoutLit
meta import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.Machine
meta import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.Sbox
meta import VerifiedGarbage.Proof.TripleDes.Bitslice.Pass

/-!
# One S-box of a bitsliced round on x86 (32-bit), and the exchange of the halves

As on ARMv7 (`Proof/TripleDes/Arm/Bitsliced/Step.lean`). `sboxStep_ok`: the
code of S-box `j` (its inputs, the key's bits `inBit j i`, from the round
key's words in words `kloSlot` and `khiSlot` of the working space, as masks
XORed with the words of `E`, into the first six words; its circuit; XORing
its outputs into their words) does to the state words what `step` does, and
writes only the circuits' words and the state words. `swapHalves_ok`: the
exchange of the halves does what `swapW` does.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86.Bitsliced

open VG VG.X86 VG.X86.Straight VG.X86.Wp VG.Bitslice VG.Impl.TripleDes.X86.Bitslice
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (step sboxIn sboxOut outIdx partner swapW)

/-- The all-zero or all-one word. -/
def maskVal (b : Bool) : BitVec 32 := if b then BitVec.allOnes 32 else 0

theorem getLsbD_mask (b : Bool) {p : Nat} (hp : p < 32) : (maskVal b).getLsbD p = b := by
  cases b
  · simp [maskVal]
  · simp only [maskVal, ite_true, BitVec.getLsbD_allOnes, hp, decide_true]

/-- The carry of a word added to itself is its top bit. -/
theorem carry_double (x : BitVec 32) : decide (2 ^ 32 ≤ x.toNat + x.toNat) = x.getLsbD 31 := by
  rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  have := x.isLt
  apply decide_eq_decide.mpr
  omega_using [this]

/-- A word of the working space in a state that differs from `s` by a store to another. -/
theorem fw_write {s s' : State} (h : Room s) {k j : Nat} {v : BitVec 32}
    (hm : s'.mem = s.mem.writeW (wordAddr (s.gpr .ebp) k) v) (hb : s'.gpr .ebp = s.gpr .ebp)
    (hk : k < wsWords) (hj : j < wsWords) : fw s' j = if j = k then v else fw s j := by
  rw [← fw_stFw h hk hj v, fw, fw, hb, hm]; rfl

/-! ## Inputs -/

/-- One input: bit `c` of the word in slot `kslot` as a mask, XORed with the
word in slot `st`, into slot `i`. -/
theorem inputAt_wp {s : State} (h : Room s) {kslot c st i : Nat} (hk : kslot < wsWords) (hc : c < 32)
    (hst : st < wsWords) (hi : i < wsWords) :
    WP isa (.block (inputAt kslot c st i)) s fun s' =>
      s'.mem = s.mem.writeW (wordAddr (s.gpr .ebp) i) (maskVal ((fw s kslot).getLsbD c) ^^^ fw s st) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have tail : ∀ (s₂ : State), s₂.cf = some ((fw s kslot).getLsbD c) → s₂.mem = s.mem →
      (∀ r, r ≠ .eax → s₂.gpr r = s.gpr r) → s₂.rd = s.rd → s₂.wr = s.wr →
      WP isa (.block [.alu .sbb .ecx (.reg .ecx), .alu .xor .ecx (.mem (ws st)), .store (ws i) .ecx]) s₂
        fun s' => s'.mem = s.mem.writeW (wordAddr (s.gpr .ebp) i)
            (maskVal ((fw s kslot).getLsbD c) ^^^ fw s st) ∧
          (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    intro s₂ cf₂ m₂ g₂ rd₂ wr₂
    refine wp_sbb_self cf₂ fun s₃ u₃ => ?_
    have b₃ : s₃.gpr .ebp = s.gpr .ebp := by rw [u₃.other _ (by decide), g₂ _ (by decide)]
    refine wp_xorm (B := s.gpr .ebp) b₃ (by rw [u₃.rd, u₃.wr, rd₂, wr₂]; exact slot_rd h hst) fun s₄ u₄ => ?_
    have b₄ : s₄.gpr .ebp = s.gpr .ebp := by rw [u₄.other _ (by decide), b₃]
    refine wp_stm (B := s.gpr .ebp) b₄ (by rw [u₄.wr, u₃.wr, wr₂]; exact slot_in h hi) fun s₅ u₅ =>
      WP.block_nil ⟨?_, fun r h0 h1 => ?_, by rw [u₅.rd, u₄.rd, u₃.rd, rd₂], by rw [u₅.wr, u₄.wr, u₃.wr, wr₂]⟩
    · rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₄.gpr, u₃.gpr, u₃.mem, m₂]
      rfl
    · rw [u₅.gpr, u₄.other _ h1, u₃.other _ h1, g₂ _ h0]
  unfold inputAt
  split
  · rename_i h31
    subst h31
    refine wp_ldm (B := s.gpr .ebp) rfl (slot_rd h hk) fun s₁ u₁ => ?_
    refine wp_add fun s₂ u₂ cf₂ => ?_
    refine tail s₂ ?_ (by rw [u₂.mem, u₁.mem]) (fun r hr => by rw [u₂.other _ hr, u₁.other _ hr])
      (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
    rw [cf₂, carry_double, u₁.gpr]; rfl
  · rename_i h31
    refine wp_ldm (B := s.gpr .ebp) rfl (slot_rd h hk) fun s₁ u₁ => ?_
    refine wp_shr (by omega_using [hc, h31]) fun s₂ u₂ cf₂ => ?_
    refine tail s₂ ?_ (by rw [u₂.mem, u₁.mem]) (fun r hr => by rw [u₂.other _ hr, u₁.other _ hr])
      (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
    rw [cf₂, u₁.gpr, Nat.add_sub_cancel]; rfl

def inputsN (ρ : Role) (j n : Nat) : List Instr := (List.range n).flatMap (inputStep ρ j)

theorem inputCode_eq (ρ : Role) (j : Nat) : inputCode ρ j = inputsN ρ j 6 := rfl

theorem inputsN_succ (ρ : Role) (j n : Nat) :
    inputsN ρ j (n + 1) = inputsN ρ j n ++ inputStep ρ j n := by
  simp only [inputsN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem readWord_lt : ∀ ρ : Role, ∀ j < 8, ∀ i < 6, readWord ρ (eBit (inBit j i)) < 64 := by
  intro ρ; cases ρ <;> lit_decide

/-- The slot of the key word with S-box `j`'s input `m`. -/
def keySlot (j m : Nat) : Nat := if inBit j m < 32 then kloSlot else khiSlot

theorem keySlot_bounds (j m : Nat) : 6 ≤ keySlot j m ∧ keySlot j m < wsWords := by
  unfold keySlot; split <;> decide

/-- The first `n` inputs of S-box `j`, in the first words of the working space. -/
structure Ins (ρ : Role) (j n : Nat) (s s' : State) : Prop where
  ins : ∀ m < n, fw s' m = maskVal ((fw s (keySlot j m)).getLsbD (inBit j m % 32)) ^^^
    words s (readWord ρ (eBit (inBit j m)))
  rest : ∀ k, n ≤ k → k < wsWords → fw s' k = fw s k
  regs : ∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [headR s 6] s.mem s'.mem

theorem inputsN_ok (ρ : Role) {j : Nat} (hj : j < 8) {n : Nat} (hn : n ≤ 6) {s : State} (h : Room s) :
    WP isa (.block (inputsN ρ j n)) s (Ins ρ j n s) := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨fun m hm => by omega, fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [inputsN_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn])) fun s₁ p₁ => ?_
    have b₁ : s₁.gpr .ebp = s.gpr .ebp := p₁.regs _ (by decide) (by decide)
    have h₁ : Room s₁ := h.congr b₁ p₁.wr
    obtain ⟨kb0, kb1⟩ := keySlot_bounds j n
    have hw := readWord_lt ρ j hj n (by omega_using [hn])
    have hst : stSlot (readWord ρ (eBit (inBit j n))) < wsWords := by
      unfold stSlot spills wsWords; omega_using [hw]
    refine WP.mono (inputAt_wp h₁ (kslot := keySlot j n) (c := inBit j n % 32)
      (st := stSlot (readWord ρ (eBit (inBit j n)))) (i := n) kb1 (Nat.mod_lt _ (by decide)) hst
      (by unfold wsWords; omega_using [hn])) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_
    have b₂ : s₂.gpr .ebp = s₁.gpr .ebp := g₂ _ (by decide) (by decide)
    have fwn : ∀ k, k < wsWords → fw s₂ k = if k = n then
        maskVal ((fw s₁ (keySlot j n)).getLsbD (inBit j n % 32)) ^^^
          fw s₁ (stSlot (readWord ρ (eBit (inBit j n)))) else fw s₁ k := fun k hk =>
      fw_write h₁ m₂ b₂ (by unfold wsWords; omega_using [hn]) hk
    refine ⟨fun m hm => ?_, fun k hk hk' => ?_, fun r h0 h1 => by rw [g₂ r h0 h1, p₁.regs r h0 h1],
      rd₂.trans p₁.rd, wr₂.trans p₁.wr, ?_⟩
    · rw [fwn m (by unfold wsWords; omega_using [hn, hm])]
      by_cases he : m = n
      · subst he
        rw [ite_eq_left rfl, p₁.rest _ (by omega_using [kb0, hn]) kb1,
          p₁.rest _ (by unfold stSlot spills; omega_using [hn]) hst]
        rfl
      · rw [ite_eq_right he]; exact p₁.ins m (by omega_using [hm, he])
    · rw [fwn k hk', ite_eq_right (by omega_using [hk]), p₁.rest k (by omega_using [hk]) hk']
    · refine p₁.frame.trans ?_
      rw [m₂, b₁]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (slot_contains _ (by omega_using [hn]) (by have := h.fit; unfold wsWords at this; omega_using [this]))

/-! ## Outputs -/

def outPost (ρ : Role) (j : Nat) (e : Env Nat) : Bool :=
  (List.range 64).all fun k => e.slot (spills + k) ==
    some (match outIdx ρ j k with
      | some i => 2 ^ k ^^^ 2 ^ (64 + i)
      | none => 2 ^ k)

theorem output_check : ∀ ρ : Role, ∀ j < 8,
    check (vars 32) varsCfg (fun _ => none) (outputCode ρ j) (varEnv outRegs) (outPost ρ j) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem output_kept : ∀ ρ : Role, ∀ j < 8,
    ((outputCode ρ j).all fun i => i.dst != some .esp) = true := by
  intro ρ; cases ρ <;> lit_decide

theorem outIdx_lt (ρ : Role) (j x i : Nat) (h : outIdx ρ j x = some i) : i < 4 := by
  have := List.mem_of_find?_eq_some h
  simpa using this

theorem outputs_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) :
    ∃ s', runBlock isa (outputCode ρ j) s = some s' ∧
      (∀ k < 64, words s' k = match outIdx ρ j k with
        | some i => words s k ^^^ s.gpr (outReg i)
        | none => words s k) ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [stR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun outRegs (output_check ρ j hj) h
  simp only [outPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  refine ⟨s', hrun, fun k hk => ?_, p.base, p.other _ (by rw [output_kept ρ j hj]; exact Bool.noConfusion),
    p.rd, p.wr, p.frame⟩
  rw [varRel_word p.rel hk (hpost k hk)]
  split
  · rename_i i hi
    have hi4 := outIdx_lt ρ j k i hi
    rw [xorSet_two_pow_xor (by simp [varN, outRegs]; omega_using [hk])
      (by simp [varN, outRegs]; omega_using [hi4])]
    have e1 : ¬ 64 + i < 64 := by omega_using []
    simp only [varVals, hk, ite_true, e1, ite_false, Nat.add_sub_cancel_left, outReg]
  · rw [xorSet_two_pow _ (by simp [varN]; omega_using [hk])]
    simp only [varVals, hk, ite_true]

/-! ## One S-box -/

theorem sboxStep_eq (ρ : Role) (j : Nat) :
    sboxStep ρ j = inputsN ρ j 6 ++ (sboxCode j ++ outputCode ρ j) := by
  simp only [sboxStep, inputCode_eq, List.append_assoc]

/-- The key `k`'s low and high words. -/
structure KeyWords (lo hi : BitVec 32) (k : BitVec 48) : Prop where
  lo : ∀ b < 32, lo.getLsbD b = k.getLsbD b
  hi : ∀ b < 16, hi.getLsbD b = k.getLsbD (32 + b)

theorem sboxStep_ok (ρ : Role) {j : Nat} (hj : j < 8) {s : State} (h : Room s) (k : BitVec 48)
    (hkey : KeyWords (fw s kloSlot) (fw s khiSlot) k) :
    WP isa (.block (sboxStep ρ j)) s fun s' =>
      (∀ x < 64, words s' x = step ρ k j (words s) x) ∧ s'.gpr .ebp = s.gpr .ebp ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [stR s] s.mem s'.mem := by
  rw [sboxStep_eq, WP.block_append_iff]
  refine WP.mono (inputsN_ok ρ hj (Nat.le_refl 6) h) fun s₁ p₁ => ?_
  have g₁ : s₁.gpr .ebp = s.gpr .ebp := p₁.regs _ (by decide) (by decide)
  have h₁ : Room s₁ := h.congr g₁ p₁.wr
  obtain ⟨s₂, run₂, out₂, rd₂, wr₂, g₂', sp₂, f₂⟩ := sbox_ok j hj (h₁.ok rfl (by decide) rfl)
  have g₂ : s₂.gpr .ebp = s.gpr .ebp := g₂'.trans g₁
  have h₂ : Room s₂ := h.congr g₂ (wr₂.trans p₁.wr)
  obtain ⟨s₃, run₃, w₃, g₃, sp₃, rd₃, wr₃, f₃⟩ := outputs_ok ρ hj h₂
  refine WP.of_runBlock ⟨s₃, runBlock_cat_some run₂ run₃, ?_⟩
  have f₁₂ : Frame [headR s spills] s.mem s₂.mem := by
    have e : slotRegion sboxCfg s₁ = headR s spills := by simp only [slotRegion, sboxCfg, headR, g₁]
    rw [e] at f₂
    exact (headR_mono (by decide) p₁.frame).trans f₂
  have w₂ : ∀ x < 64, words s₂ x = words s x := fun x hx => by
    simp only [words, fw, g₂]
    exact fw_frame h f₁₂ (Nat.le_add_right _ _) (by unfold spills wsWords; omega_using [hx])
  have kbit : ∀ i < 6, (fw s (keySlot j i)).getLsbD (inBit j i % 32) = k.getLsbD (inBit j i) := by
    intro i hi
    have hb : inBit j i < 48 := by unfold inBit; omega_using [hi, hj]
    unfold keySlot
    split
    · rename_i hlt
      rw [Nat.mod_eq_of_lt hlt]; exact hkey.lo _ hlt
    · rename_i hge
      rw [show inBit j i % 32 = inBit j i - 32 by omega_using [hb, hge],
        hkey.hi _ (by omega_using [hb, hge])]
      congr 1; omega_using [hge]
  have hin : ∀ i < 6, fw s₁ i =
      maskVal (k.getLsbD (inBit j i)) ^^^ words s (readWord ρ (eBit (inBit j i))) := by
    intro i hi
    rw [p₁.ins i hi, kbit i hi]
  refine ⟨fun x hx => ?_, g₃.trans g₂, sp₃.trans (sp₂.trans (p₁.regs _ (by decide) (by decide))),
    rd₃.trans (rd₂.trans p₁.rd), wr₃.trans (wr₂.trans p₁.wr), ?_⟩
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
  · refine (f₁₂.sub fun r hr => ?_).trans (by rw [← stR_congr g₂]; exact f₃)
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

theorem swap_kept : (swapHalves.all fun i => i.dst != some .esp) = true := by lit_decide

theorem swapSlot_lt : ∀ k < 64, swapSlot k < 64 := by lit_decide

theorem swapHalves_ok {s : State} (h : Room s) :
    ∃ s', runBlock isa swapHalves s = some s' ∧ (∀ x < 64, words s' x = swapW (words s) x) ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [stR s] s.mem s'.mem := by
  obtain ⟨e', s', hpost, hrun, p⟩ := varsRun [] swap_check h
  simp only [swapPost, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  have key : ∀ k < 64, words s' k = words s (swapSlot k) := by
    intro k hk
    rw [varRel_word p.rel hk (hpost k hk), xorSet_two_pow _ (by simp [varN]; exact swapSlot_lt k hk)]
    simp only [varVals, swapSlot_lt k hk, ite_true]
  refine ⟨s', hrun, fun x hx => ?_, p.base, p.other _ (by rw [swap_kept]; exact Bool.noConfusion), p.rd, p.wr,
    p.frame⟩
  rw [key _ hx]
  simp only [swapW, swapSlot]
  rcases partner x with _ | y <;> rfl

end VG.Proof.TripleDes.X86.Bitsliced
