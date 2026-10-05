import Batteries.Logic
import VerifiedGarbage.Impl.TripleDes.X86.Sbox
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.TripleDes.X86.Block
import VerifiedGarbage.Proof.Framework.X86.Straight
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.Bitslice.Table
import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Impl.TripleDes.X86.Permutation
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc2.X86.Key
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.TripleDes.KeyMemory
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Rc2.X86.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.TripleDes.X86.ExpandKey
import VerifiedGarbage.Impl.TripleDes.X86.Ecb
import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Spec.TripleDes.Contract
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.SboxTable`. -/
section

/-!
The code of the eight S-boxes as literals (`materialize_table`): the
literals of the code that runs them, and the kernel's checks of that code
(`lit_decide`, `taint_decide`), read it rather than run the register
allocator that writes it again.
-/

namespace VG

materialize_table Impl.TripleDes.X86.sboxCode 8

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.RoundLit`. -/
section

namespace VG.Impl.TripleDes.X86
open VG.X86
def input0 : Prog isa := .block (sboxInputBits 0)
materialize_code VG.Impl.TripleDes.X86.input0
def output0 : Prog isa := .block (sboxOutputs 0)
materialize_code VG.Impl.TripleDes.X86.output0
def input1 : Prog isa := .block (sboxInputBits 1)
materialize_code VG.Impl.TripleDes.X86.input1
def output1 : Prog isa := .block (sboxOutputs 1)
materialize_code VG.Impl.TripleDes.X86.output1
def input2 : Prog isa := .block (sboxInputBits 2)
materialize_code VG.Impl.TripleDes.X86.input2
def output2 : Prog isa := .block (sboxOutputs 2)
materialize_code VG.Impl.TripleDes.X86.output2
def input3 : Prog isa := .block (sboxInputBits 3)
materialize_code VG.Impl.TripleDes.X86.input3
def output3 : Prog isa := .block (sboxOutputs 3)
materialize_code VG.Impl.TripleDes.X86.output3
def input4 : Prog isa := .block (sboxInputBits 4)
materialize_code VG.Impl.TripleDes.X86.input4
def output4 : Prog isa := .block (sboxOutputs 4)
materialize_code VG.Impl.TripleDes.X86.output4
def input5 : Prog isa := .block (sboxInputBits 5)
materialize_code VG.Impl.TripleDes.X86.input5
def output5 : Prog isa := .block (sboxOutputs 5)
materialize_code VG.Impl.TripleDes.X86.output5
def input6 : Prog isa := .block (sboxInputBits 6)
materialize_code VG.Impl.TripleDes.X86.input6
def output6 : Prog isa := .block (sboxOutputs 6)
materialize_code VG.Impl.TripleDes.X86.output6
def input7 : Prog isa := .block (sboxInputBits 7)
materialize_code VG.Impl.TripleDes.X86.input7
def output7 : Prog isa := .block (sboxOutputs 7)
materialize_code VG.Impl.TripleDes.X86.output7
end VG.Impl.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Linear`. -/
section

namespace VG.Proof.TripleDes.X86.Linear

open VG VG.X86 VG.X86.Straight VG.Bitslice

/-! ## Words of atoms (as `Framework/Bitslice/Atoms.lean`, for 32-bit words) -/

/-- Input word `i`: bit `t` is atom `32 i + t`. -/
def inWord (i : Nat) : Nat × Nat := (0, mk 32 (fun t => [32 * i + t]) 32)

/-- The word whose bit `p` is the XOR of the atoms `g p`. -/
def outWord (g : Nat → List Nat) : Nat × Nat := (0, mk 32 g 32)

/-- Bit `a % 32` of word `a / 32`. -/
def bitOf (W : Nat → BitVec 32) (a : Nat) : Bool := (W (a / 32)).getLsbD (a % 32)

/-- The XOR of the bits `l` of the words `W`. -/
def xorBits (W : Nat → BitVec 32) (l : List Nat) : Bool := l.foldr (fun a b => VG.Proof.TripleDes.X86.Linear.bitOf W a ^^ b) false

@[simp] theorem xorBits_nil (W : Nat → BitVec 32) : VG.Proof.TripleDes.X86.Linear.xorBits W [] = false := rfl

@[simp] theorem xorBits_cons (W : Nat → BitVec 32) (a : Nat) (l : List Nat) :
    VG.Proof.TripleDes.X86.Linear.xorBits W (a :: l) = (VG.Proof.TripleDes.X86.Linear.bitOf W a ^^ VG.Proof.TripleDes.X86.Linear.xorBits W l) := rfl

theorem bitOf_word (W : Nat → BitVec 32) (i t : Nat) (ht : t < 32) :
    VG.Proof.TripleDes.X86.Linear.bitOf W (32 * i + t) = (W i).getLsbD t := by
  simp only [VG.Proof.TripleDes.X86.Linear.bitOf]
  rw [Nat.mul_add_div (by decide), Nat.div_eq_of_lt ht, Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt ht]

/-- The assignment of the atoms below `N` given by the words `W`. -/
def assign (W : Nat → BitVec 32) (N : Nat) : Nat := tableOf (VG.Proof.TripleDes.X86.Linear.bitOf W) N

theorem xorA_assign (W : Nat → BitVec 32) {N : Nat} {l : List Nat} (hl : ∀ a ∈ l, a < N) :
    xorA (VG.Proof.TripleDes.X86.Linear.assign W N) l = VG.Proof.TripleDes.X86.Linear.xorBits W l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [xorA, List.foldr_cons, VG.Proof.TripleDes.X86.Linear.xorBits_cons] at ih ⊢
    rw [ih fun b hb => hl b (by simp [hb]), VG.Proof.TripleDes.X86.Linear.assign, testBit_tableOf]
    simp [hl a (by simp)]

theorem inWord_rel {k : Nat} (W : Nat → BitVec 32) {i : Nat} (hi : 32 * i + 32 ≤ 2 ^ k) :
    LaneRel k (VG.Proof.TripleDes.X86.Linear.assign W (2 ^ k)) (VG.Proof.TripleDes.X86.Linear.inWord i) (W i) := by
  refine ⟨Nat.two_pow_pos _, fun q hq => ?_⟩
  simp only [VG.Proof.TripleDes.X86.Linear.inWord, Nat.zero_testBit, Bool.false_xor]
  rw [par_mk hq (Nat.le_refl _) _ (fun q' hq' a ha => by simp at ha; omega), VG.Proof.TripleDes.X86.Linear.xorA_assign W
    (by intro a ha; simp at ha; omega)]
  simp [hq, VG.Proof.TripleDes.X86.Linear.bitOf_word W i q hq]

theorem outWord_rel {k : Nat} {W : Nat → BitVec 32} {g : Nat → List Nat} {x : BitVec 32}
    (hg : ∀ p < 32, ∀ a ∈ g p, a < 2 ^ k) (h : LaneRel k (VG.Proof.TripleDes.X86.Linear.assign W (2 ^ k)) (VG.Proof.TripleDes.X86.Linear.outWord g) x) :
    ∀ p < 32, x.getLsbD p = VG.Proof.TripleDes.X86.Linear.xorBits W (g p) := by
  intro p hp
  rw [h.2 p hp]
  simp only [VG.Proof.TripleDes.X86.Linear.outWord, Nat.zero_testBit, Bool.false_xor]
  rw [par_mk hp (Nat.le_refl _) _ (fun q hq => hg q hq), VG.Proof.TripleDes.X86.Linear.xorA_assign W (hg p hp)]
  simp [hp]

/-! ## The check -/

/-- The registers `ins` hold input words. -/
def linEnv (ins : List (Reg × Nat)) : Env (Nat × Nat) :=
  { reg := fun r => (ins.find? (·.1 == r)).map (VG.Proof.TripleDes.X86.Linear.inWord ·.2), slot := fun _ => none }

/-- External word `j` is input word `xb + j`. -/
def linExt (xb j : Nat) : Option (Nat × Nat) := some (VG.Proof.TripleDes.X86.Linear.inWord (xb + j))

/-- Each output register `r` holds `outWord g`, with atoms below `2 ^ k`. -/
def linPost (k : Nat) (outs : List (Reg × (Nat → List Nat))) (e : Env (Nat × Nat)) : Bool :=
  outs.all fun o => e.reg o.1 == some (VG.Proof.TripleDes.X86.Linear.outWord o.2) && (List.range 32).all fun p => (o.2 p).all (· < 2 ^ k)

/-- A linear block that the evaluator accepts, on the machine. -/
theorem linear_ok {k xb : Nat} {c : Cfg} {is : List Instr} {ins : List (Reg × Nat)}
    {outs : List (Reg × (Nat → List Nat))}
    (hchk : VG.X86.Straight.check (lanes 32 k) c (VG.Proof.TripleDes.X86.Linear.linExt xb) is (VG.Proof.TripleDes.X86.Linear.linEnv ins) (VG.Proof.TripleDes.X86.Linear.linPost k outs) = true)
    {s : VG.X86.State} (hok : Ok c s) (W : Nat → BitVec 32)
    (hin : ∀ r i, (r, i) ∈ ins → 32 * i + 32 ≤ 2 ^ k ∧ W i = s.gpr r)
    (hext : ∀ j < c.exts,
      32 * (xb + j) + 32 ≤ 2 ^ k ∧ W (xb + j) = s.mem.readW (wordAddr (s.gpr c.ext) j) 32) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ r g, (r, g) ∈ outs → ∀ p < 32, (s'.gpr r).getLsbD p = VG.Proof.TripleDes.X86.Linear.xorBits W (g p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, (is.all fun i => i.dst != some r) = true → s'.gpr r = s.gpr r) ∧
      VG.Frame [slotRegion c s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  have hrel : Rel (LaneRel k (VG.Proof.TripleDes.X86.Linear.assign W (2 ^ k))) c (VG.Proof.TripleDes.X86.Linear.linExt xb) (VG.Proof.TripleDes.X86.Linear.linEnv ins) s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), fun j a hj h => ?_⟩
    · simp only [VG.Proof.TripleDes.X86.Linear.linEnv, Option.map_eq_some_iff] at h
      obtain ⟨⟨r', i⟩, hf, rfl⟩ := h
      have hr : r' = r := by simpa using List.find?_some hf
      subst hr
      obtain ⟨h1, h2⟩ := hin r' i (List.mem_of_find?_eq_some hf)
      rw [← h2]; exact VG.Proof.TripleDes.X86.Linear.inWord_rel W h1
    · simp only [VG.Proof.TripleDes.X86.Linear.linExt, Option.some.injEq] at h; subst h
      obtain ⟨h1, h2⟩ := hext j hj
      rw [← h2]; exact VG.Proof.TripleDes.X86.Linear.inWord_rel W h1
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  refine ⟨s', hs', fun r g hrg q hq => ?_, p.rd, p.wr, fun r hr => p.other r (by simp [hr]), p.frame⟩
  have h := List.all_eq_true.mp hpost (r, g) hrg
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact VG.Proof.TripleDes.X86.Linear.outWord_rel (fun p hp a ha => h.2 p hp a ha) (p.rel.reg r _ h.1) q hq

/-- Output slots of a register-input linear block. -/
def linSlotPost (n k : Nat) (outs : List (Nat × (Nat → List Nat)))
    (e : Env (Nat × Nat)) : Bool :=
  outs.all fun o => decide (o.1 < n) && e.slot o.1 == some (VG.Proof.TripleDes.X86.Linear.outWord o.2) &&
    (List.range 32).all fun p => (o.2 p).all (· < 2 ^ k)

theorem linear_slots_ok {k xb : Nat} {c : Cfg} {is : List Instr}
    {ins : List (Reg × Nat)} {outs : List (Nat × (Nat → List Nat))}
    (hchk : VG.X86.Straight.check (lanes 32 k) c (VG.Proof.TripleDes.X86.Linear.linExt xb) is (VG.Proof.TripleDes.X86.Linear.linEnv ins)
      (VG.Proof.TripleDes.X86.Linear.linSlotPost c.slots k outs) = true)
    {s : VG.X86.State} (hok : Ok c s) (W : Nat → BitVec 32)
    (hin : ∀ r i, (r, i) ∈ ins → 32 * i + 32 ≤ 2 ^ k ∧ W i = s.gpr r)
    (hext : ∀ j < c.exts, 32 * (xb + j) + 32 ≤ 2 ^ k ∧
      W (xb + j) = s.mem.readW (wordAddr (s.gpr c.ext) j) 32) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ j g, (j, g) ∈ outs → ∀ p < 32,
        (s'.mem.readW (wordAddr (s.gpr c.base) j) 32).getLsbD p = VG.Proof.TripleDes.X86.Linear.xorBits W (g p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, (is.all fun i => i.dst != some r) = true → s'.gpr r = s.gpr r) ∧
      VG.Frame [slotRegion c s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  have hrel : Rel (LaneRel k (VG.Proof.TripleDes.X86.Linear.assign W (2 ^ k))) c (VG.Proof.TripleDes.X86.Linear.linExt xb) (VG.Proof.TripleDes.X86.Linear.linEnv ins) s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), fun j a hj h => ?_⟩
    · simp only [VG.Proof.TripleDes.X86.Linear.linEnv, Option.map_eq_some_iff] at h
      obtain ⟨⟨r', i⟩, hf, rfl⟩ := h
      have hr : r' = r := by simpa using List.find?_some hf
      subst hr
      obtain ⟨h1, h2⟩ := hin r' i (List.mem_of_find?_eq_some hf)
      rw [← h2]; exact VG.Proof.TripleDes.X86.Linear.inWord_rel W h1
    · simp only [VG.Proof.TripleDes.X86.Linear.linExt, Option.some.injEq] at h; subst h
      obtain ⟨h1, h2⟩ := hext j hj
      rw [← h2]; exact VG.Proof.TripleDes.X86.Linear.inWord_rel W h1
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  refine ⟨s', hs', fun j g hjg q hq => ?_, p.rd, p.wr,
    fun r hr => p.other r (by simp [hr]), p.frame⟩
  have h := List.all_eq_true.mp hpost (j, g) hjg
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at h
  have hb := p.base
  have hh := p.rel.slot j _ h.1.1 h.1.2
  rw [hb] at hh
  exact VG.Proof.TripleDes.X86.Linear.outWord_rel (fun p hp a ha => h.2 p hp a ha) hh q hq
end VG.Proof.TripleDes.X86.Linear

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.RoundCheck`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.TripleDes.X86
open VG.Proof.TripleDes.X86.Linear

noncomputable def inputLiterals : Array (Prog isa) :=
  #[input0.lit, input1.lit, input2.lit, input3.lit, input4.lit, input5.lit, input6.lit, input7.lit]
noncomputable def outputLiterals : Array (Prog isa) :=
  #[output0.lit, output1.lit, output2.lit, output3.lit, output4.lit, output5.lit, output6.lit, output7.lit]
def inputCfg : Cfg := { base := .ebp, slots := 128, ext := .edx, exts := 2 }
def inputEnv : Env (Nat × Nat) :=
  { reg := fun r => if r = .edi then some (VG.Proof.TripleDes.X86.Linear.inWord 0) else none, slot := fun _ => none }
def inputBits (i j p : Nat) : List Nat :=
  if p = 0 then
    let k := 6 * i + 5 - j
    [32 - Spec.TripleDes.expansion.getD k 1, 32 + (47 - k)]
  else []
def inputPost (i : Nat) (e : Env (Nat × Nat)) : Bool :=
  VG.Proof.TripleDes.X86.Linear.linSlotPost 128 7 ((List.range 6).map fun j => (16 + j, VG.Proof.TripleDes.X86.inputBits i j)) e

theorem input_check : ∀ i < 8,
    VG.X86.Straight.check (lanes 32 7) VG.Proof.TripleDes.X86.inputCfg (VG.Proof.TripleDes.X86.Linear.linExt 1)
      (instrs (inputLiterals.getD i (.block []))) VG.Proof.TripleDes.X86.inputEnv (VG.Proof.TripleDes.X86.inputPost i) = true := by
  decide +kernel

def outputCfg : Cfg := { base := .ebp, slots := 128, ext := .ebp, exts := 0 }
def outputEnv : Env (Nat × Nat) :=
  { reg := fun r => if r = .esi then some (VG.Proof.TripleDes.X86.Linear.inWord 4) else none,
    slot := fun k => if 16 ≤ k ∧ k < 20 then some (VG.Proof.TripleDes.X86.Linear.inWord (k - 16)) else none }
def outputBits (i p : Nat) : List Nat :=
  [128 + p] ++ (List.range 4).flatMap fun j =>
    let position := 4 * i + 4 - j
    let dst := (Spec.TripleDes.p.toList.findIdx? (· == position)).getD 0
    if p = 31 - dst then [32 * j] else []
def outputPost (i : Nat) (e : Env (Nat × Nat)) : Bool :=
  VG.Proof.TripleDes.X86.Linear.linPost 8 [(.esi, VG.Proof.TripleDes.X86.outputBits i)] e
theorem output_check : ∀ i < 8,
    VG.X86.Straight.check (lanes 32 8) VG.Proof.TripleDes.X86.outputCfg (fun _ => none)
      (instrs (outputLiterals.getD i (.block []))) VG.Proof.TripleDes.X86.outputEnv (VG.Proof.TripleDes.X86.outputPost i) = true := by
  decide +kernel
end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.RoundInput`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.TripleDes.X86.Linear

theorem inputLiteral_eq : ∀ i < 8,
    inputLiterals.getD i (.block []) = .block (sboxInputBits i)
  | 0, _ => input0.lit_eq.symm
  | 1, _ => input1.lit_eq.symm
  | 2, _ => input2.lit_eq.symm
  | 3, _ => input3.lit_eq.symm
  | 4, _ => input4.lit_eq.symm
  | 5, _ => input5.lit_eq.symm
  | 6, _ => input6.lit_eq.symm
  | 7, _ => input7.lit_eq.symm
  | n + 8, h => by omega

theorem inputEnv_eq : VG.Proof.TripleDes.X86.inputEnv = VG.Proof.TripleDes.X86.Linear.linEnv [(.edi, 0)] := by
  unfold VG.Proof.TripleDes.X86.inputEnv VG.Proof.TripleDes.X86.Linear.linEnv
  congr 1
  funext r; cases r <;> rfl

def roundInputs (s : VG.X86.State) (i : Nat) : BitVec 32 :=
  if i = 0 then s.gpr .edi
  else s.mem.readW (wordAddr (s.gpr .edx) (i - 1)) 32

theorem roundInput_ok (i : Nat) (hi : i < 8) (s : VG.X86.State) (hok : Ok VG.Proof.TripleDes.X86.inputCfg s) :
    ∃ s', runBlock isa (sboxInputBits i) s = some s' ∧
      (∀ j < 6, ∀ p < 32,
        (s'.mem.readW (wordAddr (s.gpr .ebp) (16 + j)) 32).getLsbD p =
          VG.Proof.TripleDes.X86.Linear.xorBits (VG.Proof.TripleDes.X86.roundInputs s) (VG.Proof.TripleDes.X86.inputBits i j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, ((sboxInputBits i).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) ∧ VG.Frame [slotRegion VG.Proof.TripleDes.X86.inputCfg s] s.mem s'.mem := by
  have h := VG.Proof.TripleDes.X86.input_check i hi
  rw [VG.Proof.TripleDes.X86.inputLiteral_eq i hi] at h
  change VG.X86.Straight.check _ _ _ (sboxInputBits i) VG.Proof.TripleDes.X86.inputEnv (VG.Proof.TripleDes.X86.inputPost i) = true at h
  rw [VG.Proof.TripleDes.X86.inputEnv_eq] at h
  obtain ⟨s', run, out, rd, wr, keep, frame⟩ :=
    VG.Proof.TripleDes.X86.Linear.linear_slots_ok h hok (VG.Proof.TripleDes.X86.roundInputs s) (fun r k hk => by
      simp only [List.mem_singleton, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact ⟨by decide, rfl⟩) (fun j hj => by
        refine ⟨?_, ?_⟩
        · simp only [VG.Proof.TripleDes.X86.inputCfg] at hj; omega
        · simp only [VG.Proof.TripleDes.X86.inputCfg, VG.Proof.TripleDes.X86.roundInputs, Nat.add_eq_zero_iff, Nat.one_ne_zero,
            false_and, ite_false, Nat.add_sub_cancel_left])
  refine ⟨s', run, fun j hj p hp => ?_, rd, wr, keep, frame⟩
  exact out (16 + j) (VG.Proof.TripleDes.X86.inputBits i j) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) p hp
end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.RoundOutput`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.TripleDes.X86
open VG.Proof.TripleDes.X86.Linear

theorem outputLiteral_eq : ∀ i < 8,
    outputLiterals.getD i (.block []) = .block (sboxOutputs i)
  | 0, _ => output0.lit_eq.symm
  | 1, _ => output1.lit_eq.symm
  | 2, _ => output2.lit_eq.symm
  | 3, _ => output3.lit_eq.symm
  | 4, _ => output4.lit_eq.symm
  | 5, _ => output5.lit_eq.symm
  | 6, _ => output6.lit_eq.symm
  | 7, _ => output7.lit_eq.symm
  | n + 8, h => by omega

def roundOutputs (s : VG.X86.State) (i : Nat) : BitVec 32 :=
  if i = 4 then s.gpr .esi
  else s.mem.readW (wordAddr (s.gpr .ebp) (16 + i)) 32

theorem roundOutput_ok (i : Nat) (hi : i < 8) (s : VG.X86.State) (hok : Ok VG.Proof.TripleDes.X86.outputCfg s) :
    ∃ s', runBlock isa (sboxOutputs i) s = some s' ∧
      (∀ p < 32, (s'.gpr .esi).getLsbD p =
        VG.Proof.TripleDes.X86.Linear.xorBits (VG.Proof.TripleDes.X86.roundOutputs s) (VG.Proof.TripleDes.X86.outputBits i p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, ((sboxOutputs i).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) ∧ VG.Frame [slotRegion VG.Proof.TripleDes.X86.outputCfg s] s.mem s'.mem := by
  have h := VG.Proof.TripleDes.X86.output_check i hi
  rw [VG.Proof.TripleDes.X86.outputLiteral_eq i hi] at h
  change VG.X86.Straight.check _ _ _ (sboxOutputs i) VG.Proof.TripleDes.X86.outputEnv (VG.Proof.TripleDes.X86.outputPost i) = true at h
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ h
  have hrel : Rel (LaneRel 8 (VG.Proof.TripleDes.X86.Linear.assign (VG.Proof.TripleDes.X86.roundOutputs s) 256)) VG.Proof.TripleDes.X86.outputCfg
      (fun _ => none) VG.Proof.TripleDes.X86.outputEnv s := by
    refine ⟨fun r a h => ?_, fun j a hj h => ?_, fun _ _ _ h => by cases h⟩
    · simp only [VG.Proof.TripleDes.X86.outputEnv] at h
      split at h
      · rename_i hr; subst r; cases h
        have hr := VG.Proof.TripleDes.X86.Linear.inWord_rel (VG.Proof.TripleDes.X86.roundOutputs s) (i := 4) (k := 8) (by decide)
        exact hr
      · cases h
    · simp only [VG.Proof.TripleDes.X86.outputEnv] at h
      split at h
      · rename_i hb; cases h
        have heq : 16 + (j - 16) = j := by omega
        have hne : j - 16 ≠ 4 := by omega
        have hr := VG.Proof.TripleDes.X86.Linear.inWord_rel (VG.Proof.TripleDes.X86.roundOutputs s) (i := j - 16) (k := 8) (by omega)
        simpa only [VG.Proof.TripleDes.X86.roundOutputs, hne, ite_false, heq, VG.Proof.TripleDes.X86.outputCfg] using hr
      · cases h
  obtain ⟨s', hs', post⟩ := run lanes_sound hok hrel he
  have ho := List.all_eq_true.mp hpost (.esi, VG.Proof.TripleDes.X86.outputBits i) (by simp)
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at ho
  refine ⟨s', hs', ?_, post.rd, post.wr,
    fun r hr => post.other r (by simp [hr]), post.frame⟩
  exact VG.Proof.TripleDes.X86.Linear.outWord_rel (fun p hp a ha => ho.2 p hp a ha) (post.rel.reg .esi _ ho.1)
end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Lit`. -/
section

namespace VG.Impl.TripleDes.X86

materialize_code sbox0
materialize_code sbox1
materialize_code sbox2
materialize_code sbox3
materialize_code sbox4
materialize_code sbox5
materialize_code sbox6
materialize_code sbox7

materialize_code initialPermutation
materialize_code finalPermutation
materialize_code keyPermutation1
materialize_code keyPermutation2

end VG.Impl.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Sbox`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.TripleDes.X86

noncomputable def sboxLiterals : Array (Prog isa) :=
  #[sbox0.lit, sbox1.lit, sbox2.lit, sbox3.lit, sbox4.lit, sbox5.lit, sbox6.lit, sbox7.lit]
noncomputable def sboxLiteral (i : Nat) : Prog isa := sboxLiterals.getD i (.block [])
def sboxCfg : Cfg := { base := .ebp, slots := 128, ext := .ebp, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun _ => none,
    slot := fun k => if 16 ≤ k ∧ k < 22 then some (inputTable (k - 16)) else none }
def sboxPost (i : Nat) (e : Env Nat) : Bool :=
  (List.range 4).all fun j => e.slot (16 + j) == some (outputTable i j)
theorem sbox_check : ∀ i < 8,
    VG.X86.Straight.check (table 32 64) VG.Proof.TripleDes.X86.sboxCfg (fun _ => none) (instrs (VG.Proof.TripleDes.X86.sboxLiteral i))
      VG.Proof.TripleDes.X86.sboxEnv (VG.Proof.TripleDes.X86.sboxPost i) = true := by
  lit_decide

def sboxWrites : List Reg := [.eax, .ebx, .ecx, .edx]
theorem sbox_preserves : ∀ i < 8,
    [Reg.esp, .ebp, .esi, .edi].all
      (fun r => (instrs (VG.Proof.TripleDes.X86.sboxLiteral i)).all fun op => op.dst != some r) = true := by
  decide +kernel

def inputAt (s : VG.X86.State) (p : Nat) : BitVec 6 :=
  ofBits 6 fun j => (s.mem.readW (wordAddr (s.gpr .ebp) (16 + j)) 32).getLsbD p
theorem inputAt_bit (s : VG.X86.State) (p k : Nat) (hk : k < 6) :
    (VG.Proof.TripleDes.X86.inputAt s p).toNat.testBit k =
      (s.mem.readW (wordAddr (s.gpr .ebp) (16 + k)) 32).getLsbD p := by
  simp only [VG.Proof.TripleDes.X86.inputAt, BitVec.testBit_toNat, getLsbD_ofBits, hk, decide_true, Bool.true_and]

theorem sboxLiteral_eq : ∀ i < 8, VG.Proof.TripleDes.X86.sboxLiteral i = .block (sboxCode i)
  | 0, _ => sbox0.lit_eq.symm
  | 1, _ => sbox1.lit_eq.symm
  | 2, _ => sbox2.lit_eq.symm
  | 3, _ => sbox3.lit_eq.symm
  | 4, _ => sbox4.lit_eq.symm
  | 5, _ => sbox5.lit_eq.symm
  | 6, _ => sbox6.lit_eq.symm
  | 7, _ => sbox7.lit_eq.symm
  | n + 8, h => by omega

/-- Every output bit, including allocated spills and memory operands. -/
theorem sbox_ok (i : Nat) (hi : i < 8) {s : VG.X86.State} (hok : Ok VG.Proof.TripleDes.X86.sboxCfg s) :
    ∃ s', runBlock isa (sboxCode i) s = some s' ∧
      (∀ j < 4, ∀ p < 32,
        (s'.mem.readW (wordAddr (s.gpr .ebp) (16 + j)) 32).getLsbD p =
        (Spec.TripleDes.sBox i (VG.Proof.TripleDes.X86.inputAt s p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ VG.Proof.TripleDes.X86.sboxWrites → s'.gpr r = s.gpr r) ∧
      VG.Frame [slotRegion VG.Proof.TripleDes.X86.sboxCfg s] s.mem s'.mem := by
  have codeEq : instrs (VG.Proof.TripleDes.X86.sboxLiteral i) = sboxCode i := by rw [VG.Proof.TripleDes.X86.sboxLiteral_eq i hi]; rfl
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ (VG.Proof.TripleDes.X86.sbox_check i hi)
  rw [codeEq] at he
  have hout : ∀ j < 4, e'.slot (16 + j) = some (outputTable i j) := by
    intro j hj
    exact beq_iff_eq.mp (List.all_eq_true.mp hpost j (List.mem_range.mpr hj))
  have key : ∀ p < 32, ∃ s', runBlock isa (sboxCode i) s = some s' ∧
      Post (TableRel p (VG.Proof.TripleDes.X86.inputAt s p).toNat) VG.Proof.TripleDes.X86.sboxCfg (fun _ => none) e' s s'
        (fun r => ((sboxCode i).all fun op => op.dst != some r) = false) := by
    intro p hp
    have hc := (VG.Proof.TripleDes.X86.inputAt s p).isLt
    refine run (table_sound hp hc) hok ⟨(fun _ _ h => by cases h), ?_,
      (fun _ _ _ h => by cases h)⟩ he
    intro k a hk h
    simp only [VG.Proof.TripleDes.X86.sboxEnv] at h
    split at h
    · rename_i hb
      cases h
      have hk6 : k - 16 < 6 := by omega
      have heq : 16 + (k - 16) = k := by omega
      simp only [TableRel, inputTable, testBit_tableOf, hc, decide_true, Bool.true_and,
        VG.Proof.TripleDes.X86.inputAt_bit s p (k - 16) hk6, heq, VG.Proof.TripleDes.X86.sboxCfg]
    · cases h
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, fun r hr => ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have h := p₁.rel.slot (16 + j) _ (by simp [VG.Proof.TripleDes.X86.sboxCfg]; omega) (hout j hj)
    have hb := p₁.base
    simp only [TableRel, outputTable, testBit_tableOf, (VG.Proof.TripleDes.X86.inputAt s p).isLt,
      decide_true, Bool.true_and, VG.Proof.TripleDes.X86.sboxCfg] at h hb
    rw [hb, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    exact h.symm
  · apply p₀.other r
    have hrest : r ∈ [Reg.esp, .ebp, .esi, .edi] := by
      revert hr; cases r <;> decide
    have h := List.all_eq_true.mp (VG.Proof.TripleDes.X86.sbox_preserves i hi) r hrest
    rw [codeEq] at h
    simp [h]
end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Spills`. -/
section

namespace VG.Proof.TripleDes.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)

def spillRegion (s : State) : Region := ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 64, 384⟩

def spillSafe : Instr → Bool
  | .mov d _ | .shift _ d _ => d != .ebp
  | .alu .and d _ | .alu .xor d _ => d != .ebp
  | .store m _ => decide (m.base = .ebp ∧
      64 ≤ m.disp ∧ m.disp + 4 ≤ 448)
  | _ => false

theorem spillSafe_check : ∀ i < 8,
    (instrs (VG.Proof.TripleDes.X86.sboxLiteral i)).all VG.Proof.TripleDes.X86.spillSafe = true := by decide +kernel

theorem spillStep_frame (i : Instr) (s s' : State)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (h : VG.Proof.TripleDes.X86.spillSafe i = true) (he : exec i s = some s') :
    s'.gpr .ebp = s.gpr .ebp ∧ VG.Frame [VG.Proof.TripleDes.X86.spillRegion s] s.mem s'.mem := by
  cases i <;> simp only [VG.Proof.TripleDes.X86.spillSafe, Bool.false_eq_true] at h
  case mov d src =>
    have hd : .ebp ≠ d := by intro heq; subst d; simp at h
    simp only [exec, Option.map_eq_some_iff] at he
    obtain ⟨v, _, rfl⟩ := he
    exact ⟨by simp only [gpr_setReg, hd, ite_false], by
      simp only [mem_setReg]; exact Frame.refl _ _⟩
  case alu op d src =>
    cases op <;> simp only [Bool.false_eq_true] at h
    all_goals
      have hd : .ebp ≠ d := by intro heq; subst d; simp at h
      simp only [exec, execAlu, Option.bind_eq_some_iff, Option.some.injEq] at he
      obtain ⟨v, _, rfl⟩ := he
      exact ⟨by simp only [gpr_setReg, gpr_arithFlags, hd, ite_false], by
        simp only [mem_setReg, mem_arithFlags]; exact Frame.refl _ _⟩
  case shift op d n =>
    have hd : .ebp ≠ d := by intro heq; subst d; simp at h
    simp only [exec, execShift] at he
    split at he
    · cases op <;> obtain rfl := Option.some.inj he
      all_goals
        exact ⟨by simp only [gpr_setReg, gpr_setFlags, hd, ite_false], by
          simp only [mem_setReg, mem_setFlags]; exact Frame.refl _ _⟩
    · cases he
  case store m r =>
    obtain ⟨hb, hlo, hhi⟩ := of_decide_eq_true h
    simp only [exec, State.store32] at he
    split at he
    · simp only [Option.some.injEq] at he
      subst s'
      refine ⟨rfl, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_⟩
      simp only [State.ea, hb]
      change (VG.Proof.TripleDes.X86.spillRegion s).Contains (addr (s.gpr .ebp) m.disp) 4
      rw [VG.X86.addr_eq (by omega)]
      exact Offset.contains (addr32 (s.gpr .ebp)) (by omega) (by omega) (by decide)
    · cases he

theorem spillBlock_frame (is : List Instr) (s s' : State)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (hsafe : is.all VG.Proof.TripleDes.X86.spillSafe = true) (he : runBlock isa is s = some s') :
    s'.gpr .ebp = s.gpr .ebp ∧ VG.Frame [VG.Proof.TripleDes.X86.spillRegion s] s.mem s'.mem := by
  induction is generalizing s with
  | nil =>
    rw [runBlock_nil] at he
    obtain rfl := Option.some.inj he
    exact ⟨rfl, Frame.refl _ _⟩
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hsafe
    rw [runBlock_cons] at he
    change (exec i s).bind (runBlock isa is) = some s' at he
    obtain ⟨s₁, hi, hrest⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨hg, hf⟩ := VG.Proof.TripleDes.X86.spillStep_frame i s s₁ fit hsafe.1 hi
    obtain ⟨hg', hf'⟩ := ih s₁ (by rw [hg]; exact fit) hsafe.2 hrest
    refine ⟨hg'.trans hg, hf.trans ?_⟩
    have hr : VG.Proof.TripleDes.X86.spillRegion s₁ = VG.Proof.TripleDes.X86.spillRegion s := by simp only [VG.Proof.TripleDes.X86.spillRegion, hg]
    rw [hr] at hf'
    exact hf'

/-- The saved registers and round counter in scratch slots 0–7 are
outside the S-box's frame, as are the key schedule and block data. -/
theorem sbox_spillFrame (i : Nat) (hi : i < 8) (s s' : State)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (he : runBlock isa (sboxCode i) s = some s') :
    VG.Frame [VG.Proof.TripleDes.X86.spillRegion s] s.mem s'.mem := by
  have h := VG.Proof.TripleDes.X86.spillSafe_check i hi
  rw [VG.Proof.TripleDes.X86.sboxLiteral_eq i hi] at h
  exact (VG.Proof.TripleDes.X86.spillBlock_frame _ _ _ fit h he).2

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Round`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.TripleDes.X86
open VG.Proof.TripleDes.X86.Linear

theorem roundInput_bounds : ∀ i < 8, ∀ j < 6,
    32 - Spec.TripleDes.expansion.getD (6 * i + 5 - j) 1 < 32 ∧
    47 - (6 * i + 5 - j) < 64 := by
  decide +kernel

theorem bitOf_low (W : Nat → BitVec 32) (a : Nat) (ha : a < 32) :
    VG.Proof.TripleDes.X86.Linear.bitOf W a = (W 0).getLsbD a := by
  simp only [VG.Proof.TripleDes.X86.Linear.bitOf, Nat.div_eq_of_lt ha, Nat.mod_eq_of_lt ha]

def keyWord (s : State) : BitVec 64 :=
  s.mem.readW (wordAddr (s.gpr .edx) 1) 32 ++ s.mem.readW (wordAddr (s.gpr .edx) 0) 32

theorem bitOf_key (s : State) (a : Nat) (ha : a < 64) :
    VG.Proof.TripleDes.X86.Linear.bitOf (fun k => if k = 0 then s.gpr .edi else
      s.mem.readW (wordAddr (s.gpr .edx) (k - 1)) 32) (32 + a) =
    (VG.Proof.TripleDes.X86.keyWord s).getLsbD a := by
  simp only [VG.Proof.TripleDes.X86.Linear.bitOf, VG.Proof.TripleDes.X86.keyWord, BitVec.getLsbD_append]
  by_cases h : a < 32
  · have hd : (32 + a) / 32 = 1 := by omega
    simp only [h, ite_true, hd, Nat.add_mod_left, Nat.mod_eq_of_lt h]
    rfl
  · have hd : (32 + a) / 32 = 2 := by omega
    have hm : (32 + a) % 32 = a - 32 := by omega
    simp only [h, ite_false, hd, hm]
    rfl

def roundChunk (i : Nat) (r : BitVec 32) (k : BitVec 48) : BitVec 6 :=
  ((Spec.TripleDes.permute Spec.TripleDes.expansion r ^^^ k) >>> (6 * (7 - i))).setWidth 6

theorem roundChunk_bit (i j : Nat) (hi : i < 8) (hj : j < 6)
    (r : BitVec 32) (k : BitVec 64) :
    (VG.Proof.TripleDes.X86.roundChunk i (r.setWidth 32) (k.setWidth 48)).getLsbD j =
      (r.getLsbD (32 - Spec.TripleDes.expansion.getD (6 * i + 5 - j) 1) ^^
        k.getLsbD (47 - (6 * i + 5 - j))) := by
  have ht : 6 * (7 - i) + j < 48 := by omega
  have heq : 48 - 1 - (6 * (7 - i) + j) = 6 * i + 5 - j := by omega
  have hkey : 6 * (7 - i) + j = 47 - (6 * i + 5 - j) := by omega
  have hsource : 32 - Spec.TripleDes.expansion.getD (6 * i + 5 - j) 1 < 32 := by
    have hb : ∀ t < 48, 1 ≤ Spec.TripleDes.expansion.getD t 1 := by decide +kernel
    have hpos : 6 * i + 5 - j < 48 := by omega
    have := hb _ hpos
    omega
  simp only [VG.Proof.TripleDes.X86.roundChunk, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]
  rw [VG.Proof.TripleDes.permute_bit _ _ (by decide) _ ht]
  rw [heq]
  simp only [BitVec.getLsbD_setWidth, hsource, ht, decide_true, Bool.true_and]
  rw [hkey]

theorem input_keeps : ∀ i < 8,
    [Reg.esp, .ebp, .esi, .edi, .edx].all (fun r =>
      (instrs (inputLiterals.getD i (.block []))).all fun op => op.dst != some r) = true := by
  decide +kernel

theorem input_keep (i : Nat) (hi : i < 8) (r : Reg)
    (hr : r ∈ [Reg.esp, .ebp, .esi, .edi, .edx]) :
    (sboxInputBits i).all (fun op => op.dst != some r) = true := by
  have h := List.all_eq_true.mp (VG.Proof.TripleDes.X86.input_keeps i hi) r hr
  rw [VG.Proof.TripleDes.X86.inputLiteral_eq i hi] at h
  exact h

theorem input_spillSafe : ∀ i < 8,
    (instrs (inputLiterals.getD i (.block []))).all VG.Proof.TripleDes.X86.spillSafe = true := by decide +kernel

theorem roundInput_chunk (i : Nat) (hi : i < 8) (s : State) (hok : Ok VG.Proof.TripleDes.X86.inputCfg s) :
    ∃ s', runBlock isa (sboxInputBits i) s = some s' ∧
      VG.Proof.TripleDes.X86.inputAt s' 0 = VG.Proof.TripleDes.X86.roundChunk i (s.gpr .edi) ((VG.Proof.TripleDes.X86.keyWord s).setWidth 48) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.esp, .ebp, .esi, .edi, .edx], s'.gpr r = s.gpr r) ∧
      VG.Frame [VG.Proof.TripleDes.X86.spillRegion s] s.mem s'.mem := by
  obtain ⟨s', run, bits, rd, wr, keep, _⟩ := VG.Proof.TripleDes.X86.roundInput_ok i hi s hok
  have kept : ∀ r ∈ [Reg.esp, .ebp, .esi, .edi, .edx], s'.gpr r = s.gpr r :=
    fun r hr => keep r (VG.Proof.TripleDes.X86.input_keep i hi r hr)
  have safe := VG.Proof.TripleDes.X86.input_spillSafe i hi
  rw [VG.Proof.TripleDes.X86.inputLiteral_eq i hi] at safe
  refine ⟨s', run, ?_, rd, wr, kept, (VG.Proof.TripleDes.X86.spillBlock_frame _ _ _ hok.fit safe run).2⟩
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [VG.Proof.TripleDes.X86.inputAt, getLsbD_ofBits, hj, decide_true, Bool.true_and,
    kept .ebp (by decide)]
  rw [bits j hj 0 (by decide), ← BitVec.setWidth_eq (s.gpr .edi), VG.Proof.TripleDes.X86.roundChunk_bit i j hi hj]
  obtain ⟨hr, hk⟩ := VG.Proof.TripleDes.X86.roundInput_bounds i hi j hj
  simp only [VG.Proof.TripleDes.X86.inputBits, ite_true, VG.Proof.TripleDes.X86.Linear.xorBits_cons, VG.Proof.TripleDes.X86.Linear.xorBits_nil, Bool.xor_false,
    VG.Proof.TripleDes.X86.bitOf_low _ _ hr, VG.Proof.TripleDes.X86.roundInputs, ite_true]
  have hkey : VG.Proof.TripleDes.X86.Linear.bitOf (VG.Proof.TripleDes.X86.roundInputs s) (32 + (47 - (6 * i + 5 - j))) =
      (VG.Proof.TripleDes.X86.keyWord s).getLsbD (47 - (6 * i + 5 - j)) := VG.Proof.TripleDes.X86.bitOf_key s _ hk
  rw [hkey]

def boxSource (p : Nat) : Nat := Spec.TripleDes.p.getD (31 - p) 1 - 1

def boxPiece (i : Nat) (b : BitVec 4) : BitVec 32 :=
  ofBits 32 fun p => if VG.Proof.TripleDes.X86.boxSource p / 4 = i then
    b.getLsbD (3 - VG.Proof.TripleDes.X86.boxSource p % 4) else false

theorem outputBits_shape : ∀ i < 8, ∀ p < 32,
    VG.Proof.TripleDes.X86.outputBits i p = [128 + p] ++
      (if VG.Proof.TripleDes.X86.boxSource p / 4 = i then [32 * (3 - VG.Proof.TripleDes.X86.boxSource p % 4)] else []) := by
  decide +kernel
theorem output_keeps : ∀ i < 8,
    [Reg.esp, .ebp, .edi, .edx, .ebx, .ecx].all (fun r =>
      (instrs (outputLiterals.getD i (.block []))).all fun op => op.dst != some r) = true := by
  decide +kernel

theorem output_keep (i : Nat) (hi : i < 8) (r : Reg)
    (hr : r ∈ [Reg.esp, .ebp, .edi, .edx, .ebx, .ecx]) :
    (sboxOutputs i).all (fun op => op.dst != some r) = true := by
  have h := List.all_eq_true.mp (VG.Proof.TripleDes.X86.output_keeps i hi) r hr
  rw [VG.Proof.TripleDes.X86.outputLiteral_eq i hi] at h
  exact h

theorem output_spillSafe : ∀ i < 8,
    (instrs (outputLiterals.getD i (.block []))).all VG.Proof.TripleDes.X86.spillSafe = true := by decide +kernel

theorem roundOutput_piece (i : Nat) (hi : i < 8) (s : State) (hok : Ok VG.Proof.TripleDes.X86.outputCfg s)
    (b : BitVec 4)
    (hb : ∀ j < 4,
      (s.mem.readW (wordAddr (s.gpr .ebp) (16 + j)) 32).getLsbD 0 = b.getLsbD j) :
    ∃ s', runBlock isa (sboxOutputs i) s = some s' ∧
      s'.gpr .esi = s.gpr .esi ^^^ VG.Proof.TripleDes.X86.boxPiece i b ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.esp, .ebp, .edi, .edx, .ebx, .ecx], s'.gpr r = s.gpr r) ∧
      VG.Frame [VG.Proof.TripleDes.X86.spillRegion s] s.mem s'.mem := by
  obtain ⟨s', run, bits, rd, wr, keep, _⟩ := VG.Proof.TripleDes.X86.roundOutput_ok i hi s hok
  have safe := VG.Proof.TripleDes.X86.output_spillSafe i hi
  rw [VG.Proof.TripleDes.X86.outputLiteral_eq i hi] at safe
  refine ⟨s', run, ?_, rd, wr, fun r hr => keep r (VG.Proof.TripleDes.X86.output_keep i hi r hr),
    (VG.Proof.TripleDes.X86.spillBlock_frame _ _ _ hok.fit safe run).2⟩
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [bits p hp, VG.Proof.TripleDes.X86.outputBits_shape i hi p hp]
  simp only [BitVec.getLsbD_xor, List.cons_append, List.nil_append, VG.Proof.TripleDes.X86.Linear.xorBits_cons]
  have hleft : VG.Proof.TripleDes.X86.Linear.bitOf (VG.Proof.TripleDes.X86.roundOutputs s) (128 + p) = (s.gpr .esi).getLsbD p := by
    have h := VG.Proof.TripleDes.X86.Linear.bitOf_word (VG.Proof.TripleDes.X86.roundOutputs s) 4 p hp
    exact h
  rw [hleft]
  by_cases h : VG.Proof.TripleDes.X86.boxSource p / 4 = i
  · simp only [h, ite_true, VG.Proof.TripleDes.X86.Linear.xorBits_cons, VG.Proof.TripleDes.X86.Linear.xorBits_nil, Bool.xor_false]
    have hj : 3 - VG.Proof.TripleDes.X86.boxSource p % 4 < 4 := by omega
    have hjne : 3 - VG.Proof.TripleDes.X86.boxSource p % 4 ≠ 4 := by omega
    have hbit := VG.Proof.TripleDes.X86.Linear.bitOf_word (VG.Proof.TripleDes.X86.roundOutputs s)
      (3 - VG.Proof.TripleDes.X86.boxSource p % 4) 0 (by decide)
    simp only [Nat.add_zero] at hbit
    rw [hbit]
    simp only [VG.Proof.TripleDes.X86.roundOutputs, hjne, ite_false, hb _ hj, VG.Proof.TripleDes.X86.boxPiece, getLsbD_ofBits,
      hp, decide_true, Bool.true_and, h, ite_true]
  · simp only [h, ite_false, VG.Proof.TripleDes.X86.Linear.xorBits_nil, Bool.xor_false, VG.Proof.TripleDes.X86.boxPiece, getLsbD_ofBits,
      hp, decide_true, Bool.true_and]
end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Box`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd VG.Impl.TripleDes.X86

def roundKeyPtr (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .ebp) 4) 32

def roundKeyWord (s : State) : BitVec 64 :=
  s.mem.readW (wordAddr (VG.Proof.TripleDes.X86.roundKeyPtr s) 1) 32 ++
    s.mem.readW (wordAddr (VG.Proof.TripleDes.X86.roundKeyPtr s) 0) 32

structure BoxPre (s : State) : Prop where
  scratch : Ok VG.Proof.TripleDes.X86.sboxCfg s
  read : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (VG.Proof.TripleDes.X86.roundKeyPtr s) j) 4
  disjoint : ∀ j < 2, (⟨wordAddr (VG.Proof.TripleDes.X86.roundKeyPtr s) j, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.spillRegion s)
  sep : ∀ k < 128, ∀ j < 2,
    Mem.Sep (wordAddr (s.gpr .ebp) k) 4 (wordAddr (VG.Proof.TripleDes.X86.roundKeyPtr s) j) 4

theorem pointerLoad_ok (s : State) (hok : Ok VG.Proof.TripleDes.X86.sboxCfg s) :
    exec (.mov .edx (.mem (memOp .ebp 16))) s = some (s.setReg .edx (VG.Proof.TripleDes.X86.roundKeyPtr s)) := by
  have hw := hok.slotIn 4 (by decide)
  have hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 4) 4 := by
    obtain ⟨r, hmem, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hmem, hc⟩
  simp only [exec, readSrc, State.load32, memOp, State.ea]
  change (if InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 4) 4 then
    some (VG.Proof.TripleDes.X86.roundKeyPtr s) else none).map (s.setReg .edx) = _
  simp only [hr, ite_true, Option.map_some]

theorem runBoxes_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

/-- One complete DES S-box contribution on IA-32. -/
theorem box_ok (i : Nat) (hi : i < 8) (s : State) (pre : VG.Proof.TripleDes.X86.BoxPre s) :
    ∃ s', runBlock isa (box i) s = some s' ∧
      s'.gpr .esi = s.gpr .esi ^^^ VG.Proof.TripleDes.X86.boxPiece i
        (Spec.TripleDes.sBox i (VG.Proof.TripleDes.X86.roundChunk i (s.gpr .edi) ((VG.Proof.TripleDes.X86.roundKeyWord s).setWidth 48))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.esp, .ebp, .edi], s'.gpr r = s.gpr r) ∧
      VG.Frame [VG.Proof.TripleDes.X86.spillRegion s] s.mem s'.mem := by
  let s₀ := s.setReg .edx (VG.Proof.TripleDes.X86.roundKeyPtr s)
  have inputOk : Ok VG.Proof.TripleDes.X86.inputCfg s₀ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hk; exact pre.scratch.slotIn k hk
    · intro j hj; exact pre.read j hj
    · exact pre.scratch.fit
    · intro k hk j hj; exact pre.sep k hk j hj
  obtain ⟨s₁, run₁, chunk, rd₁, wr₁, keep₁, frame₁⟩ := VG.Proof.TripleDes.X86.roundInput_chunk i hi s₀ inputOk
  have hok₁ : Ok VG.Proof.TripleDes.X86.sboxCfg s₁ := pre.scratch.congr
    ((keep₁ .ebp (by decide)).trans (gpr_setReg_of_ne s _ (by decide)))
    ((keep₁ .ebp (by decide)).trans (gpr_setReg_of_ne s _ (by decide))) rd₁ wr₁
  obtain ⟨s₂, run₂, bits, rd₂, wr₂, keep₂, _⟩ := VG.Proof.TripleDes.X86.sbox_ok i hi hok₁
  have kept₂ : ∀ r ∈ [Reg.esp, .ebp, .esi, .edi], s₂.gpr r = s₁.gpr r := by
    intro r hr; apply keep₂ r
    revert hr; cases r <;> decide
  have hok₂ : Ok VG.Proof.TripleDes.X86.outputCfg s₂ := hok₁.congr
    (kept₂ .ebp (by decide)) (kept₂ .ebp (by decide)) rd₂ wr₂
  have hbits : ∀ j < 4,
      (s₂.mem.readW (wordAddr (s₂.gpr .ebp) (16 + j)) 32).getLsbD 0 =
        (Spec.TripleDes.sBox i (VG.Proof.TripleDes.X86.roundChunk i (s.gpr .edi)
          ((VG.Proof.TripleDes.X86.roundKeyWord s).setWidth 48))).getLsbD j := by
    intro j hj
    rw [kept₂ .ebp (by decide), bits j hj 0 (by decide), chunk]
    rfl
  obtain ⟨s₃, run₃, value, rd₃, wr₃, keep₃, frame₃⟩ := VG.Proof.TripleDes.X86.roundOutput_piece i hi s₂ hok₂ _ hbits
  have region₁ : VG.Proof.TripleDes.X86.spillRegion s₁ = VG.Proof.TripleDes.X86.spillRegion s := by
    simp only [VG.Proof.TripleDes.X86.spillRegion, keep₁ .ebp (by decide), s₀, gpr_setReg, reduceCtorEq, ite_false]
  have region₂ : VG.Proof.TripleDes.X86.spillRegion s₂ = VG.Proof.TripleDes.X86.spillRegion s := by
    simp only [VG.Proof.TripleDes.X86.spillRegion, kept₂ .ebp (by decide), keep₁ .ebp (by decide), s₀,
      gpr_setReg, reduceCtorEq, ite_false]
  have frame₂ := VG.Proof.TripleDes.X86.sbox_spillFrame i hi s₁ s₂ hok₁.fit run₂
  rw [region₁] at frame₂
  rw [region₂] at frame₃
  have hframe₁ : VG.Frame [VG.Proof.TripleDes.X86.spillRegion s] s.mem s₁.mem := frame₁
  refine ⟨s₃, ?_, ?_, rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_,
    hframe₁.trans (frame₂.trans frame₃)⟩
  · simp only [box, sboxInputs, VG.Proof.TripleDes.X86.runBoxes_append, runBlock_cons, runBlock_nil,
      VG.Proof.TripleDes.X86.pointerLoad_ok s pre.scratch, runStep_some, s₀, run₁, Option.bind_some, run₂, run₃]
  · rw [value, kept₂ .esi (by decide), keep₁ .esi (by decide)]
    rfl
  · intro r hr
    have hr₃ : r ∈ [Reg.esp, .ebp, .edi, .edx, .ebx, .ecx] := by
      revert hr; cases r <;> decide
    have hr₂ : r ∈ [Reg.esp, .ebp, .esi, .edi] := by
      revert hr; cases r <;> decide
    have hr₁ : r ∈ [Reg.esp, .ebp, .esi, .edi, .edx] := by
      revert hr; cases r <;> decide
    rw [keep₃ r hr₃, kept₂ r hr₂, keep₁ r hr₁]
    exact gpr_setReg_of_ne s _ (by revert hr; cases r <;> decide)
end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.RoundFunction`. -/
section

namespace VG.Proof.TripleDes.X86

open VG VG.Bitslice VG.Spec.TripleDes

theorem boxSource_shape : ∀ j < 32,
    7 - (32 - p.getD (31 - j) 1) / 4 = VG.Proof.TripleDes.X86.boxSource j / 4 ∧
    (32 - p.getD (31 - j) 1) % 4 = 3 - VG.Proof.TripleDes.X86.boxSource j % 4 ∧
    VG.Proof.TripleDes.X86.boxSource j / 4 < 8 := by
  decide +kernel

theorem boxPiece_round_bit (i : Nat) (r : BitVec 32) (k : BitVec 48)
    (j : Nat) (hj : j < 32) :
    (VG.Proof.TripleDes.X86.boxPiece i (sBox i (VG.Proof.TripleDes.X86.roundChunk i r k))).getLsbD j =
      if VG.Proof.TripleDes.X86.boxSource j / 4 = i then (roundFunction r k).getLsbD j else false := by
  simp only [VG.Proof.TripleDes.X86.boxPiece, getLsbD_ofBits, hj, decide_true, Bool.true_and]
  by_cases heq : VG.Proof.TripleDes.X86.boxSource j / 4 = i
  · simp only [heq, ite_true]
    rw [VG.Proof.TripleDes.roundFunction_bit r k j hj]
    obtain ⟨hidx, hbit, _⟩ := VG.Proof.TripleDes.X86.boxSource_shape j hj
    simp only [hidx, hbit, heq, VG.Proof.TripleDes.X86.roundChunk]
  · simp only [heq, ite_false]

theorem foldl_xor_bits (xs : List Nat) (f : Nat → BitVec 32) (a : BitVec 32) (j : Nat) :
    (xs.foldl (fun out i => out ^^^ f i) a).getLsbD j =
      xs.foldl (fun out i => out ^^ (f i).getLsbD j) (a.getLsbD j) := by
  induction xs generalizing a with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.foldl_cons, ih, BitVec.getLsbD_xor]

theorem select_xor : ∀ n < 8, ∀ b : Bool,
    (List.range 8).foldl (fun out i => out ^^ (if n = i then b else false)) false = b := by
  decide +kernel

/-- The eight S-box contributions give the standard DES round function. -/
theorem boxPieces_eq_roundFunction (r : BitVec 32) (k : BitVec 48) :
    (List.range 8).foldl (fun out i => out ^^^ VG.Proof.TripleDes.X86.boxPiece i (sBox i (VG.Proof.TripleDes.X86.roundChunk i r k)))
      (0 : BitVec 32) = roundFunction r k := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hfold : (fun (out : Bool) i => out ^^
      (VG.Proof.TripleDes.X86.boxPiece i (sBox i (VG.Proof.TripleDes.X86.roundChunk i r k))).getLsbD j) =
      (fun out i => out ^^ (if VG.Proof.TripleDes.X86.boxSource j / 4 = i then
        (roundFunction r k).getLsbD j else false)) := by
    funext out i
    exact congrArg (fun b => out ^^ b) (VG.Proof.TripleDes.X86.boxPiece_round_bit i r k j hj)
  have hbits := VG.Proof.TripleDes.X86.foldl_xor_bits (List.range 8)
    (fun i => VG.Proof.TripleDes.X86.boxPiece i (sBox i (VG.Proof.TripleDes.X86.roundChunk i r k))) 0 j
  have hz : (0 : BitVec 32).getLsbD j = false := by
    change (BitVec.ofNat 32 0).getLsbD j = false
    exact BitVec.getLsbD_zero
  have hinit := congrArg (fun b : Bool => (List.range 8).foldl
    (fun out i => out ^^ (VG.Proof.TripleDes.X86.boxPiece i (sBox i (VG.Proof.TripleDes.X86.roundChunk i r k))).getLsbD j) b) hz
  have hchange := congrArg
    (fun f : Bool → Nat → Bool => (List.range 8).foldl f false) hfold
  exact hbits.trans (hinit.trans (hchange.trans (VG.Proof.TripleDes.X86.select_xor _ (VG.Proof.TripleDes.X86.boxSource_shape j hj).2.2 _)))

theorem foldl_xor_start (xs : List Nat) (f : Nat → BitVec 32) (a : BitVec 32) :
    xs.foldl (fun out i => out ^^^ f i) a =
      a ^^^ xs.foldl (fun out i => out ^^^ f i) 0 := by
  induction xs generalizing a with
  | nil => simp
  | cons i xs ih =>
    simp only [List.foldl_cons]
    have hz : (0 : BitVec 32) ^^^ f i = f i := BitVec.zero_xor
    rw [hz, ih (a ^^^ f i), ih (f i)]
    exact BitVec.xor_assoc _ _ _

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.RoundBody`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd VG.Impl.TripleDes.X86

theorem roundKeyPtr_frame {s s' : State} (pre : VG.Proof.TripleDes.X86.BoxPre s)
    (base : s'.gpr .ebp = s.gpr .ebp) (frame : VG.Frame [VG.Proof.TripleDes.X86.spillRegion s] s.mem s'.mem) :
    VG.Proof.TripleDes.X86.roundKeyPtr s' = VG.Proof.TripleDes.X86.roundKeyPtr s := by
  unfold VG.Proof.TripleDes.X86.roundKeyPtr
  rw [base]
  apply frame.readW (r := ⟨wordAddr (s.gpr .ebp) 4, 4⟩) (Region.contains_self _ _)
    (fun q hq => ?_) (by decide)
  obtain rfl := List.mem_singleton.mp hq
  change (⟨addr (s.gpr .ebp) 16, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.spillRegion s)
  rw [addr_eq (by have h := pre.scratch.fit; change (s.gpr .ebp).toNat + 512 ≤ _ at h; omega)]
  exact Offset.disjoint _ (by decide) (by decide) (by decide)

theorem BoxPre.frame {s s' : State} (pre : VG.Proof.TripleDes.X86.BoxPre s)
    (base : s'.gpr .ebp = s.gpr .ebp) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (frame : VG.Frame [VG.Proof.TripleDes.X86.spillRegion s] s.mem s'.mem) :
    VG.Proof.TripleDes.X86.BoxPre s' ∧ VG.Proof.TripleDes.X86.roundKeyWord s' = VG.Proof.TripleDes.X86.roundKeyWord s := by
  have ptr := VG.Proof.TripleDes.X86.roundKeyPtr_frame pre base frame
  have region : VG.Proof.TripleDes.X86.spillRegion s' = VG.Proof.TripleDes.X86.spillRegion s := by simp only [VG.Proof.TripleDes.X86.spillRegion, base]
  constructor
  · refine ⟨pre.scratch.congr base base rd wr, ?_, ?_, ?_⟩
    · rw [rd, wr, ptr]; exact pre.read
    · rw [ptr, region]; exact pre.disjoint
    · rw [base, ptr]; exact pre.sep
  · unfold VG.Proof.TripleDes.X86.roundKeyWord
    rw [ptr]
    have hword (j : Nat) (hj : j < 2) :
        s'.mem.readW (wordAddr (VG.Proof.TripleDes.X86.roundKeyPtr s) j) 32 =
          s.mem.readW (wordAddr (VG.Proof.TripleDes.X86.roundKeyPtr s) j) 32 :=
      frame.readW (r := ⟨wordAddr (VG.Proof.TripleDes.X86.roundKeyPtr s) j, 4⟩) (Region.contains_self _ _)
        (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact pre.disjoint j hj) (by decide)
    rw [hword 0 (by decide), hword 1 (by decide)]

def contribution (r : BitVec 32) (k : BitVec 64) (i : Nat) : BitVec 32 :=
  VG.Proof.TripleDes.X86.boxPiece i (Spec.TripleDes.sBox i (VG.Proof.TripleDes.X86.roundChunk i r (k.setWidth 48)))

theorem boxes_ok (indices : List Nat) (hindices : ∀ i ∈ indices, i < 8)
    (r : BitVec 32) (k : BitVec 64) (s : State) (pre : VG.Proof.TripleDes.X86.BoxPre s)
    (hr : s.gpr .edi = r) (hk : VG.Proof.TripleDes.X86.roundKeyWord s = k) :
    ∃ s', runBlock isa (indices.flatMap box) s = some s' ∧
      s'.gpr .esi = indices.foldl (fun out i => out ^^^ VG.Proof.TripleDes.X86.contribution r k i) (s.gpr .esi) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ [Reg.esp, .ebp, .edi], s'.gpr q = s.gpr q) ∧
      VG.Frame [VG.Proof.TripleDes.X86.spillRegion s] s.mem s'.mem := by
  induction indices generalizing s with
  | nil => exact ⟨s, runBlock_nil, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | cons i indices ih =>
    have hi := hindices i List.mem_cons_self
    obtain ⟨s₁, run₁, value₁, rd₁, wr₁, keep₁, frame₁⟩ := VG.Proof.TripleDes.X86.box_ok i hi s pre
    obtain ⟨pre₁, key₁⟩ := pre.frame (keep₁ .ebp (by decide)) rd₁ wr₁ frame₁
    obtain ⟨s₂, run₂, value₂, rd₂, wr₂, keep₂, frame₂⟩ := ih
      (fun j hj => hindices j (List.mem_cons_of_mem _ hj)) s₁ pre₁
      ((keep₁ .edi (by decide)).trans hr) (key₁.trans hk)
    refine ⟨s₂, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁,
      fun q hq => (keep₂ q hq).trans (keep₁ q hq), ?_⟩
    · simp only [List.flatMap_cons, VG.Proof.TripleDes.X86.runBoxes_append, run₁, Option.bind_some, run₂]
    · rw [hr, hk] at value₁
      change s₁.gpr .esi = s.gpr .esi ^^^ VG.Proof.TripleDes.X86.contribution r k i at value₁
      simpa only [List.foldl_cons, ← value₁] using value₂
    · have hregion : VG.Proof.TripleDes.X86.spillRegion s₁ = VG.Proof.TripleDes.X86.spillRegion s := by
        simp only [VG.Proof.TripleDes.X86.spillRegion, keep₁ .ebp (by decide)]
      rw [hregion] at frame₂
      exact frame₁.trans frame₂

theorem contributions_roundFunction (r : BitVec 32) (k : BitVec 64) (l : BitVec 32) :
    (List.range 8).foldl (fun out i => out ^^^ VG.Proof.TripleDes.X86.contribution r k i) l =
      l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48) := by
  rw [VG.Proof.TripleDes.X86.foldl_xor_start]
  exact congrArg (l ^^^ ·) (VG.Proof.TripleDes.X86.boxPieces_eq_roundFunction r (k.setWidth 48))

theorem swapHalves_ok (s : State) :
    ∃ s', runBlock isa swapHalves s = some s' ∧
      s'.gpr .esi = s.gpr .edi ∧ s'.gpr .edi = s.gpr .esi ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esp = s.gpr .esp := by
  refine ⟨_, by
    simp only [swapHalves, rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true,
    rd_setReg, wr_setReg, mem_setReg]

theorem roundBody_ok (s : State) (l r : BitVec 32) (k : BitVec 64)
    (hl : s.gpr .esi = l) (hr : s.gpr .edi = r) (hk : VG.Proof.TripleDes.X86.roundKeyWord s = k) (pre : VG.Proof.TripleDes.X86.BoxPre s) :
    ∃ s', runBlock isa roundBody s = some s' ∧
      s'.gpr .esi = r ∧ s'.gpr .edi = l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esp = s.gpr .esp ∧
      VG.Frame [VG.Proof.TripleDes.X86.spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, value, rd₁, wr₁, keep₁, frame₁⟩ := VG.Proof.TripleDes.X86.boxes_ok (List.range 8)
    (fun i hi => List.mem_range.mp hi) r k s pre hr hk
  obtain ⟨s₂, run₂, left, right, rd₂, wr₂, mem₂, base₂, sp₂⟩ := VG.Proof.TripleDes.X86.swapHalves_ok s₁
  refine ⟨s₂, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁,
    base₂.trans (keep₁ .ebp (by decide)), sp₂.trans (keep₁ .esp (by decide)), ?_⟩
  · simp only [roundBody, VG.Proof.TripleDes.X86.runBoxes_append, run₁, Option.bind_some, run₂]
  · exact left.trans ((keep₁ .edi (by decide)).trans hr)
  · rw [right, value, VG.Proof.TripleDes.X86.contributions_roundFunction, hl]
  · rw [mem₂]; exact frame₁
end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.RoundAdvance`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd VG.Impl.TripleDes.X86

def roundCount (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .ebp) 5) 32

def nextPtr (d : Spec.TripleDes.Direction) (s : State) : BitVec 32 :=
  if d = .encrypt then VG.Proof.TripleDes.X86.roundKeyPtr s + 8 else VG.Proof.TripleDes.X86.roundKeyPtr s - 8

def advanceMem (d : Spec.TripleDes.Direction) (s : State) : Mem :=
  (s.mem.writeW (wordAddr (s.gpr .ebp) 4) (VG.Proof.TripleDes.X86.nextPtr d s)).writeW
    (wordAddr (s.gpr .ebp) 5) (VG.Proof.TripleDes.X86.roundCount s - 1)

theorem counter_ptr_sep (s : State) (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32) :
    Mem.Sep (wordAddr (s.gpr .ebp) 5) 4 (wordAddr (s.gpr .ebp) 4) 4 := by
  change Mem.Sep (addr (s.gpr .ebp) 20) 4 (addr (s.gpr .ebp) 16) 4
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sep _ (by decide) (by decide) (by decide)

theorem roundAdvance_ok (d : Spec.TripleDes.Direction) (s : State) (hok : Ok VG.Proof.TripleDes.X86.sboxCfg s) :
    ∃ s', runBlock isa (roundAdvance d) s = some s' ∧
      s'.mem = VG.Proof.TripleDes.X86.advanceMem d s ∧ s'.zf = some ((VG.Proof.TripleDes.X86.roundCount s - 1) == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) := by
  have hw4 := hok.slotIn 4 (by decide)
  have hw5 := hok.slotIn 5 (by decide)
  have hr4 : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 4) 4 := by
    obtain ⟨r, h, hc⟩ := hw4; exact ⟨r, List.mem_append_right _ h, hc⟩
  have hr5 : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 5) 4 := by
    obtain ⟨r, h, hc⟩ := hw5; exact ⟨r, List.mem_append_right _ h, hc⟩
  have hsep := VG.Proof.TripleDes.X86.counter_ptr_sep s hok.fit
  simp only [wordAddr, addr, VG.Proof.TripleDes.X86.sboxCfg] at hw4 hw5 hr4 hr5 hsep
  cases d <;> refine ⟨_, by
    simp only [roundAdvance, reduceCtorEq, ite_true, ite_false, runBlock_cons,
      runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load32, State.store32,
      State.ea, memOp, gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_true, ite_false,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      hw4, hw5, hr4, hr5,
      Option.bind_some, Option.map_some]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp only [mem_setReg, mem_arithFlags, VG.Proof.TripleDes.X86.advanceMem, VG.Proof.TripleDes.X86.nextPtr, VG.Proof.TripleDes.X86.roundKeyPtr,
    VG.Proof.TripleDes.X86.roundCount, reduceCtorEq, ite_true, ite_false, wordAddr, addr,
    gpr_setReg, gpr_arithFlags,
    rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, zf_setReg, zf_arithFlags]
  all_goals try rw [Mem.readW_writeW_sep hsep (by decide)]
  all_goals try rfl
  all_goals
    intro r hr
    simp only [hr, ite_false]
end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.RoundStep`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)

def workRegion (s : State) : Region := ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 16, 432⟩

theorem spill_sub_work (s : State) : Region.Sub (VG.Proof.TripleDes.X86.spillRegion s) (VG.Proof.TripleDes.X86.workRegion s) :=
  Offset.sub _ (by decide) (by decide)

theorem count_spill_disjoint (s : State) (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32) :
    (⟨wordAddr (s.gpr .ebp) 5, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.spillRegion s) := by
  change (⟨addr (s.gpr .ebp) 20, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.spillRegion s)
  rw [addr_eq (by omega)]
  exact Offset.disjoint _ (by decide) (by decide) (by decide)

theorem advance_frame (d : Spec.TripleDes.Direction) (s : State)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32) :
    VG.Frame [VG.Proof.TripleDes.X86.workRegion s] s.mem (VG.Proof.TripleDes.X86.advanceMem d s) := by
  have h4 : (VG.Proof.TripleDes.X86.workRegion s).Contains (wordAddr (s.gpr .ebp) 4) 4 := by
    change (VG.Proof.TripleDes.X86.workRegion s).Contains (addr (s.gpr .ebp) 16) 4
    rw [addr_eq (by omega)]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  have h5 : (VG.Proof.TripleDes.X86.workRegion s).Contains (wordAddr (s.gpr .ebp) 5) 4 := by
    change (VG.Proof.TripleDes.X86.workRegion s).Contains (addr (s.gpr .ebp) 20) 4
    rw [addr_eq (by omega)]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  exact ((Frame.refl [VG.Proof.TripleDes.X86.workRegion s] s.mem).writeW (List.mem_singleton_self _) _ h4).writeW
    (List.mem_singleton_self _) _ h5

theorem countDown_rules : ∀ n < 17, 1 ≤ n →
    (BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1)) ∧
    (!(BitVec.ofNat 32 n - 1 == 0)) = decide (n ≠ 1) := by decide +kernel

theorem roundStep_ok (d : Spec.TripleDes.Direction) (s : State)
    (l r : BitVec 32) (k : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn' : n < 17)
    (hl : s.gpr .esi = l) (hr : s.gpr .edi = r) (hk : VG.Proof.TripleDes.X86.roundKeyWord s = k)
    (pre : VG.Proof.TripleDes.X86.BoxPre s) (hcount : VG.Proof.TripleDes.X86.roundCount s = BitVec.ofNat 32 n) :
    ∃ s', runBlock isa (roundBody ++ roundAdvance d) s = some s' ∧
      s'.gpr .esi = r ∧ s'.gpr .edi = l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48) ∧
      VG.Proof.TripleDes.X86.roundKeyPtr s' = VG.Proof.TripleDes.X86.nextPtr d s ∧ VG.Proof.TripleDes.X86.roundCount s' = BitVec.ofNat 32 (n - 1) ∧
      isa.eval .ne s' = some (decide (n ≠ 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esp = s.gpr .esp ∧
      VG.Frame [VG.Proof.TripleDes.X86.workRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, left₁, right₁, rd₁, wr₁, base₁, sp₁, frame₁⟩ := VG.Proof.TripleDes.X86.roundBody_ok s l r k hl hr hk pre
  obtain ⟨pre₁, _⟩ := pre.frame base₁ rd₁ wr₁ frame₁
  have ptr₁ := VG.Proof.TripleDes.X86.roundKeyPtr_frame pre base₁ frame₁
  have count₁ : VG.Proof.TripleDes.X86.roundCount s₁ = VG.Proof.TripleDes.X86.roundCount s := by
    unfold VG.Proof.TripleDes.X86.roundCount
    rw [base₁]
    exact frame₁.readW (r := ⟨wordAddr (s.gpr .ebp) 5, 4⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact VG.Proof.TripleDes.X86.count_spill_disjoint s pre.scratch.fit)
      (by decide)
  obtain ⟨s₂, run₂, mem₂, flag₂, rd₂, wr₂, keep₂⟩ := VG.Proof.TripleDes.X86.roundAdvance_ok d s₁ pre₁.scratch
  have base₂ : s₂.gpr .ebp = s₁.gpr .ebp := keep₂ _ (by decide)
  have ptr₂ : VG.Proof.TripleDes.X86.roundKeyPtr s₂ = VG.Proof.TripleDes.X86.nextPtr d s₁ := by
    unfold VG.Proof.TripleDes.X86.roundKeyPtr
    rw [base₂, mem₂]
    have hsep : Mem.Sep (wordAddr (s₁.gpr .ebp) 4) 4 (wordAddr (s₁.gpr .ebp) 5) 4 := by
      intro a h4 h5
      exact VG.Proof.TripleDes.X86.counter_ptr_sep s₁ pre₁.scratch.fit a h5 h4
    rw [VG.Proof.TripleDes.X86.advanceMem, Mem.readW_writeW_sep hsep (by decide), Mem.readW_writeW_self32]
  have count₂ : VG.Proof.TripleDes.X86.roundCount s₂ = BitVec.ofNat 32 (n - 1) := by
    unfold VG.Proof.TripleDes.X86.roundCount
    rw [base₂, mem₂, VG.Proof.TripleDes.X86.advanceMem, Mem.readW_writeW_self32, count₁, hcount,
      (VG.Proof.TripleDes.X86.countDown_rules n hn' hn).1]
  refine ⟨s₂, ?_, (keep₂ .esi (by decide)).trans left₁,
    (keep₂ .edi (by decide)).trans right₁, ?_, count₂, ?_, rd₂.trans rd₁, wr₂.trans wr₁,
    base₂.trans base₁, (keep₂ .esp (by decide)).trans sp₁, ?_⟩
  · simp only [VG.Proof.TripleDes.X86.runBoxes_append, run₁, Option.bind_some, run₂]
  · rw [ptr₂]; simp only [VG.Proof.TripleDes.X86.nextPtr, ptr₁]
  · change VG.X86.eval .ne s₂ = _
    simp only [VG.X86.eval, flag₂, count₁, hcount, Option.map_some, (VG.Proof.TripleDes.X86.countDown_rules n hn' hn).2]
  · have hf₁ : VG.Frame [VG.Proof.TripleDes.X86.workRegion s] s.mem s₁.mem := frame₁.sub (by
      intro q hq; obtain rfl := List.mem_singleton.mp hq
      exact ⟨_, List.mem_singleton_self _, VG.Proof.TripleDes.X86.spill_sub_work s⟩)
    have hf₂ := VG.Proof.TripleDes.X86.advance_frame d s₁ pre₁.scratch.fit
    have hwork : VG.Proof.TripleDes.X86.workRegion s₁ = VG.Proof.TripleDes.X86.workRegion s := by simp only [VG.Proof.TripleDes.X86.workRegion, base₁]
    rw [hwork, ← mem₂] at hf₂
    exact hf₁.trans hf₂
end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Loop`. -/
section

namespace VG.Proof.TripleDes.X86

open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix feistelStep)

def keyAddr (base : BitVec 32) (direction : Direction) (j : Nat) : BitVec 32 :=
  base + BitVec.ofNat 32 (8 * (if direction = .encrypt then j else 15 - j))

def readKey (m : Mem) (ptr : BitVec 32) : BitVec 64 :=
  m.readW (wordAddr ptr 1) 32 ++ m.readW (wordAddr ptr 0) 32

theorem readKey_frame {m m' : Mem} {ptr : BitVec 32} {regions : List Region}
    (hf : VG.Frame regions m m')
    (sep : ∀ j < 2, ∀ r ∈ regions, (⟨wordAddr ptr j, 4⟩ : Region).Disjoint r) :
    VG.Proof.TripleDes.X86.readKey m' ptr = VG.Proof.TripleDes.X86.readKey m ptr := by
  exact congrArg₂ (fun hi lo : BitVec 32 => hi ++ lo)
    (hf.readW (a := wordAddr ptr 1) (w := 32) (r := ⟨wordAddr ptr 1, 4⟩)
      (Region.contains_self _ _) (sep 1 (by decide)) (by decide))
    (hf.readW (a := wordAddr ptr 0) (w := 32) (r := ⟨wordAddr ptr 0, 4⟩)
      (Region.contains_self _ _) (sep 0 (by decide)) (by decide))

theorem keyAddr_step (base : BitVec 32) (direction : Direction) (j : Nat) (hj : j < 15) :
    (if direction = .encrypt then VG.Proof.TripleDes.X86.keyAddr base direction j + 8
      else VG.Proof.TripleDes.X86.keyAddr base direction j - 8) = VG.Proof.TripleDes.X86.keyAddr base direction (j + 1) := by
  cases direction
  · change base + BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 8 = base + BitVec.ofNat 32 (8 * (j + 1))
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega)
  · change base + BitVec.ofNat 32 (8 * (15 - j)) - BitVec.ofNat 32 8 = base + BitVec.ofNat 32 (8 * (15 - (j + 1)))
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      Offset.ofNat_sub_ofNat (by omega)]
    exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega)

def endPointer (base : BitVec 32) (d : Direction) : BitVec 32 :=
  if d = .encrypt then base + 128 else base - 8

theorem keyAddr_end (base : BitVec 32) (d : Direction) :
    (if d = .encrypt then VG.Proof.TripleDes.X86.keyAddr base d 15 + 8 else VG.Proof.TripleDes.X86.keyAddr base d 15 - 8) = VG.Proof.TripleDes.X86.endPointer base d := by
  cases d <;> simp only [VG.Proof.TripleDes.X86.endPointer, VG.Proof.TripleDes.X86.keyAddr, reduceCtorEq, ite_true, ite_false, Nat.reduceSub, Nat.reduceMul]
  · change base + BitVec.ofNat 32 120 + BitVec.ofNat 32 8 = base + BitVec.ofNat 32 128
    rw [Offset.add_ofNat_add_ofNat]
  · rw [BitVec.add_zero]

structure LoopInv (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (n : Nat) (s : State) : Prop where
  positive : 1 ≤ n
  bounded : n ≤ 16
  left : s.gpr .esi = (roundPrefix keys direction (16 - n) v).1
  right : s.gpr .edi = (roundPrefix keys direction (16 - n) v).2
  counter : VG.Proof.TripleDes.X86.roundCount s = BitVec.ofNat 32 n
  pointer : VG.Proof.TripleDes.X86.roundKeyPtr s = VG.Proof.TripleDes.X86.keyAddr base direction (16 - n)
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  base : s.gpr .ebp = origin.gpr .ebp
  sp : s.gpr .esp = origin.gpr .esp
  frame : VG.Frame [VG.Proof.TripleDes.X86.workRegion origin] origin.mem s.mem

structure LoopPost (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .esi = (roundPrefix keys direction 16 v).1
  right : s.gpr .edi = (roundPrefix keys direction 16 v).2
  counter : VG.Proof.TripleDes.X86.roundCount s = 0
  pointer : VG.Proof.TripleDes.X86.roundKeyPtr s = VG.Proof.TripleDes.X86.endPointer base direction
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  base : s.gpr .ebp = origin.gpr .ebp
  sp : s.gpr .esp = origin.gpr .esp
  frame : VG.Frame [VG.Proof.TripleDes.X86.workRegion origin] origin.mem s.mem

theorem loopStep (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok VG.Proof.TripleDes.X86.sboxCfg origin)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (VG.Proof.TripleDes.X86.keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (VG.Proof.TripleDes.X86.keyAddr base direction j) t, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.workRegion origin))
    (hslots : ∀ j < 16, ∀ k < 128, ∀ t < 2,
      Mem.Sep (wordAddr (origin.gpr .ebp) k) 4 (wordAddr (VG.Proof.TripleDes.X86.keyAddr base direction j) t) 4)
    (hkeys : ∀ j < 16, (VG.Proof.TripleDes.X86.readKey origin.mem (VG.Proof.TripleDes.X86.keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j)
    (n : Nat) (s : State) (hs : VG.Proof.TripleDes.X86.LoopInv keys direction base origin v n s) :
    WP isa (.block (roundBody ++ roundAdvance direction)) s (fun s' =>
      (isa.eval .ne s' = some false ∧ VG.Proof.TripleDes.X86.LoopPost keys direction base origin v s') ∨
      (isa.eval .ne s' = some true ∧ ∃ m < n, VG.Proof.TripleDes.X86.LoopInv keys direction base origin v m s')) := by
  have hj : 16 - n < 16 := by omega_using [hs.positive]
  have hwork : VG.Proof.TripleDes.X86.workRegion s = VG.Proof.TripleDes.X86.workRegion origin := by simp only [VG.Proof.TripleDes.X86.workRegion, hs.base]
  have hokS : Ok VG.Proof.TripleDes.X86.sboxCfg s := hok.congr hs.base hs.base hs.rd hs.wr
  have preS : VG.Proof.TripleDes.X86.BoxPre s := by
    refine ⟨hokS, ?_, ?_, ?_⟩
    · rw [hs.rd, hs.wr, hs.pointer]; exact hread _ hj
    · intro t ht a ha hb
      have hsw := VG.Proof.TripleDes.X86.spill_sub_work s a hb
      rw [hwork] at hsw
      rw [hs.pointer] at ha
      exact hsep _ hj t ht a ha hsw
    · rw [hs.base, hs.pointer]; exact hslots _ hj
  have hk : (VG.Proof.TripleDes.X86.roundKeyWord s).setWidth 48 = roundKey keys direction (16 - n) := by
    change (VG.Proof.TripleDes.X86.readKey s.mem (VG.Proof.TripleDes.X86.roundKeyPtr s)).setWidth 48 = _
    rw [hs.pointer]
    have hmem := VG.Proof.TripleDes.X86.readKey_frame hs.frame (ptr := VG.Proof.TripleDes.X86.keyAddr base direction (16 - n))
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hsep _ hj t ht)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hkeys _ hj)
  obtain ⟨s', run, left, right, ptr, count, flag, rd, wr, keptBase, keptSp, frame⟩ :=
    VG.Proof.TripleDes.X86.roundStep_ok direction s _ _ (VG.Proof.TripleDes.X86.roundKeyWord s) n hs.positive
      (by omega_using [hs.bounded]) hs.left hs.right rfl preS hs.counter
  have hidx : 16 - (n - 1) = 16 - n + 1 := by
    omega_using [hs.positive, hs.bounded]
  have hleft : s'.gpr .esi = (roundPrefix keys direction (16 - (n - 1)) v).1 := by
    rw [hidx]
    exact left.trans (congrArg (fun pair => pair.1)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hright : s'.gpr .edi = (roundPrefix keys direction (16 - (n - 1)) v).2 := by
    rw [hidx]
    have hval := congrArg (fun key =>
      ((roundPrefix keys direction (16 - n) v).1 ^^^
        Spec.TripleDes.roundFunction (roundPrefix keys direction (16 - n) v).2 key)) hk
    exact (right.trans hval).trans (congrArg (fun pair => pair.2)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hframe : VG.Frame [VG.Proof.TripleDes.X86.workRegion origin] origin.mem s'.mem := by
    rw [hwork] at frame
    exact hs.frame.trans frame
  refine WP.of_runBlock ⟨s', run, ?_⟩
  by_cases hlast : n = 1
  · left
    refine ⟨?_, ?_⟩
    · simpa only [hlast, ne_eq, not_true_eq_false, decide_false] using flag
    · subst n
      exact ⟨hleft, hright, count, by
        rw [ptr, VG.Proof.TripleDes.X86.nextPtr, hs.pointer]
        exact VG.Proof.TripleDes.X86.keyAddr_end base direction, rd.trans hs.rd, wr.trans hs.wr, keptBase.trans hs.base, keptSp.trans hs.sp, hframe⟩
  · right
    refine ⟨?_, n - 1, by omega_using [hs.positive], ?_⟩
    · simpa only [hlast, ne_eq, not_false_eq_true, decide_true] using flag
    · refine ⟨by omega_using [hs.positive, hlast], by omega_using [hs.bounded],
        hleft, hright, count, ?_, rd.trans hs.rd, wr.trans hs.wr, keptBase.trans hs.base, keptSp.trans hs.sp, hframe⟩
      rw [ptr, VG.Proof.TripleDes.X86.nextPtr, hs.pointer, VG.Proof.TripleDes.X86.keyAddr_step base direction (16 - n) (by
        omega_using [hs.positive, hlast]), ← hidx]

/-- The complete sixteen-round loop, in either key order. -/
theorem roundsLoop_ok (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok VG.Proof.TripleDes.X86.sboxCfg origin)
    (hl : origin.gpr .esi = v.1) (hr : origin.gpr .edi = v.2)
    (hptr : VG.Proof.TripleDes.X86.roundKeyPtr origin = VG.Proof.TripleDes.X86.keyAddr base direction 0)
    (hcount : VG.Proof.TripleDes.X86.roundCount origin = BitVec.ofNat 32 16)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (VG.Proof.TripleDes.X86.keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (VG.Proof.TripleDes.X86.keyAddr base direction j) t, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.workRegion origin))
    (hslots : ∀ j < 16, ∀ k < 128, ∀ t < 2,
      Mem.Sep (wordAddr (origin.gpr .ebp) k) 4 (wordAddr (VG.Proof.TripleDes.X86.keyAddr base direction j) t) 4)
    (hkeys : ∀ j < 16, (VG.Proof.TripleDes.X86.readKey origin.mem (VG.Proof.TripleDes.X86.keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j) :
    WP isa (.loop (.block (roundBody ++ roundAdvance direction)) .ne)
      origin (VG.Proof.TripleDes.X86.LoopPost keys direction base origin v) := by
  apply WP.loop (M := isa) (body := .block (roundBody ++ roundAdvance direction))
    (c := .ne) (Q := VG.Proof.TripleDes.X86.LoopPost keys direction base origin v) (VG.Proof.TripleDes.X86.LoopInv keys direction base origin v)
    (VG.Proof.TripleDes.X86.loopStep keys direction base origin v hok hread hsep hslots hkeys)
    16 origin
  exact ⟨by decide, by decide, hl, hr, hcount, hptr, rfl, rfl, rfl, rfl, Frame.refl _ _⟩

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.PassStart`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction)

def scheduleArg (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .esp) 1) 32

def startAddr (c : Nat) (d : Direction) (s : State) : BitVec 32 :=
  VG.Proof.TripleDes.X86.scheduleArg s + BitVec.ofNat 32 (128 * c + if d = .encrypt then 0 else 120)

def startMem (c : Nat) (d : Direction) (s : State) : Mem :=
  (s.mem.writeW (wordAddr (s.gpr .ebp) 4) (VG.Proof.TripleDes.X86.startAddr c d s)).writeW
    (wordAddr (s.gpr .ebp) 5) (16 : BitVec 32)

theorem passStart_ok (c : Nat) (d : Direction) (s : State) (hok : Ok VG.Proof.TripleDes.X86.sboxCfg s)
    (hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 1) 4) :
    ∃ s', runBlock isa (passStart c d) s = some s' ∧ s'.mem = VG.Proof.TripleDes.X86.startMem c d s ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) := by
  have hw4 := hok.slotIn 4 (by decide)
  have hw5 := hok.slotIn 5 (by decide)
  simp only [wordAddr, addr, VG.Proof.TripleDes.X86.sboxCfg] at hw4 hw5 hr
  refine ⟨_, by
    simp only [passStart, imm, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, State.load32, State.store32, State.ea, memOp, hw4, hw5, hr,
      ite_true, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · intro r hr
    simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]

/-- Starting a DES pass writes only its public pointer and round count. -/
theorem start_frame (c : Nat) (d : Direction) (s : State)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32) : VG.Frame [VG.Proof.TripleDes.X86.workRegion s] s.mem (VG.Proof.TripleDes.X86.startMem c d s) := by
  have h4 : (VG.Proof.TripleDes.X86.workRegion s).Contains (wordAddr (s.gpr .ebp) 4) 4 := by
    change (VG.Proof.TripleDes.X86.workRegion s).Contains (addr (s.gpr .ebp) 16) 4
    rw [addr_eq (by omega)]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  have h5 : (VG.Proof.TripleDes.X86.workRegion s).Contains (wordAddr (s.gpr .ebp) 5) 4 := by
    change (VG.Proof.TripleDes.X86.workRegion s).Contains (addr (s.gpr .ebp) 20) 4
    rw [addr_eq (by omega)]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  exact ((Frame.refl [VG.Proof.TripleDes.X86.workRegion s] s.mem).writeW (List.mem_singleton_self _) _ h4).writeW
    (List.mem_singleton_self _) _ h5

theorem start_pointer (c : Nat) (d : Direction) (s : State) (t : State)
    (base : t.gpr .ebp = s.gpr .ebp) (mem : t.mem = VG.Proof.TripleDes.X86.startMem c d s)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32) :
    VG.Proof.TripleDes.X86.roundKeyPtr t = VG.Proof.TripleDes.X86.startAddr c d s ∧ VG.Proof.TripleDes.X86.roundCount t = 16 := by
  have hsep : Mem.Sep (wordAddr (s.gpr .ebp) 4) 4 (wordAddr (s.gpr .ebp) 5) 4 := by
    intro a h4 h5; exact VG.Proof.TripleDes.X86.counter_ptr_sep s fit a h5 h4
  constructor
  · unfold VG.Proof.TripleDes.X86.roundKeyPtr
    rw [base, mem, VG.Proof.TripleDes.X86.startMem, Mem.readW_writeW_sep hsep (by decide), Mem.readW_writeW_self32]
  · unfold VG.Proof.TripleDes.X86.roundCount
    rw [base, mem, VG.Proof.TripleDes.X86.startMem, Mem.readW_writeW_self32]
end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Pass`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix)

structure PassPost (keys : DesSchedule) (d : Direction) (origin : State)
    (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .esi = (roundPrefix keys d 16 v).2
  right : s.gpr .edi = (roundPrefix keys d 16 v).1
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  base : s.gpr .ebp = origin.gpr .ebp
  sp : s.gpr .esp = origin.gpr .esp
  frame : VG.Frame [VG.Proof.TripleDes.X86.workRegion origin] origin.mem s.mem

theorem roundsWithSwap_ok (keys : DesSchedule) (d : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (hok : Ok VG.Proof.TripleDes.X86.sboxCfg origin)
    (hl : origin.gpr .esi = v.1) (hr : origin.gpr .edi = v.2)
    (hptr : VG.Proof.TripleDes.X86.roundKeyPtr origin = VG.Proof.TripleDes.X86.keyAddr base d 0) (hcount : VG.Proof.TripleDes.X86.roundCount origin = 16)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (VG.Proof.TripleDes.X86.keyAddr base d j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (VG.Proof.TripleDes.X86.keyAddr base d j) t, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.workRegion origin))
    (hslots : ∀ j < 16, ∀ k < 128, ∀ t < 2,
      Mem.Sep (wordAddr (origin.gpr .ebp) k) 4 (wordAddr (VG.Proof.TripleDes.X86.keyAddr base d j) t) 4)
    (hkeys : ∀ j < 16, (VG.Proof.TripleDes.X86.readKey origin.mem (VG.Proof.TripleDes.X86.keyAddr base d j)).setWidth 48 = roundKey keys d j) :
    WP isa (.seq (.loop (.block (roundBody ++ roundAdvance d)) .ne) (.block swapHalves))
      origin (VG.Proof.TripleDes.X86.PassPost keys d origin v) := by
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86.roundsLoop_ok keys d base origin v hok hl hr hptr hcount hread hsep hslots hkeys)
  intro s hs
  obtain ⟨s', run, left, right, rd, wr, mem, keptBase, keptSp⟩ := VG.Proof.TripleDes.X86.swapHalves_ok s
  apply WP.of_runBlock
  refine ⟨s', run, left.trans hs.right, right.trans hs.left, rd.trans hs.rd, wr.trans hs.wr,
    keptBase.trans hs.base, keptSp.trans hs.sp, ?_⟩
  rw [mem]; exact hs.frame

theorem pass_ok (c : Nat) (keys : DesSchedule) (d : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (hok : Ok VG.Proof.TripleDes.X86.sboxCfg origin)
    (hl : origin.gpr .esi = v.1) (hr : origin.gpr .edi = v.2)
    (hptr : VG.Proof.TripleDes.X86.startAddr c d origin = VG.Proof.TripleDes.X86.keyAddr base d 0)
    (harg : InRegions (origin.rd ++ origin.wr) (wordAddr (origin.gpr .esp) 1) 4)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (VG.Proof.TripleDes.X86.keyAddr base d j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (VG.Proof.TripleDes.X86.keyAddr base d j) t, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.workRegion origin))
    (hslots : ∀ j < 16, ∀ k < 128, ∀ t < 2,
      Mem.Sep (wordAddr (origin.gpr .ebp) k) 4 (wordAddr (VG.Proof.TripleDes.X86.keyAddr base d j) t) 4)
    (hkeys : ∀ j < 16, (VG.Proof.TripleDes.X86.readKey origin.mem (VG.Proof.TripleDes.X86.keyAddr base d j)).setWidth 48 = roundKey keys d j) :
    WP isa (pass c d) origin (VG.Proof.TripleDes.X86.PassPost keys d origin v) := by
  obtain ⟨s, run, mem, rd, wr, regs⟩ := VG.Proof.TripleDes.X86.passStart_ok c d origin hok harg
  have keptBase := regs .ebp (by decide)
  have keptSp := regs .esp (by decide)
  have hwork : VG.Proof.TripleDes.X86.workRegion s = VG.Proof.TripleDes.X86.workRegion origin := by simp only [VG.Proof.TripleDes.X86.workRegion, keptBase]
  have hf : VG.Frame [VG.Proof.TripleDes.X86.workRegion origin] origin.mem s.mem := by
    rw [mem]; exact VG.Proof.TripleDes.X86.start_frame c d origin hok.fit
  have hkeysS : ∀ j < 16, (VG.Proof.TripleDes.X86.readKey s.mem (VG.Proof.TripleDes.X86.keyAddr base d j)).setWidth 48 = roundKey keys d j := by
    intro j hj
    have heq := VG.Proof.TripleDes.X86.readKey_frame hf (ptr := VG.Proof.TripleDes.X86.keyAddr base d j)
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hsep j hj t ht)
    exact (congrArg (BitVec.setWidth 48) heq).trans (hkeys j hj)
  have hreadS : ∀ j < 16, ∀ t < 2, InRegions (s.rd ++ s.wr) (wordAddr (VG.Proof.TripleDes.X86.keyAddr base d j) t) 4 := by
    rw [rd, wr]; exact hread
  have hsepS : ∀ j < 16, ∀ t < 2, (⟨wordAddr (VG.Proof.TripleDes.X86.keyAddr base d j) t, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.workRegion s) := by
    rw [hwork]; exact hsep
  have hslotsS : ∀ j < 16, ∀ k < 128, ∀ t < 2,
      Mem.Sep (wordAddr (s.gpr .ebp) k) 4 (wordAddr (VG.Proof.TripleDes.X86.keyAddr base d j) t) 4 := by
    rw [keptBase]; exact hslots
  have start := VG.Proof.TripleDes.X86.start_pointer c d origin s keptBase mem hok.fit
  have htail := VG.Proof.TripleDes.X86.roundsWithSwap_ok keys d base s v (hok.congr keptBase keptBase rd wr)
    ((regs .esi (by decide)).trans hl) ((regs .edi (by decide)).trans hr)
    (start.1.trans hptr) start.2 hreadS hsepS hslotsS hkeysS
  apply WP.seq
  apply WP.of_runBlock
  refine ⟨s, run, WP.mono htail ?_⟩
  intro s' hs
  refine ⟨hs.left, hs.right, hs.rd.trans rd, hs.wr.trans wr, hs.base.trans keptBase,
    hs.sp.trans keptSp, ?_⟩
  have hframe := hs.frame
  rw [hwork] at hframe
  exact hf.trans hframe
end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.WordState`. -/
section

namespace VG.Proof.TripleDes.X86

open VG VG.X86 VG.Impl.TripleDes.X86
open VG.Proof.TripleDes (desCore roundPrefix)

/-- A DES word held as two 32-bit Feistel registers. -/
structure WordState (x : BitVec 64) (s : State) : Prop where
  left : s.gpr .esi = ((x >>> 32).setWidth 32)
  right : s.gpr .edi = (x.setWidth 32)

theorem PassPost.wordState {keys : Spec.TripleDes.DesSchedule}
    {direction : Spec.TripleDes.Direction} {origin s : State} {x : BitVec 64}
    (hs : VG.Proof.TripleDes.X86.PassPost keys direction origin ((x >>> 32).setWidth 32, x.setWidth 32) s) :
    VG.Proof.TripleDes.X86.WordState (desCore keys direction x) s := by
  have hcore := VG.Proof.TripleDes.desCore_roundPrefix keys direction x
  let halves := roundPrefix keys direction 16 ((x >>> 32).setWidth 32, x.setWidth 32)
  have hleft : ((desCore keys direction x >>> 32).setWidth 32) = halves.2 :=
    (congrArg (fun v : BitVec 64 => ((v >>> 32).setWidth 32)) hcore).trans
      (VG.Proof.TripleDes.appended_left halves.2 halves.1)
  have hright : ((desCore keys direction x).setWidth 32) = halves.1 :=
    (congrArg (fun v : BitVec 64 => (v.setWidth 32)) hcore).trans
      (VG.Proof.TripleDes.appended_right halves.2 halves.1)
  exact ⟨hs.left.trans hleft.symm, hs.right.trans hright.symm⟩

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Ready`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def componentBase (base : BitVec 32) (component : Nat) : BitVec 32 :=
  base + BitVec.ofNat 32 (128 * component)

structure Ready (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) : Prop where
  spills : Ok VG.Proof.TripleDes.X86.sboxCfg s
  schedule : VG.Proof.TripleDes.X86.scheduleArg s = base
  argRead : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 1) 4
  argSeparate : (⟨wordAddr (s.gpr .esp) 1, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.workRegion s)
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    InRegions (s.rd ++ s.wr) (wordAddr (VG.Proof.TripleDes.X86.keyAddr (VG.Proof.TripleDes.X86.componentBase base c) d j) t) 4
  separate : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    (⟨wordAddr (VG.Proof.TripleDes.X86.keyAddr (VG.Proof.TripleDes.X86.componentBase base c) d j) t, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.workRegion s)
  slots : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ k < 128, ∀ t < 2,
    Mem.Sep (wordAddr (s.gpr .ebp) k) 4 (wordAddr (VG.Proof.TripleDes.X86.keyAddr (VG.Proof.TripleDes.X86.componentBase base c) d j) t) 4
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (VG.Proof.TripleDes.X86.readKey s.mem (VG.Proof.TripleDes.X86.keyAddr (VG.Proof.TripleDes.X86.componentBase base c) d j)).setWidth 48 = roundKey (keys c) d j

theorem Ready.congr {keys : Nat → DesSchedule} {base : BitVec 32} {s t : State}
    (hs : VG.Proof.TripleDes.X86.Ready keys base s) (hbase : t.gpr .ebp = s.gpr .ebp) (hsp : t.gpr .esp = s.gpr .esp)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : VG.Frame [VG.Proof.TripleDes.X86.workRegion s] s.mem t.mem) : VG.Proof.TripleDes.X86.Ready keys base t := by
  have hwork : VG.Proof.TripleDes.X86.workRegion t = VG.Proof.TripleDes.X86.workRegion s := by unfold VG.Proof.TripleDes.X86.workRegion; rw [hbase]
  refine ⟨hs.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold VG.Proof.TripleDes.X86.scheduleArg
    rw [hsp]
    have hm := hf.readW (a := wordAddr (s.gpr .esp) 1) (w := 32)
      (r := ⟨wordAddr (s.gpr .esp) 1, 4⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hs.argSeparate) (by decide)
    exact hm.trans hs.schedule
  · rw [hsp, hrd, hwr]; exact hs.argRead
  · rw [hsp, hwork]; exact hs.argSeparate
  · rw [hrd, hwr]; exact hs.read
  · rw [hwork]; exact hs.separate
  · rw [hbase]; exact hs.slots
  · intro c hc d j hj
    have hm := VG.Proof.TripleDes.X86.readKey_frame hf (ptr := VG.Proof.TripleDes.X86.keyAddr (VG.Proof.TripleDes.X86.componentBase base c) d j)
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hs.separate c hc d j hj t ht)
    exact (congrArg (BitVec.setWidth 48) hm).trans (hs.values c hc d j hj)

theorem Ready.congrFrame {keys : Nat → DesSchedule} {base : BitVec 32} {s t : State}
    (hs : VG.Proof.TripleDes.X86.Ready keys base s) (hbase : t.gpr .ebp = s.gpr .ebp) (hsp : t.gpr .esp = s.gpr .esp)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (rs : List Region) (hf : VG.Frame rs s.mem t.mem)
    (hargs : ∀ q ∈ rs, (⟨wordAddr (s.gpr .esp) 1, 4⟩ : Region).Disjoint q)
    (hkeys : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ i < 2, ∀ q ∈ rs,
      (⟨wordAddr (VG.Proof.TripleDes.X86.keyAddr (VG.Proof.TripleDes.X86.componentBase base c) d j) i, 4⟩ : Region).Disjoint q) :
    VG.Proof.TripleDes.X86.Ready keys base t := by
  have hwork : VG.Proof.TripleDes.X86.workRegion t = VG.Proof.TripleDes.X86.workRegion s := by unfold VG.Proof.TripleDes.X86.workRegion; rw [hbase]
  refine ⟨hs.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold VG.Proof.TripleDes.X86.scheduleArg
    rw [hsp]
    have hm := hf.readW (a := wordAddr (s.gpr .esp) 1) (w := 32)
      (r := ⟨wordAddr (s.gpr .esp) 1, 4⟩) (Region.contains_self _ _)
      hargs (by decide)
    exact hm.trans hs.schedule
  · rw [hsp, hrd, hwr]; exact hs.argRead
  · rw [hsp, hwork]; exact hs.argSeparate
  · rw [hrd, hwr]; exact hs.read
  · rw [hwork]; exact hs.separate
  · rw [hbase]; exact hs.slots
  · intro c hc d j hj
    have hm := VG.Proof.TripleDes.X86.readKey_frame hf (ptr := VG.Proof.TripleDes.X86.keyAddr (VG.Proof.TripleDes.X86.componentBase base c) d j)
      (hkeys c hc d j hj)
    exact (congrArg (BitVec.setWidth 48) hm).trans (hs.values c hc d j hj)

structure Stable (origin s : State) : Prop where
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  bp : s.gpr .ebp = origin.gpr .ebp
  sp : s.gpr .esp = origin.gpr .esp
  frame : VG.Frame [VG.Proof.TripleDes.X86.workRegion origin] origin.mem s.mem

theorem Stable.trans {s t u : State} (hs : VG.Proof.TripleDes.X86.Stable s t) (ht : VG.Proof.TripleDes.X86.Stable t u) : VG.Proof.TripleDes.X86.Stable s u := by
  have hwork : VG.Proof.TripleDes.X86.workRegion t = VG.Proof.TripleDes.X86.workRegion s := by unfold VG.Proof.TripleDes.X86.workRegion; rw [hs.bp]
  have hf := ht.frame
  rw [hwork] at hf
  exact ⟨ht.rd.trans hs.rd, ht.wr.trans hs.wr, ht.bp.trans hs.bp, ht.sp.trans hs.sp,
    hs.frame.trans hf⟩

theorem passPointer (base : BitVec 32) (c : Nat) (d : Direction) (s : State)
    (hs : VG.Proof.TripleDes.X86.scheduleArg s = base) : VG.Proof.TripleDes.X86.startAddr c d s = VG.Proof.TripleDes.X86.keyAddr (VG.Proof.TripleDes.X86.componentBase base c) d 0 := by
  cases d <;> simp only [VG.Proof.TripleDes.X86.startAddr, VG.Proof.TripleDes.X86.keyAddr, VG.Proof.TripleDes.X86.componentBase, hs, reduceCtorEq,
    ite_true, ite_false, Nat.mul_zero, Nat.sub_zero, Nat.reduceMul]
  all_goals rw [Offset.add_ofNat_add_ofNat]

theorem pass_word_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (c : Nat) (hc : c < 3) (d : Direction) (hready : VG.Proof.TripleDes.X86.Ready keys base s) (hword : VG.Proof.TripleDes.X86.WordState x s) :
    WP isa (pass c d) s (fun t => VG.Proof.TripleDes.X86.WordState (VG.Proof.TripleDes.desCore (keys c) d x) t ∧
      VG.Proof.TripleDes.X86.Ready keys base t ∧ VG.Proof.TripleDes.X86.Stable s t) := by
  apply WP.mono (VG.Proof.TripleDes.X86.pass_ok c (keys c) d (VG.Proof.TripleDes.X86.componentBase base c) s
    ((x >>> 32).setWidth 32, x.setWidth 32) hready.spills hword.left hword.right
    (VG.Proof.TripleDes.X86.passPointer base c d s hready.schedule) hready.argRead (hready.read c hc d)
    (hready.separate c hc d) (hready.slots c hc d) (hready.values c hc d))
  intro t ht
  exact ⟨ht.wordState, hready.congr ht.base ht.sp ht.rd ht.wr ht.frame,
    ⟨ht.rd, ht.wr, ht.base, ht.sp, ht.frame⟩⟩

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Body`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (desCore)

theorem threePasses_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (c₀ c₁ c₂ : Nat) (h₀ : c₀ < 3) (h₁ : c₁ < 3) (h₂ : c₂ < 3)
    (d₀ d₁ d₂ : Direction) (hready : VG.Proof.TripleDes.X86.Ready keys base s) (hword : VG.Proof.TripleDes.X86.WordState x s) :
    WP isa (.seq (pass c₀ d₀) (.seq (pass c₁ d₁) (pass c₂ d₂))) s
      (fun t => VG.Proof.TripleDes.X86.WordState (desCore (keys c₂) d₂ (desCore (keys c₁) d₁ (desCore (keys c₀) d₀ x))) t ∧
        VG.Proof.TripleDes.X86.Ready keys base t ∧ VG.Proof.TripleDes.X86.Stable s t) := by
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86.pass_word_ok keys base s x c₀ h₀ d₀ hready hword)
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86.pass_word_ok keys base s₁ _ c₁ h₁ d₁ hs₁.2.1 hs₁.1)
  intro s₂ hs₂
  apply WP.mono (VG.Proof.TripleDes.X86.pass_word_ok keys base s₂ _ c₂ h₂ d₂ hs₂.2.1 hs₂.1)
  intro s₃ hs₃
  exact ⟨hs₃.1, hs₃.2.1, hs₁.2.2.trans (hs₂.2.2.trans hs₃.2.2)⟩

def blockCore (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) : BitVec 64 :=
  match direction with
  | .encrypt => desCore (keys 2) .encrypt (desCore (keys 1) .decrypt (desCore (keys 0) .encrypt x))
  | .decrypt => desCore (keys 0) .decrypt (desCore (keys 1) .encrypt (desCore (keys 2) .decrypt x))

theorem blockBody_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (direction : Direction) (hready : VG.Proof.TripleDes.X86.Ready keys base s) (hword : VG.Proof.TripleDes.X86.WordState x s) :
    WP isa (blockBody direction) s
      (fun t => VG.Proof.TripleDes.X86.WordState (VG.Proof.TripleDes.X86.blockCore keys direction x) t ∧ VG.Proof.TripleDes.X86.Ready keys base t ∧ VG.Proof.TripleDes.X86.Stable s t) := by
  cases direction
  · exact VG.Proof.TripleDes.X86.threePasses_ok keys base s x 0 1 2 (by decide) (by decide) (by decide)
      .encrypt .decrypt .encrypt hready hword
  · exact VG.Proof.TripleDes.X86.threePasses_ok keys base s x 2 1 0 (by decide) (by decide) (by decide)
      .decrypt .encrypt .decrypt hready hword

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Permutation`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.Bitslice VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86 VG.Proof.TripleDes.X86.Linear

def permutationCfg : Cfg := { base := .ebp, slots := 0, ext := .ebp, exts := 0 }
def permutationInputs (lo hi : Reg) : List (Reg × Nat) := [(lo, 0), (hi, 1)]
def permutationBits {m : Nat} (positions : Vector Nat m) (n srcSplit dstSplit start p : Nat) : List Nat :=
  if p < dstSplit ∧ start + p < m then
    let source := n - positions.getD (m - 1 - (start + p)) 1
    [if source < srcSplit then source else 32 + source - srcSplit]
  else []
def permutationOutputs {m : Nat} (positions : Vector Nat m) (n srcSplit dstSplit : Nat) (lo hi : Reg) :
    List (Reg × (Nat → List Nat)) :=
  [(lo, VG.Proof.TripleDes.X86.permutationBits positions n srcSplit dstSplit 0),
   (hi, VG.Proof.TripleDes.X86.permutationBits positions n srcSplit (m - dstSplit) dstSplit)]

theorem initialPermutation_check :
    VG.X86.Straight.check (lanes 32 6) VG.Proof.TripleDes.X86.permutationCfg (VG.Proof.TripleDes.X86.Linear.linExt 2) (instrs initialPermutation.lit)
      (VG.Proof.TripleDes.X86.Linear.linEnv (VG.Proof.TripleDes.X86.permutationInputs .esi .edi)) (VG.Proof.TripleDes.X86.Linear.linPost 6 (VG.Proof.TripleDes.X86.permutationOutputs Spec.TripleDes.ip 64 32 32 .eax .ebx)) = true := by
  decide +kernel

theorem finalPermutation_check :
    VG.X86.Straight.check (lanes 32 6) VG.Proof.TripleDes.X86.permutationCfg (VG.Proof.TripleDes.X86.Linear.linExt 2) (instrs finalPermutation.lit)
      (VG.Proof.TripleDes.X86.Linear.linEnv (VG.Proof.TripleDes.X86.permutationInputs .edi .esi)) (VG.Proof.TripleDes.X86.Linear.linPost 6 (VG.Proof.TripleDes.X86.permutationOutputs Spec.TripleDes.fp 64 32 32 .eax .ebx)) = true := by
  decide +kernel

theorem keyPermutation1_check :
    VG.X86.Straight.check (lanes 32 6) VG.Proof.TripleDes.X86.permutationCfg (VG.Proof.TripleDes.X86.Linear.linExt 2) (instrs keyPermutation1.lit)
      (VG.Proof.TripleDes.X86.Linear.linEnv (VG.Proof.TripleDes.X86.permutationInputs .esi .edi)) (VG.Proof.TripleDes.X86.Linear.linPost 6 (VG.Proof.TripleDes.X86.permutationOutputs Spec.TripleDes.pc1 64 32 28 .eax .ebx)) = true := by
  decide +kernel

theorem keyPermutation2_check :
    VG.X86.Straight.check (lanes 32 6) VG.Proof.TripleDes.X86.permutationCfg (VG.Proof.TripleDes.X86.Linear.linExt 2) (instrs keyPermutation2.lit)
      (VG.Proof.TripleDes.X86.Linear.linEnv (VG.Proof.TripleDes.X86.permutationInputs .edi .esi)) (VG.Proof.TripleDes.X86.Linear.linPost 6 (VG.Proof.TripleDes.X86.permutationOutputs Spec.TripleDes.pc2 56 28 32 .eax .ebx)) = true := by
  decide +kernel

def packedInput (n split : Nat) (lo hi : BitVec 32) : BitVec n :=
  ((hi.setWidth (n - split)) ++ lo.setWidth split).setWidth n

theorem packedInput_bit (n split : Nat) (lo hi : BitVec 32) (k : Nat)
    (hk : k < n) (hs : split ≤ n) :
    (VG.Proof.TripleDes.X86.packedInput n split lo hi).getLsbD k =
      if k < split then lo.getLsbD k else hi.getLsbD (k - split) := by
  simp only [VG.Proof.TripleDes.X86.packedInput, BitVec.getLsbD_setWidth, hk, decide_true, Bool.true_and,
    BitVec.getLsbD_append]
  by_cases h : k < split
  · simp only [h, ite_true, decide_true, Bool.true_and]
  · have hb : k - split < n - split := by omega
    simp only [h, ite_false, hb, decide_true, Bool.true_and]

theorem permutationBits_ok {m n : Nat} (positions : Vector Nat m)
    (hn : 0 < n) (split width start : Nat)
    (hs : split ≤ n) (hlo : split ≤ 32) (hhi : n - split ≤ 32)
    (hw : width + start ≤ m)
    (bounds : ∀ k < m, 1 ≤ positions.getD k 1 ∧ positions.getD k 1 ≤ n)
    (lo hi : BitVec 32) (p : Nat) (hp : p < 32) :
    VG.Proof.TripleDes.X86.Linear.xorBits (fun i => if i = 0 then lo else hi)
      (VG.Proof.TripleDes.X86.permutationBits positions n split width start p) =
    (((Spec.TripleDes.permute positions (VG.Proof.TripleDes.X86.packedInput n split lo hi) >>> start).setWidth width).setWidth 32).getLsbD p := by
  simp only [BitVec.getLsbD_setWidth, hp, decide_true, Bool.true_and, BitVec.getLsbD_ushiftRight]
  by_cases hw' : p < width
  · have hm : start + p < m := by omega
    simp only [hw', decide_true, Bool.true_and]
    have hk : m - 1 - (start + p) < m := by omega
    obtain ⟨hb, ht⟩ := bounds _ hk
    have hn' : n - positions.getD (m - 1 - (start + p)) 1 < n := by omega
    rw [VG.Proof.TripleDes.permute_bit positions _ hn _ hm, VG.Proof.TripleDes.X86.packedInput_bit _ _ _ _ _ hn' hs]
    simp only [VG.Proof.TripleDes.X86.permutationBits, hw', hm, and_self, ite_true, VG.Proof.TripleDes.X86.Linear.xorBits_cons, VG.Proof.TripleDes.X86.Linear.xorBits_nil, Bool.xor_false]
    let k := n - positions.getD (m - 1 - (start + p)) 1
    change VG.Proof.TripleDes.X86.Linear.bitOf (fun i => if i = 0 then lo else hi) (if k < split then k else 32 + k - split) =
      if k < split then lo.getLsbD k else hi.getLsbD (k - split)
    by_cases h : k < split
    · have h32 : k < 32 := by omega
      simp only [h, ite_true, VG.Proof.TripleDes.X86.Linear.bitOf, Nat.div_eq_of_lt h32, Nat.mod_eq_of_lt h32]
    · have h32 : k - split < 32 := by change n - positions.getD (m - 1 - (start + p)) 1 < n at hn'; dsimp [k]; omega
      have he : 32 + k - split = 32 * 1 + (k - split) := by omega
      simp only [h, ite_false, he, VG.Proof.TripleDes.X86.Linear.bitOf_word _ _ _ h32]
      rfl
  · simp only [hw', decide_false, Bool.false_and, VG.Proof.TripleDes.X86.permutationBits, false_and, ite_false, VG.Proof.TripleDes.X86.Linear.xorBits_nil]

theorem permutationCfg_ok (s : VG.X86.State) : Ok VG.Proof.TripleDes.X86.permutationCfg s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk; simp [VG.Proof.TripleDes.X86.permutationCfg] at hk
  · intro k hk; simp [VG.Proof.TripleDes.X86.permutationCfg] at hk
  · change (s.gpr .ebp).toNat + 4 * 0 ≤ 2 ^ 32
    have h := (s.gpr .ebp).isLt
    omega
  · intro k hk; simp [VG.Proof.TripleDes.X86.permutationCfg] at hk

theorem fixedPermutation_ok {m n : Nat} (positions : Vector Nat m)
    (hn : 0 < n) (split dstSplit : Nat)
    (hs : split ≤ n) (hlo : split ≤ 32) (hhi : n - split ≤ 32) (hd : dstSplit ≤ m)
    (bounds : ∀ k < m, 1 ≤ positions.getD k 1 ∧ positions.getD k 1 ≤ n)
    (srcLo srcHi dstLo dstHi : Reg) (is : List Instr)
    (hchk : VG.X86.Straight.check (lanes 32 6) VG.Proof.TripleDes.X86.permutationCfg (VG.Proof.TripleDes.X86.Linear.linExt 2) is
      (VG.Proof.TripleDes.X86.Linear.linEnv (VG.Proof.TripleDes.X86.permutationInputs srcLo srcHi))
      (VG.Proof.TripleDes.X86.Linear.linPost 6 (VG.Proof.TripleDes.X86.permutationOutputs positions n split dstSplit dstLo dstHi)) = true)
    (hsp : (is.all fun op => op.dst != some .esp) = true) (s : VG.X86.State) :
    ∃ s', runBlock isa is s = some s' ∧
      s'.gpr dstLo = ((Spec.TripleDes.permute positions
        (VG.Proof.TripleDes.X86.packedInput n split (s.gpr srcLo) (s.gpr srcHi))).setWidth dstSplit).setWidth 32 ∧
      s'.gpr dstHi = ((Spec.TripleDes.permute positions
        (VG.Proof.TripleDes.X86.packedInput n split (s.gpr srcLo) (s.gpr srcHi)) >>> dstSplit).setWidth (m - dstSplit)).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem ∧
      (∀ r, (is.all fun op => op.dst != some r) = true → s'.gpr r = s.gpr r) := by
  let W : Nat → BitVec 32 := fun i => if i = 0 then s.gpr srcLo else s.gpr srcHi
  obtain ⟨s', hs', out, rd, wr, keep, frame⟩ :=
    VG.Proof.TripleDes.X86.Linear.linear_ok hchk (VG.Proof.TripleDes.X86.permutationCfg_ok s) W (fun r i h => by
      simp only [VG.Proof.TripleDes.X86.permutationInputs, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact ⟨by decide, rfl⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact ⟨by decide, rfl⟩)
      (fun j hj => by simp [VG.Proof.TripleDes.X86.permutationCfg] at hj)
  refine ⟨s', hs', ?_, ?_, rd, wr, ?_, ?_, keep⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro p hp
    have h := out dstLo (VG.Proof.TripleDes.X86.permutationBits positions n split dstSplit 0) (by simp [VG.Proof.TripleDes.X86.permutationOutputs]) p hp
    rw [h]
    have hbits := VG.Proof.TripleDes.X86.permutationBits_ok positions hn split dstSplit 0 hs hlo hhi (by omega) bounds (s.gpr srcLo) (s.gpr srcHi) p hp
    simpa only [BitVec.ushiftRight_zero] using hbits
  · apply BitVec.eq_of_getLsbD_eq
    intro p hp
    have h := out dstHi (VG.Proof.TripleDes.X86.permutationBits positions n split (m - dstSplit) dstSplit)
      (by simp [VG.Proof.TripleDes.X86.permutationOutputs]) p hp
    rw [h]
    exact VG.Proof.TripleDes.X86.permutationBits_ok positions hn split (m - dstSplit) dstSplit hs hlo hhi
      (by omega) bounds _ _ p hp
  · exact keep .esp hsp
  · funext a
    apply frame a
    intro r hr hc
    simp only [slotRegion, VG.Proof.TripleDes.X86.permutationCfg, List.mem_singleton] at hr
    subst r
    simp [Region.Contains] at hc

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Bytes`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.Spec.TripleDes

theorem decodeBlock_readW (m : Mem) (p : Addr) :
    VG.Spec.TripleDes.decodeBlock (VG.Spec.TripleDes.blockAt m p) = bswap (m.readW p 32) ++ bswap (m.readW (p + 4) 32) := by
  rw [VG.Proof.TripleDes.decodeBlock_cat, bswap_readW, bswap_readW]
  simp only [VG.Proof.TripleDes.catBlock, VG.Spec.TripleDes.blockAt, Vector.getElem_ofFn,
    BitVec.add_assoc, BitVec.add_zero,
    show (1 : Addr) + 1 = 2 from by decide,
    show (2 : Addr) + 1 = 3 from by decide,
    show (4 : Addr) + 1 = 5 from by decide,
    show (5 : Addr) + 1 = 6 from by decide,
    show (6 : Addr) + 1 = 7 from by decide]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have ranges : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨
      (24 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨
      (48 ≤ i ∧ i < 56) ∨ 56 ≤ i := by omega
  rcases ranges with h | h | h | h | h | h | h | h <;>
    simp (disch := omega) only [BitVec.getLsbD_append, ite_eq_left, ite_eq_right,
      Nat.sub_sub] <;> rfl

theorem packed28 (c d : BitVec 28) :
    VG.Proof.TripleDes.X86.packedInput 56 28 (d.setWidth 32) (c.setWidth 32) = c ++ d := by
  simp only [VG.Proof.TripleDes.X86.packedInput, BitVec.setWidth_setWidth_of_le _ (by decide : 28 ≤ 32),
    BitVec.setWidth_eq]

theorem byteRev64_byte (x : BitVec 64) (i : Nat) (hi : i < 8) :
    (byteRev64 x).extractLsb' (8 * i) 8 = (x >>> (8 * (7 - i))).setWidth 8 := by
  have cases8 : ∀ k < 8, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨
      k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by decide
  rcases cases8 i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp (disch := decide) only [byteRev64, extractLsb'_append_byte_hi,
    extractLsb'_append_byte_lo, Nat.reduceMul, Nat.reduceSub,
    BitVec.setWidth_ushiftRight_eq_extractLsb, BitVec.extractLsb'_eq_self]

theorem blockAt_writeW (m : Mem) (p : Addr) (x : BitVec 64) :
    VG.Spec.TripleDes.blockAt (m.writeW p (byteRev64 x)) p = VG.Spec.TripleDes.encodeBlock x := by
  apply Vector.ext
  intro i hi
  simp only [VG.Spec.TripleDes.blockAt, VG.Spec.TripleDes.encodeBlock, Vector.getElem_ofFn, Mem.writeW, Mem.write,
    Mem.sub_ofNat_toNat p (by omega : i < 2 ^ 64), BitVec.setWidth_eq,
    hi, ite_true]
  exact VG.Proof.TripleDes.X86.byteRev64_byte x i hi

theorem bswapPair (l r : BitVec 32) : bswap r ++ bswap l = byteRev64 (l ++ r) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have ranges : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨
      (24 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨
      (48 ≤ i ∧ i < 56) ∨ 56 ≤ i := by omega
  rcases ranges with h | h | h | h | h | h | h | h <;>
    simp (disch := omega) only [bswap, byteRev64, BitVec.getLsbD_append,
      BitVec.getLsbD_extractLsb', ite_eq_left, ite_eq_right, Nat.sub_sub] <;>
    congr 2 <;> omega

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Initial`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep addr32)

def dataArg (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .esp) 2) 32

def readHead : List Instr :=
  [.mov .edx (.mem (memOp .esp 8)), .mov .edi (.mem (memOp .edx 0)),
    .mov .esi (.mem (memOp .edx 4)), .bswap .edi, .bswap .esi]

theorem readHead_ok (s : State)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4)
    (hr : ∀ i < 2, InRegions (s.rd ++ s.wr) (wordAddr (VG.Proof.TripleDes.X86.dataArg s) i) 4) :
    ∃ s', runBlock isa VG.Proof.TripleDes.X86.readHead s = some s' ∧
      s'.gpr .edi = bswap (s.mem.readW (wordAddr (VG.Proof.TripleDes.X86.dataArg s) 0) 32) ∧
      s'.gpr .esi = bswap (s.mem.readW (wordAddr (VG.Proof.TripleDes.X86.dataArg s) 1) 32) ∧
      Keep [.edi, .esi, .edx] s s' := by
  have h0 := hr 0 (by decide)
  have h1 := hr 1 (by decide)
  simp only [wordAddr, addr, VG.Proof.TripleDes.X86.dataArg] at harg h0 h1
  refine ⟨_, by
    simp only [VG.Proof.TripleDes.X86.readHead, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.ea, memOp, harg, h0, h1, ite_true,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]

theorem ip_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.ip 64 32 32 .eax .ebx .esi .edi .ecx) s = some s' ∧
      s'.gpr .eax = (Spec.TripleDes.permute Spec.TripleDes.ip
        (VG.Proof.TripleDes.X86.packedInput 64 32 (s.gpr .esi) (s.gpr .edi))).setWidth 32 ∧
      s'.gpr .ebx = ((Spec.TripleDes.permute Spec.TripleDes.ip
        (VG.Proof.TripleDes.X86.packedInput 64 32 (s.gpr .esi) (s.gpr .edi))) >>> 32).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    VG.Proof.TripleDes.X86.fixedPermutation_ok Spec.TripleDes.ip (by decide) 32 32
      (by decide) (by decide) (by decide) (by decide) (by decide)
      .esi .edi .eax .ebx (instrs initialPermutation.lit) VG.Proof.TripleDes.X86.initialPermutation_check (by decide +kernel) s
  have hcode : permuteCode Spec.TripleDes.ip 64 32 32 .eax .ebx .esi .edi .ecx = instrs initialPermutation.lit :=
    congrArg instrs initialPermutation.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run,
    lo, hi, rd, wr, sp, mem, regs⟩

structure InitialPost (x : BitVec 64) (s s' : State) : Prop where
  l : s'.gpr .esi = (x >>> 32).setWidth 32
  r : s'.gpr .edi = x.setWidth 32
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bp : s'.gpr .ebp = s.gpr .ebp
  sp : s'.gpr .esp = s.gpr .esp

theorem blockLoad_ok (s : State)
    (fit : (VG.Proof.TripleDes.X86.dataArg s).toNat + 8 ≤ 2 ^ 32)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4)
    (hr : ∀ i < 2, InRegions (s.rd ++ s.wr) (wordAddr (VG.Proof.TripleDes.X86.dataArg s) i) 4) :
    WP isa (.block blockLoad) s (VG.Proof.TripleDes.X86.InitialPost (Spec.TripleDes.permute Spec.TripleDes.ip
      (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (addr32 (VG.Proof.TripleDes.X86.dataArg s))))) s) := by
  have code : blockLoad = (VG.Proof.TripleDes.X86.readHead ++
      permuteCode Spec.TripleDes.ip 64 32 32 .eax .ebx .esi .edi .ecx) ++
      [rr .esi .ebx, rr .edi .eax] := rfl
  rw [code, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, hi₁, lo₁, keep₁⟩ := VG.Proof.TripleDes.X86.readHead_ok s harg hr
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, lo₂, hi₂, rd₂, wr₂, sp₂, mem₂, reg₂⟩ := VG.Proof.TripleDes.X86.ip_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have input : VG.Proof.TripleDes.X86.packedInput 64 32 (s₁.gpr .esi) (s₁.gpr .edi) =
      Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (addr32 (VG.Proof.TripleDes.X86.dataArg s))) := by
    rw [VG.Proof.TripleDes.X86.packedInput, lo₁, hi₁, VG.Proof.TripleDes.X86.decodeBlock_readW]
    simp only [BitVec.setWidth_eq]
    rw [show wordAddr (VG.Proof.TripleDes.X86.dataArg s) 0 = addr32 (VG.Proof.TripleDes.X86.dataArg s) from by simp [wordAddr, addr, addr32],
      show wordAddr (VG.Proof.TripleDes.X86.dataArg s) 1 = addr32 (VG.Proof.TripleDes.X86.dataArg s) + 4 from addr_eq (by omega)]
  rw [input] at lo₂ hi₂
  refine WP.of_runBlock ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, rr, readSrc, Option.map_some,
      gpr_setReg, reduceCtorEq, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, mem₂.trans keep₁.mem, rd₂.trans keep₁.rd, wr₂.trans keep₁.wr,
    ?_, ?_⟩
  · exact hi₂
  · exact lo₂
  · exact (reg₂ .ebp (by decide +kernel)).trans (keep₁.reg .ebp (by decide))
  · exact sp₂.trans (keep₁.reg .esp (by decide))

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Save`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32 Keep)

def savedReg (i : Nat) : Reg := savedRegs.getD i .ebp

def scratchArg (s : State) (slot : Nat) : BitVec 32 :=
  s.mem.readW (wordAddr (s.gpr .esp) slot) 32

def Saved (original current : State) : Prop :=
  ∀ i < 4, current.mem.readW (addr32 (current.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 32 =
    original.gpr (VG.Proof.TripleDes.X86.savedReg i)

structure SavePost (slot : Nat) (original current : State) : Prop where
  bp : current.gpr .ebp = VG.Proof.TripleDes.X86.scratchArg original slot
  rd : current.rd = original.rd
  wr : current.wr = original.wr
  reg : ∀ r, r ≠ .eax → r ≠ .ebp → current.gpr r = original.gpr r
  saved : VG.Proof.TripleDes.X86.Saved original current
  frame : VG.Frame [⟨addr32 (VG.Proof.TripleDes.X86.scratchArg original slot), 16⟩] original.mem current.mem

theorem saveWithArg_ok (s : State) (slot : Nat)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) slot) 4)
    (fit : (VG.Proof.TripleDes.X86.scratchArg s slot).toNat + 512 ≤ 2 ^ 32)
    (hw : ∀ i < 4, InRegions s.wr (addr32 (VG.Proof.TripleDes.X86.scratchArg s slot) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (saveWithArg slot)) s (VG.Proof.TripleDes.X86.SavePost slot s) := by
  have code : saveWithArg slot =
      (([.mov .eax (.mem (memOp .esp (4 * slot)))] : List Instr) ++
        VG.Proof.Rc2.X86.saveCode .eax VG.Proof.TripleDes.X86.savedReg 4) ++ [rr .ebp .eax] := by
    unfold saveWithArg
    congr 1
  rw [code, WP.block_append_iff, WP.block_append_iff]
  let s₀ := s.setReg .eax (VG.Proof.TripleDes.X86.scratchArg s slot)
  have load : runBlock isa [.mov .eax (.mem (memOp .esp (4 * slot)))] s = some s₀ := by
    have he : exec (.mov .eax (.mem (memOp .esp (4 * slot)))) s = some s₀ := by
      simp only [exec, readSrc, State.load32, State.ea, memOp]
      change (if InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) slot) 4 then
        some (VG.Proof.TripleDes.X86.scratchArg s slot) else none).map (s.setReg .eax) = some s₀
      rw [ite_eq_left harg, Option.map_some]
    simp only [runBlock_cons, he, runStep_some, runBlock_nil]
  refine WP.of_runBlock ⟨s₀, load, ?_⟩
  have ptr₀ : s₀.gpr .eax = VG.Proof.TripleDes.X86.scratchArg s slot := gpr_setReg_self _ _ _
  have hw₀ : ∀ i < 4, InRegions s₀.wr (addr32 (s₀.gpr .eax) + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [ptr₀]; exact hw
  apply WP.mono (VG.Proof.Rc2.X86.saveCode_ok s₀ .eax VG.Proof.TripleDes.X86.savedReg 4 (by decide)
    (by rw [ptr₀]; omega) hw₀)
  intro s₁ h₁
  refine WP.of_runBlock ⟨s₁.setReg .ebp (s₁.gpr .eax), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, rr, readSrc, Option.map_some], ?_⟩
  have ptr₁ : s₁.gpr .eax = VG.Proof.TripleDes.X86.scratchArg s slot := by rw [h₁.1]; exact ptr₀
  refine ⟨ptr₁, h₁.2.1, h₁.2.2.1, ?_, ?_, ?_⟩
  · intro r ha hb
    rw [gpr_setReg_of_ne _ _ hb, h₁.1, gpr_setReg_of_ne _ _ ha]
  · intro i hi
    rw [gpr_setReg_self, mem_setReg, ptr₁, h₁.2.2.2, ptr₀]
    rw [VG.Proof.Rc2.X86.saveMem_read _ _ _ 4 (by decide) i hi]
    have hr : VG.Proof.TripleDes.X86.savedReg i ≠ .eax := by
      have h : ∀ i < 4, VG.Proof.TripleDes.X86.savedReg i ≠ .eax := by decide
      exact h i hi
    exact gpr_setReg_of_ne _ _ hr
  · rw [mem_setReg, h₁.2.2.2, ptr₀]
    exact VG.Proof.Rc2.X86.saveMem_frame _ _ _ 4 (by decide)

structure RestorePost (original origin current : State) : Prop where
  saved : ∀ r ∈ savedRegs, current.gpr r = original.gpr r
  mem : current.mem = origin.mem
  rd : current.rd = origin.rd
  wr : current.wr = origin.wr
  sp : current.gpr .esp = origin.gpr .esp
  ptr : current.gpr .eax = origin.gpr .ebp

theorem blockRestore_ok (original s : State) (hsaved : VG.Proof.TripleDes.X86.Saved original s)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr)
      (addr32 (s.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block VG.Impl.TripleDes.X86.blockRestore) s (VG.Proof.TripleDes.X86.RestorePost original s) := by
  have code : VG.Impl.TripleDes.X86.blockRestore = ([rr .eax .ebp] : List Instr) ++
      VG.Proof.Rc2.X86.restoreCode .eax VG.Proof.TripleDes.X86.savedReg (List.range 4) := by
    unfold VG.Impl.TripleDes.X86.blockRestore
    congr 1
  rw [code, WP.block_append_iff]
  let s₀ := s.setReg .eax (s.gpr .ebp)
  refine WP.of_runBlock ⟨s₀, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, rr, readSrc, Option.map_some]
    rfl, ?_⟩
  have hptr : s₀.gpr .eax = s.gpr .ebp := gpr_setReg_self _ _ _
  have hregs : (List.range 4).map VG.Proof.TripleDes.X86.savedReg = savedRegs := by decide
  have separate : ∀ i ∈ List.range 4, VG.Proof.TripleDes.X86.savedReg i ≠ .eax := by decide
  have h := VG.Proof.Rc2.X86.restoreCode_ok s₀ .eax VG.Proof.TripleDes.X86.savedReg (List.range 4)
    original.gpr (by rw [hptr]; omega)
    (fun i hi => by have := List.mem_range.mp hi; omega) separate
    (fun i hi => by rw [hptr]; exact hread i (List.mem_range.mp hi))
    (fun i hi => by rw [hptr]; exact hsaved i (List.mem_range.mp hi))
  rw [hregs] at h
  apply WP.mono h
  intro s₁ h₁
  exact ⟨h₁.1, h₁.2.mem, h₁.2.rd, h₁.2.wr,
    (h₁.2.reg .esp (by decide)).trans (gpr_setReg_of_ne s _ (by decide)),
    (h₁.2.reg .eax (by decide)).trans hptr⟩

theorem savedSlot_work_disjoint (s : State) (i : Nat) (hi : i < 4) :
    (⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.workRegion s) :=
  Offset.disjoint _ (by omega) (by omega) (by decide)

theorem Saved.congr {original s t : State} (hs : VG.Proof.TripleDes.X86.Saved original s)
    (hbase : t.gpr .ebp = s.gpr .ebp) (hf : VG.Frame [VG.Proof.TripleDes.X86.workRegion s] s.mem t.mem) :
    VG.Proof.TripleDes.X86.Saved original t := by
  intro i hi
  rw [hbase]
  have hm := hf.readW (a := addr32 (s.gpr .ebp) + BitVec.ofNat 64 (4 * i)) (w := 32)
    (r := ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 (4 * i), 4⟩)
    (Region.contains_self _ _) (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq
      exact VG.Proof.TripleDes.X86.savedSlot_work_disjoint s i hi) (by decide)
  exact hm.trans (hs i hi)

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Head`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.Rc2.X86 (addr32)

def prepared (s : State) : State := s.setReg .ebp (VG.Proof.TripleDes.X86.scratchArg s 3)
def saveRegion (s : State) : Region := ⟨addr32 (VG.Proof.TripleDes.X86.scratchArg s 3), 16⟩

structure HeadPre (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) : Prop where
  ready : VG.Proof.TripleDes.X86.Ready keys base (VG.Proof.TripleDes.X86.prepared s)
  scratchFit : (VG.Proof.TripleDes.X86.scratchArg s 3).toNat + 512 ≤ 2 ^ 32
  dataFit : (VG.Proof.TripleDes.X86.dataArg s).toNat + 8 ≤ 2 ^ 32
  saveWrite : ∀ i < 4, InRegions s.wr (addr32 (VG.Proof.TripleDes.X86.scratchArg s 3) + BitVec.ofNat 64 (4 * i)) 4
  argRead : ∀ i ∈ [1, 2, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4
  argSeparate : ∀ i ∈ [1, 2, 3], (⟨wordAddr (s.gpr .esp) i, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.saveRegion s)
  dataRead : ∀ i < 2, InRegions (s.rd ++ s.wr) (wordAddr (VG.Proof.TripleDes.X86.dataArg s) i) 4
  dataSeparate : (⟨addr32 (VG.Proof.TripleDes.X86.dataArg s), 8⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.saveRegion s)
  keySeparate : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    (⟨wordAddr (VG.Proof.TripleDes.X86.keyAddr (VG.Proof.TripleDes.X86.componentBase base c) d j) t, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.saveRegion s)

structure HeadPost (keys : Nat → DesSchedule) (base : BitVec 32) (original s : State) : Prop where
  word : VG.Proof.TripleDes.X86.WordState (Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt original.mem (addr32 (VG.Proof.TripleDes.X86.dataArg original))))) s
  ready : VG.Proof.TripleDes.X86.Ready keys base s
  saved : VG.Proof.TripleDes.X86.Saved original s
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  bp : s.gpr .ebp = VG.Proof.TripleDes.X86.scratchArg original 3
  sp : s.gpr .esp = original.gpr .esp
  data : VG.Proof.TripleDes.X86.dataArg s = VG.Proof.TripleDes.X86.dataArg original
  frame : VG.Frame [VG.Proof.TripleDes.X86.saveRegion original] original.mem s.mem

theorem blockHead_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State)
    (hp : VG.Proof.TripleDes.X86.HeadPre keys base s) : WP isa (.block (blockSave ++ blockLoad)) s (VG.Proof.TripleDes.X86.HeadPost keys base s) := by
  rw [WP.block_append_iff, blockSave]
  apply WP.mono (VG.Proof.TripleDes.X86.saveWithArg_ok s 3 (hp.argRead 3 (by decide)) hp.scratchFit hp.saveWrite)
  intro s₁ h₁
  have sp₁ : s₁.gpr .esp = s.gpr .esp := h₁.reg .esp (by decide) (by decide)
  have frame₁ : VG.Frame [VG.Proof.TripleDes.X86.saveRegion s] s.mem s₁.mem := h₁.frame
  have bp₁ : s₁.gpr .ebp = (VG.Proof.TripleDes.X86.prepared s).gpr .ebp := h₁.bp
  have sp₁' : s₁.gpr .esp = (VG.Proof.TripleDes.X86.prepared s).gpr .esp := by
    rw [VG.Proof.TripleDes.X86.prepared, gpr_setReg_of_ne _ _ (by decide)]; exact sp₁
  have ready₁ : VG.Proof.TripleDes.X86.Ready keys base s₁ := hp.ready.congrFrame bp₁ sp₁' h₁.rd h₁.wr
    [VG.Proof.TripleDes.X86.saveRegion s] frame₁
    (by intro q hq; obtain rfl := List.mem_singleton.mp hq
        rw [VG.Proof.TripleDes.X86.prepared, gpr_setReg_of_ne _ _ (by decide)]
        exact hp.argSeparate 1 (by decide))
    (by intro c hc d j hj i hi q hq; obtain rfl := List.mem_singleton.mp hq
        exact hp.keySeparate c hc d j hj i hi)
  have data₁ : VG.Proof.TripleDes.X86.dataArg s₁ = VG.Proof.TripleDes.X86.dataArg s := by
    unfold VG.Proof.TripleDes.X86.dataArg
    rw [sp₁]
    exact frame₁.readW (r := ⟨wordAddr (s.gpr .esp) 2, 4⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.argSeparate 2 (by decide)) (by decide)
  have args₁ : InRegions (s₁.rd ++ s₁.wr) (wordAddr (s₁.gpr .esp) 2) 4 := by
    rw [sp₁, h₁.rd, h₁.wr]; exact hp.argRead 2 (by decide)
  have reads₁ : ∀ i < 2, InRegions (s₁.rd ++ s₁.wr) (wordAddr (VG.Proof.TripleDes.X86.dataArg s₁) i) 4 := by
    rw [h₁.rd, h₁.wr, data₁]; exact hp.dataRead
  have input₁ : Spec.TripleDes.blockAt s₁.mem (addr32 (VG.Proof.TripleDes.X86.dataArg s₁)) =
      Spec.TripleDes.blockAt s.mem (addr32 (VG.Proof.TripleDes.X86.dataArg s)) := by
    rw [data₁]
    exact VG.Proof.TripleDes.blockAt_eq_of_frame _ frame₁
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.dataSeparate)
  apply WP.mono (VG.Proof.TripleDes.X86.blockLoad_ok s₁ (by rw [data₁]; exact hp.dataFit) args₁ reads₁)
  intro s₂ h₂
  have hf : VG.Frame [VG.Proof.TripleDes.X86.workRegion s₁] s₁.mem s₂.mem := by rw [h₂.mem]; exact Frame.refl _ _
  have input := congrArg (fun b => Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock b)) input₁
  refine ⟨⟨h₂.l.trans (congrArg (fun x : BitVec 64 => (x >>> 32).setWidth 32) input),
    h₂.r.trans (congrArg (fun x : BitVec 64 => x.setWidth 32) input)⟩,
    ready₁.congr h₂.bp h₂.sp h₂.rd h₂.wr hf, h₁.saved.congr h₂.bp hf,
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.bp.trans h₁.bp, h₂.sp.trans sp₁, ?_, ?_⟩
  · unfold VG.Proof.TripleDes.X86.dataArg
    rw [h₂.mem, h₂.sp]
    exact data₁
  · rw [h₂.mem]; exact frame₁

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.WordStore`. -/
section

namespace VG.Proof.TripleDes.X86
open VG

theorem getLsbD_read (m : Mem) : ∀ (n : Nat) (a : Addr) (i : Nat), i < 8 * n →
    (m.read a n).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8)
  | 0, _, _, h => absurd h (by omega)
  | n + 1, a, i, h => by
    simp only [Mem.read, BitVec.getLsbD_append]
    by_cases hi : i < 8
    · simp [hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · simp only [hi, ite_false]
      rw [VG.Proof.TripleDes.X86.getLsbD_read m n (a + 1) (i - 8) (by omega)]
      have e1 : (i - 8) / 8 = i / 8 - 1 := by omega
      have e2 : (i - 8) % 8 = i % 8 := by omega
      rw [e1, e2]
      congr 2
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
      omega

theorem readW_pair (m : Mem) (p : Addr) :
    m.readW (p + 4) 32 ++ m.readW p 32 = m.readW p 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append]
  by_cases hlo : i < 32
  · rw [ite_eq_left hlo]
    simp only [Mem.readW, BitVec.getLsbD_setWidth, hlo, hi, decide_true, Bool.true_and]
    rw [VG.Proof.TripleDes.X86.getLsbD_read m 4 p i (by omega), VG.Proof.TripleDes.X86.getLsbD_read m 8 p i (by omega)]
  · rw [ite_eq_right hlo]
    simp only [Mem.readW, BitVec.getLsbD_setWidth, hi,
      show i - 32 < 32 by omega, decide_true, Bool.true_and]
    rw [VG.Proof.TripleDes.X86.getLsbD_read m 4 (p + 4) (i - 32) (by omega), VG.Proof.TripleDes.X86.getLsbD_read m 8 p i (by omega)]
    have ha : 4 + (i - 32) / 8 = i / 8 := by omega
    have hb : (i - 32) % 8 = i % 8 := by omega
    rw [hb]
    exact congrArg (fun q => (m q).getLsbD (i % 8))
      ((VG.Offset.add_ofNat_add_ofNat p 4 ((i - 32) / 8)).trans
        (congrArg (fun j => p + BitVec.ofNat 64 j) ha))

theorem writeW_pair (m : Mem) (p : Addr) (lo hi : BitVec 32) :
    (m.writeW p lo).writeW (p + 4) hi = m.writeW p (hi ++ lo) := by
  funext a
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq]
  by_cases hhi : (a - (p + 4)).toNat < 4
  · have he : (a - p).toNat = (a - (p + 4)).toNat + 4 := by bv_omega
    have hb : (a - p).toNat < 8 := by omega
    rw [ite_eq_left hhi, ite_eq_left hb]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi'
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    simp (disch := omega) only [ite_eq_right, he]
    apply congrArg (fun b => decide (i < 8) && b)
    apply congrArg hi.getLsbD
    omega
  · rw [ite_eq_right hhi]
    by_cases hlo : (a - p).toNat < 4
    · have hb : (a - p).toNat < 8 := by omega
      rw [ite_eq_left hlo, ite_eq_left hb]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi'
      simp (disch := omega) only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
        ite_eq_left]
    · have hb : ¬ (a - p).toNat < 8 := by bv_omega
      rw [ite_eq_right hlo, ite_eq_right hb]

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.FinalPermutation`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)

theorem fp_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.fp 64 32 32 .eax .ebx .edi .esi .ecx) s = some s' ∧
      s'.gpr .eax = (Spec.TripleDes.permute Spec.TripleDes.fp
        (VG.Proof.TripleDes.X86.packedInput 64 32 (s.gpr .edi) (s.gpr .esi))).setWidth 32 ∧
      s'.gpr .ebx = ((Spec.TripleDes.permute Spec.TripleDes.fp
        (VG.Proof.TripleDes.X86.packedInput 64 32 (s.gpr .edi) (s.gpr .esi))) >>> 32).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    VG.Proof.TripleDes.X86.fixedPermutation_ok Spec.TripleDes.fp (by decide) 32 32
      (by decide) (by decide) (by decide) (by decide) (by decide)
      .edi .esi .eax .ebx (instrs finalPermutation.lit) VG.Proof.TripleDes.X86.finalPermutation_check (by decide +kernel) s
  have hcode : permuteCode Spec.TripleDes.fp 64 32 32 .eax .ebx .edi .esi .ecx = instrs finalPermutation.lit :=
    congrArg instrs finalPermutation.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run,
    lo, hi, rd, wr, sp, mem, regs⟩

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.FinalSave`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86

def finalMem (s : State) : Mem :=
  (s.mem.writeW (wordAddr (s.gpr .ebp) 6) (s.gpr .eax)).writeW
    (wordAddr (s.gpr .ebp) 7) (s.gpr .ebx)

theorem finalStores_ok (s : State) (hok : Ok VG.Proof.TripleDes.X86.sboxCfg s) :
    ∃ s', runBlock isa [.store (memOp .ebp 24) .eax, .store (memOp .ebp 28) .ebx] s = some s' ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = VG.Proof.TripleDes.X86.finalMem s := by
  have h6 := hok.slotIn 6 (by decide)
  have h7 := hok.slotIn 7 (by decide)
  simp only [wordAddr, addr, VG.Proof.TripleDes.X86.sboxCfg] at h6 h7
  refine ⟨{s with mem := VG.Proof.TripleDes.X86.finalMem s}, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, State.ea,
      memOp, h6, h7, ite_true]
    rfl, rfl, rfl, rfl, rfl⟩

structure FinalSavePost (x : BitVec 64) (s s' : State) : Prop where
  lo : s'.mem.readW (wordAddr (s.gpr .ebp) 6) 32 = x.setWidth 32
  hi : s'.mem.readW (wordAddr (s.gpr .ebp) 7) 32 = (x >>> 32).setWidth 32
  bp : s'.gpr .ebp = s.gpr .ebp
  sp : s'.gpr .esp = s.gpr .esp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : VG.Frame [VG.Proof.TripleDes.X86.workRegion s] s.mem s'.mem

theorem finalSave_ok (s : State) (hok : Ok VG.Proof.TripleDes.X86.sboxCfg s) :
    WP isa (.block finalSave) s (VG.Proof.TripleDes.X86.FinalSavePost
      (Spec.TripleDes.permute Spec.TripleDes.fp (s.gpr .esi ++ s.gpr .edi)) s) := by
  rw [finalSave, WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, rd₁, wr₁, sp₁, mem₁, regs₁⟩ := VG.Proof.TripleDes.X86.fp_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have bp₁ := regs₁ .ebp (by decide +kernel)
  obtain ⟨s₂, run₂, gpr₂, rd₂, wr₂, mem₂⟩ := VG.Proof.TripleDes.X86.finalStores_ok s₁ (hok.congr bp₁ bp₁ rd₁ wr₁)
  have hsep : Mem.Sep (wordAddr (s.gpr .ebp) 6) 4 (wordAddr (s.gpr .ebp) 7) 4 := by
    rw [wordAddr, wordAddr, addr_eq (by have h := hok.fit; change (s.gpr .ebp).toNat + 512 ≤ 2^32 at h; omega),
      addr_eq (by have h := hok.fit; change (s.gpr .ebp).toNat + 512 ≤ 2^32 at h; omega)]
    exact Offset.sep _ (by decide) (by decide) (by decide)
  have hm : s₂.mem = (s.mem.writeW (wordAddr (s.gpr .ebp) 6) (s₁.gpr .eax)).writeW
      (wordAddr (s.gpr .ebp) 7) (s₁.gpr .ebx) := by rw [mem₂, VG.Proof.TripleDes.X86.finalMem, bp₁, mem₁]
  refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, ?_, by rw [gpr₂]; exact bp₁,
    by rw [gpr₂]; exact sp₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩⟩
  · rw [hm, Mem.readW_writeW_sep hsep (by decide), Mem.readW_writeW_self32, lo₁]
    rfl
  · rw [hm, Mem.readW_writeW_self32, hi₁]
    rfl
  · have h6 : (VG.Proof.TripleDes.X86.workRegion s).Contains (wordAddr (s.gpr .ebp) 6) 4 := by
      rw [wordAddr, addr_eq (by have h := hok.fit; change (s.gpr .ebp).toNat + 512 ≤ 2^32 at h; omega)]
      exact Offset.contains _ (by decide) (by decide) (by decide)
    have h7 : (VG.Proof.TripleDes.X86.workRegion s).Contains (wordAddr (s.gpr .ebp) 7) 4 := by
      rw [wordAddr, addr_eq (by have h := hok.fit; change (s.gpr .ebp).toNat + 512 ≤ 2^32 at h; omega)]
      exact Offset.contains _ (by decide) (by decide) (by decide)
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ h6).writeW
      (List.mem_singleton_self _) _ h7

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.RestoredOutput`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)

def finalWord (s : State) : BitVec 64 :=
  s.mem.readW (addr (s.gpr .eax) 28) 32 ++ s.mem.readW (addr (s.gpr .eax) 24) 32

theorem restoredOutput_ok (s : State) (fit : (VG.Proof.TripleDes.X86.dataArg s).toNat + 8 ≤ 2 ^ 32)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4)
    (hr : ∀ k ∈ [24, 28], InRegions (s.rd ++ s.wr) (addr (s.gpr .eax) k) 4)
    (hw : ∀ i < 2, InRegions s.wr (wordAddr (VG.Proof.TripleDes.X86.dataArg s) i) 4) :
    ∃ s', runBlock isa restoredOutput s = some s' ∧
      s'.mem = s.mem.writeW (addr32 (VG.Proof.TripleDes.X86.dataArg s)) (byteRev64 (VG.Proof.TripleDes.X86.finalWord s)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) := by
  have hw0 := hw 0 (by decide)
  have hw1 := hw 1 (by decide)
  have h24 := hr 24 (by decide)
  have h28 := hr 28 (by decide)
  simp only [wordAddr, addr, VG.Proof.TripleDes.X86.dataArg] at harg hw0 hw1
  simp only [addr] at h24 h28
  refine ⟨_, by
    simp only [restoredOutput, rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.store32, State.ea, memOp, harg, hw0, hw1, h24, h28, ite_true,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_⟩
  · dsimp only [mem_setReg, gpr_setReg, reduceCtorEq, ite_true, ite_false]
    have ha0 : (VG.Proof.TripleDes.X86.dataArg s + BitVec.ofNat 32 0).setWidth 64 = addr32 (VG.Proof.TripleDes.X86.dataArg s) := by simp [addr32]
    have ha1 : (VG.Proof.TripleDes.X86.dataArg s + BitVec.ofNat 32 4).setWidth 64 = addr32 (VG.Proof.TripleDes.X86.dataArg s) + 4 := addr_eq (by omega)
    change (s.mem.writeW ((VG.Proof.TripleDes.X86.dataArg s + BitVec.ofNat 32 0).setWidth 64)
      (bswap (s.mem.readW (addr (s.gpr .eax) 28) 32))).writeW
      ((VG.Proof.TripleDes.X86.dataArg s + BitVec.ofNat 32 4).setWidth 64)
      (bswap (s.mem.readW (addr (s.gpr .eax) 24) 32)) = _
    rw [ha0, ha1, VG.Proof.TripleDes.X86.writeW_pair, VG.Proof.TripleDes.X86.bswapPair]
    rfl
  · rfl
  · rfl
  · intro r ha hc hd
    simp only [gpr_setReg, ha, hc, hd, ite_false]

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.RestoredTail`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)

structure RestoredTailPost (original origin : State) (x : BitVec 64) (s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (addr32 (VG.Proof.TripleDes.X86.dataArg origin)) =
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp x)
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.gpr .esp = origin.gpr .esp
  frame : VG.Frame [⟨addr32 (VG.Proof.TripleDes.X86.dataArg origin), 8⟩, VG.Proof.TripleDes.X86.workRegion origin] origin.mem s.mem

theorem blockTailRestored_ok (original s : State) (x : BitVec 64) (hword : VG.Proof.TripleDes.X86.WordState x s)
    (hsaved : VG.Proof.TripleDes.X86.Saved original s) (hok : Ok VG.Proof.TripleDes.X86.sboxCfg s)
    (dataFit : (VG.Proof.TripleDes.X86.dataArg s).toNat + 8 ≤ 2 ^ 32)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4)
    (hargSep : (⟨wordAddr (s.gpr .esp) 2, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.workRegion s))
    (hw : ∀ i < 2, InRegions s.wr (wordAddr (VG.Proof.TripleDes.X86.dataArg s) i) 4)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (finalSave ++ blockRestore ++ restoredOutput)) s (VG.Proof.TripleDes.X86.RestoredTailPost original s x) := by
  rw [WP.block_append_iff, WP.block_append_iff]
  apply WP.mono (VG.Proof.TripleDes.X86.finalSave_ok s hok)
  intro s₁ h₁
  have saved₁ := hsaved.congr h₁.bp h₁.frame
  have reads₁ : ∀ i < 4, InRegions (s₁.rd ++ s₁.wr) (addr32 (s₁.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [h₁.rd, h₁.wr, h₁.bp]; exact hread
  apply WP.mono (VG.Proof.TripleDes.X86.blockRestore_ok original s₁ saved₁ (by rw [h₁.bp]; exact hok.fit) reads₁)
  intro s₂ h₂
  have sp₂ : s₂.gpr .esp = s.gpr .esp := h₂.sp.trans h₁.sp
  have ptr₂ : s₂.gpr .eax = s.gpr .ebp := h₂.ptr.trans h₁.bp
  have rd₂ : s₂.rd = s.rd := h₂.rd.trans h₁.rd
  have wr₂ : s₂.wr = s.wr := h₂.wr.trans h₁.wr
  have data₂ : VG.Proof.TripleDes.X86.dataArg s₂ = VG.Proof.TripleDes.X86.dataArg s := by
    unfold VG.Proof.TripleDes.X86.dataArg
    rw [sp₂, h₂.mem]
    exact h₁.frame.readW (r := ⟨wordAddr (s.gpr .esp) 2, 4⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hargSep) (by decide)
  have input₂ : VG.Proof.TripleDes.X86.finalWord s₂ = Spec.TripleDes.permute Spec.TripleDes.fp x := by
    unfold VG.Proof.TripleDes.X86.finalWord
    rw [ptr₂, h₂.mem]
    change (s₁.mem.readW (wordAddr (s.gpr .ebp) 7) 32 ++
      s₁.mem.readW (wordAddr (s.gpr .ebp) 6) 32 : BitVec 64) =
        Spec.TripleDes.permute Spec.TripleDes.fp x
    rw [h₁.hi, h₁.lo, VG.Proof.TripleDes.halves_append, hword.left, hword.right,
      VG.Proof.TripleDes.halves_append]
  have reads₂ : ∀ k ∈ [24, 28], InRegions (s₂.rd ++ s₂.wr) (addr (s₂.gpr .eax) k) 4 := by
    intro k hk
    rw [rd₂, wr₂, ptr₂]
    have hwk : InRegions s.wr (addr (s.gpr .ebp) k) 4 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact hok.slotIn 6 (by decide)
      · exact hok.slotIn 7 (by decide)
    obtain ⟨r, hr, hc⟩ := hwk
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have arg₂ : InRegions (s₂.rd ++ s₂.wr) (wordAddr (s₂.gpr .esp) 2) 4 := by
    rw [rd₂, wr₂, sp₂]; exact harg
  have writes₂ : ∀ i < 2, InRegions s₂.wr (wordAddr (VG.Proof.TripleDes.X86.dataArg s₂) i) 4 := by
    rw [wr₂, data₂]; exact hw
  obtain ⟨s₃, run₃, mem₃, rd₃, wr₃, regs₃⟩ := VG.Proof.TripleDes.X86.restoredOutput_ok s₂
    (by rw [data₂]; exact dataFit) arg₂ reads₂ writes₂
  have hm : s₃.mem = s₁.mem.writeW (addr32 (VG.Proof.TripleDes.X86.dataArg s))
      (byteRev64 (Spec.TripleDes.permute Spec.TripleDes.fp x)) := by
    rw [mem₃, data₂, input₂, h₂.mem]
  refine WP.of_runBlock ⟨s₃, run₃, ⟨?_, ?_, rd₃.trans rd₂, wr₃.trans wr₂,
    (regs₃ .esp (by decide) (by decide) (by decide)).trans sp₂, ?_⟩⟩
  · rw [hm]
    exact VG.Proof.TripleDes.X86.blockAt_writeW _ _ _
  · intro r hr
    have neq : ∀ r ∈ savedRegs, r ≠ .eax ∧ r ≠ .ecx ∧ r ≠ .edx := by decide
    exact (regs₃ r (neq r hr).1 (neq r hr).2.1 (neq r hr).2.2).trans (h₂.saved r hr)
  · rw [hm]
    exact (h₁.frame.mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp)).writeW
      (List.mem_cons_self) _ (Region.contains_self _ _)

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Block`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction Schedule)
open VG.Proof.Rc2.X86 (addr32)

def blockResult (keys : Schedule) (d : Direction) (b : Spec.TripleDes.Block) : Spec.TripleDes.Block :=
  match d with
  | .encrypt => Spec.TripleDes.encryptBlock keys b
  | .decrypt => Spec.TripleDes.decryptBlock keys b

theorem blockResult_core (keys : Schedule) (d : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp
      (VG.Proof.TripleDes.X86.blockCore (Spec.TripleDes.componentSchedule keys) d
        (Spec.TripleDes.permute Spec.TripleDes.ip (Spec.TripleDes.decodeBlock b)))) = VG.Proof.TripleDes.X86.blockResult keys d b := by
  cases d
  · exact (VG.Proof.TripleDes.encryptBlock_eq_cores keys b).symm
  · exact (VG.Proof.TripleDes.decryptBlock_eq_cores keys b).symm

def blockRegions (s : State) : List Region :=
  [⟨addr32 (VG.Proof.TripleDes.X86.dataArg s), 8⟩, ⟨addr32 (VG.Proof.TripleDes.X86.scratchArg s 3), 512⟩]

structure BlockPost (keys : Schedule) (d : Direction) (original s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (addr32 (VG.Proof.TripleDes.X86.dataArg original)) =
    VG.Proof.TripleDes.X86.blockResult keys d (Spec.TripleDes.blockAt original.mem (addr32 (VG.Proof.TripleDes.X86.dataArg original)))
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.gpr .esp = original.gpr .esp
  frame : VG.Frame (VG.Proof.TripleDes.X86.blockRegions original) original.mem s.mem

theorem block_ok (keys : Schedule) (base : BitVec 32) (d : Direction) (s : State)
    (hp : VG.Proof.TripleDes.X86.HeadPre (Spec.TripleDes.componentSchedule keys) base s)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (addr32 (VG.Proof.TripleDes.X86.scratchArg s 3) + BitVec.ofNat 64 (4 * i)) 4)
    (hwrite : ∀ i < 2, InRegions s.wr (wordAddr (VG.Proof.TripleDes.X86.dataArg s) i) 4)
    (hargSep : (⟨wordAddr (s.gpr .esp) 2, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.workRegion (VG.Proof.TripleDes.X86.prepared s))) :
    WP isa (block d) s (VG.Proof.TripleDes.X86.BlockPost keys d s) := by
  rw [block]
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86.blockHead_ok (Spec.TripleDes.componentSchedule keys) base s hp)
  intro s₁ h₁
  apply WP.seq
  apply WP.mono (VG.Proof.TripleDes.X86.blockBody_ok (Spec.TripleDes.componentSchedule keys) base s₁ _ d h₁.ready h₁.word)
  intro s₂ h₂
  have stable := h₂.2.2
  have bp₂ : s₂.gpr .ebp = VG.Proof.TripleDes.X86.scratchArg s 3 := stable.bp.trans h₁.bp
  have sp₂ : s₂.gpr .esp = s.gpr .esp := stable.sp.trans h₁.sp
  have work₁ : VG.Proof.TripleDes.X86.workRegion s₁ = VG.Proof.TripleDes.X86.workRegion (VG.Proof.TripleDes.X86.prepared s) := by
    unfold VG.Proof.TripleDes.X86.workRegion VG.Proof.TripleDes.X86.prepared
    rw [h₁.bp, VG.X86.RegUpd.gpr_setReg_self]
  have data₂ : VG.Proof.TripleDes.X86.dataArg s₂ = VG.Proof.TripleDes.X86.dataArg s := by
    unfold VG.Proof.TripleDes.X86.dataArg
    rw [stable.sp]
    have sep : (⟨wordAddr (s₁.gpr .esp) 2, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.workRegion s₁) := by
      rw [h₁.sp, work₁]
      exact hargSep
    have hm := stable.frame.readW (a := wordAddr (s₁.gpr .esp) 2) (w := 32)
      (r := ⟨wordAddr (s₁.gpr .esp) 2, 4⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact sep) (by decide)
    exact hm.trans h₁.data
  have saved₂ := h₁.saved.congr stable.bp stable.frame
  have reads₂ : ∀ i < 4, InRegions (s₂.rd ++ s₂.wr) (addr32 (s₂.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [stable.rd, stable.wr, h₁.rd, h₁.wr, bp₂]; exact hread
  have writes₂ : ∀ i < 2, InRegions s₂.wr (wordAddr (VG.Proof.TripleDes.X86.dataArg s₂) i) 4 := by
    rw [stable.wr, h₁.wr, data₂]; exact hwrite
  have arg₂ : InRegions (s₂.rd ++ s₂.wr) (wordAddr (s₂.gpr .esp) 2) 4 := by
    rw [stable.rd, stable.wr, h₁.rd, h₁.wr, sp₂]; exact hp.argRead 2 (by decide)
  have work₂ : VG.Proof.TripleDes.X86.workRegion s₂ = VG.Proof.TripleDes.X86.workRegion (VG.Proof.TripleDes.X86.prepared s) := by
    unfold VG.Proof.TripleDes.X86.workRegion VG.Proof.TripleDes.X86.prepared
    rw [bp₂, VG.X86.RegUpd.gpr_setReg_self]
  apply WP.mono (VG.Proof.TripleDes.X86.blockTailRestored_ok s s₂ _ h₂.1 saved₂ h₂.2.1.spills
    (by rw [data₂]; exact hp.dataFit) arg₂
    (by rw [sp₂, work₂]; exact hargSep) writes₂ reads₂)
  intro s₃ h₃
  refine ⟨?_, h₃.saved, h₃.rd.trans (stable.rd.trans h₁.rd), h₃.wr.trans (stable.wr.trans h₁.wr),
    h₃.sp.trans sp₂, ?_⟩
  · have hr := h₃.result
    rw [data₂] at hr
    exact hr.trans (VG.Proof.TripleDes.X86.blockResult_core keys d _)
  · have hf₁ : VG.Frame (VG.Proof.TripleDes.X86.blockRegions s) s.mem s₁.mem := h₁.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨addr32 (VG.Proof.TripleDes.X86.scratchArg s 3), 512⟩, by simp [VG.Proof.TripleDes.X86.blockRegions], Region.sub_prefix (by decide)⟩)
    have hf₂ : VG.Frame (VG.Proof.TripleDes.X86.blockRegions s) s₁.mem s₂.mem := stable.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨⟨addr32 (VG.Proof.TripleDes.X86.scratchArg s 3), 512⟩, by simp [VG.Proof.TripleDes.X86.blockRegions], ?_⟩
      unfold VG.Proof.TripleDes.X86.workRegion
      rw [h₁.bp]
      exact Offset.sub_base _ (by decide))
    have hf₃ : VG.Frame (VG.Proof.TripleDes.X86.blockRegions s) s₂.mem s₃.mem := h₃.frame.sub (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [data₂]
        exact ⟨⟨addr32 (VG.Proof.TripleDes.X86.dataArg s), 8⟩, by simp [VG.Proof.TripleDes.X86.blockRegions], fun _ h => h⟩
      · refine ⟨⟨addr32 (VG.Proof.TripleDes.X86.scratchArg s 3), 512⟩, by simp [VG.Proof.TripleDes.X86.blockRegions], ?_⟩
        unfold VG.Proof.TripleDes.X86.workRegion
        rw [bp₂]
        exact Offset.sub_base _ (by decide))
    exact hf₁.trans (hf₂.trans hf₃)

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit`. -/
section

namespace VG

/-! The parts the block functions share, evaluated once: the round, and the
initial and final permutations. -/

materialize_value Impl.TripleDes.X86.roundBody
materialize_value Impl.TripleDes.X86.blockLoad
materialize_value Impl.TripleDes.X86.finalSave

/-! The functions. -/

materialize_code Impl.TripleDes.X86.encryptBlock
materialize_code Impl.TripleDes.X86.decryptBlock
materialize_code Impl.TripleDes.X86.Key.expandKey
materialize_code Impl.TripleDes.X86.Ecb.encrypt
materialize_code Impl.TripleDes.X86.Ecb.decrypt

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.ConstantTime`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.Impl.TripleDes.X86

def blockTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [8, 512],
    argLen := 16, argBases := [(8, 0), (12, 1)] }
def keyTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [384, 512],
    argLen := 20, argBases := [(12, 0), (16, 1)] }
def ecbTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 1024],
    argLen := 20, argBases := [(8, 0), (16, 1)], room := 16 }

/-! The body of the loop of rounds, which each block function runs three
times (two of them in each direction), and so each ECB function, through the
block function it calls, analysed once for each direction as summaries:
from what is public at the loop (the pointers and counters, two of them in
public slots of the scratch buffer), in the block functions and in the calls
from the ECB functions. -/

/-- What is public at the loop of rounds of a block function. -/
def roundTaint : VG.X86.Taint.T :=
  { regs := .ofList [.eax, .esp, .ebp], flags := false, lens := [8, 512], bases := [(.ebp, 1, 0)],
    slots := [(1, 20, 4), (1, 16, 4)], argLen := 16, argBases := [(8, 0), (12, 1)] }

/-- What is public at the loop of rounds of a block function called by an
ECB function. -/
def ecbRoundTaint : VG.X86.Taint.T :=
  { regs := .ofList [.eax, .esp, .ebp], flags := false, lens := [12, 0, 1024],
    bases := [(.esp, 0, 4), (.ebp, 2, 0)],
    slots := [(2, 20, 4), (2, 16, 4), (2, 12, 4), (2, 8, 4), (2, 4, 4), (2, 0, 4), (0, 8, 4), (0, 4, 4),
      (0, 0, 4)],
    wbases := [(0, 8, 2), (2, 0, 2)], argLen := 20, argBases := [(8, 1), (16, 2)], stk := [none, some 12],
    room := 16 }

taint_summary roundEnc : taint VG.Proof.TripleDes.X86.roundTaint (.block (roundBody ++ roundAdvance .encrypt))
taint_summary roundDec : taint VG.Proof.TripleDes.X86.roundTaint (.block (roundBody ++ roundAdvance .decrypt))
taint_summary ecbRoundEnc : taint VG.Proof.TripleDes.X86.ecbRoundTaint (.block (roundBody ++ roundAdvance .encrypt))
taint_summary ecbRoundDec : taint VG.Proof.TripleDes.X86.ecbRoundTaint (.block (roundBody ++ roundAdvance .decrypt))

theorem encryptBlock_constantTime (pre : VG.X86.State → Prop) (pub : VG.X86.State → VG.X86.State → Prop)
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree VG.Proof.TripleDes.X86.blockTaint s₁ s₂) :
    ConstantTime isa pre pub VG.Impl.TripleDes.X86.encryptBlock :=
  let ⟨_, hc⟩ := (by taint_decide_sum [roundEnc, roundDec] : ∃ h, (taint.check blockTaint encryptBlock h).isSome = true)
  VG.Taint.constantTime (A := taint) VG.Proof.TripleDes.X86.blockTaint h hc

theorem decryptBlock_constantTime (pre : VG.X86.State → Prop) (pub : VG.X86.State → VG.X86.State → Prop)
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree VG.Proof.TripleDes.X86.blockTaint s₁ s₂) :
    ConstantTime isa pre pub VG.Impl.TripleDes.X86.decryptBlock :=
  let ⟨_, hc⟩ := (by taint_decide_sum [roundEnc, roundDec] : ∃ h, (taint.check blockTaint decryptBlock h).isSome = true)
  VG.Taint.constantTime (A := taint) VG.Proof.TripleDes.X86.blockTaint h hc

theorem expandKey_constantTime (pre : VG.X86.State → Prop) (pub : VG.X86.State → VG.X86.State → Prop)
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree VG.Proof.TripleDes.X86.keyTaint s₁ s₂) :
    ConstantTime isa pre pub Key.expandKey :=
  VG.Taint.constantTime (A := taint) VG.Proof.TripleDes.X86.keyTaint h (by taint_decide)

theorem ecbEncrypt_constantTime (pre : VG.X86.State → Prop) (pub : VG.X86.State → VG.X86.State → Prop)
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree VG.Proof.TripleDes.X86.ecbTaint s₁ s₂) :
    ConstantTime isa pre pub Ecb.encrypt :=
  let ⟨_, hc⟩ := (by taint_decide_sum [ecbRoundEnc, ecbRoundDec] : ∃ h, (taint.check ecbTaint Ecb.encrypt h).isSome = true)
  VG.Taint.constantTime (A := taint) VG.Proof.TripleDes.X86.ecbTaint h hc

theorem ecbDecrypt_constantTime (pre : VG.X86.State → Prop) (pub : VG.X86.State → VG.X86.State → Prop)
    (h : ∀ s₁ s₂, pre s₁ → pre s₂ → pub s₁ s₂ → VG.X86.Taint.Agree VG.Proof.TripleDes.X86.ecbTaint s₁ s₂) :
    ConstantTime isa pre pub Ecb.decrypt :=
  let ⟨_, hc⟩ := (by taint_decide_sum [ecbRoundEnc, ecbRoundDec] : ∃ h, (taint.check ecbTaint Ecb.decrypt h).isSome = true)
  VG.Taint.constantTime (A := taint) VG.Proof.TripleDes.X86.ecbTaint h hc

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Contract`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)
open VG.Spec.TripleDes (Direction)

/-- The IA-32 calling convention and memory layout used by the block proof. -/
def blockContract (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨addr32 (arg s 0), 384⟩
    let data : Region := ⟨addr32 (arg s 1), 8⟩
    let scratch : Region := ⟨addr32 (arg s 2), 512⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    s.rd = [key, args] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 384 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 512 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s s' := Spec.TripleDes.blockAt s'.mem (addr32 (arg s 1)) =
    VG.Proof.TripleDes.X86.blockResult (Spec.TripleDes.scheduleAt s.mem (addr32 (arg s 0))) d
      (Spec.TripleDes.blockAt s.mem (addr32 (arg s 1)))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 3, arg s₁ i = arg s₂ i

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.BlockCT`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)
open VG.Spec.TripleDes (Direction)

theorem blockTaint_wf {d : Direction} {s : State} (hs : (VG.Proof.TripleDes.X86.blockContract d).pre s) : VG.X86.Taint.Wf VG.Proof.TripleDes.X86.blockTaint s := by
  obtain ⟨_, hwr, _, dataSep, argsData, argsScratch, retData, retScratch, _, dataFit, scratchFit, spFit⟩ := hs
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨spFit, ?_⟩, ?_⟩
  · rw [hwr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨dataSep, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr32, BitVec.toNat_setWidth] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega) retData argsData
    · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega) retScratch argsScratch
  · intro p hp
    simp only [VG.Proof.TripleDes.X86.blockTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, addr32, arg, argAddr]

theorem blockTaint_agree {d : Direction} {s t : State} (hs : (VG.Proof.TripleDes.X86.blockContract d).pre s)
    (ht : (VG.Proof.TripleDes.X86.blockContract d).pre t) (hp : (VG.Proof.TripleDes.X86.blockContract d).pub s t) :
    VG.X86.Taint.Agree VG.Proof.TripleDes.X86.blockTaint s t := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, (VG.Proof.TripleDes.X86.blockContract d).pre s → (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    intro s hs; exact hs.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.TripleDes.X86.blockTaint_wf hs,
    VG.Proof.TripleDes.X86.blockTaint_wf ht, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [VG.Proof.TripleDes.X86.blockTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [hs.2.1, ht.2.1, args 1 (by decide), args 2 (by decide)]
  · simp only [VG.Proof.TripleDes.X86.blockTaint] at hk
    rw [show VG.X86.Taint.depth blockTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (fit _ hs) h4 hk, VG.X86.Taint.argByte_eq (fit _ ht) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.ScheduleMemory`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight
open VG.Spec.TripleDes (Direction)
open VG.Proof.Rc2.X86 (addr32)
def selectedRound (d : Direction) (j : Nat) : Nat := if d = .encrypt then j else 15 - j

theorem selectedRound_bound (d : Direction) (j : Nat) (hj : j < 16) : VG.Proof.TripleDes.X86.selectedRound d j < 16 := by
  cases d <;> simp only [VG.Proof.TripleDes.X86.selectedRound, reduceCtorEq, ite_true, ite_false] <;> omega

theorem keyAddr_component (base : BitVec 32) (c : Nat) (d : Direction) (j : Nat) :
    VG.Proof.TripleDes.X86.keyAddr (VG.Proof.TripleDes.X86.componentBase base c) d j = base + BitVec.ofNat 32 (8 * (16 * c + VG.Proof.TripleDes.X86.selectedRound d j)) := by
  unfold VG.Proof.TripleDes.X86.keyAddr VG.Proof.TripleDes.X86.componentBase VG.Proof.TripleDes.X86.selectedRound
  rw [Offset.add_ofNat_add_ofNat]
  exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega)

theorem keyWordAddress (base : BitVec 32) (fit : base.toNat + 384 ≤ 2 ^ 32)
    (c j t : Nat) (hc : c < 3) (hj : j < 16) (ht : t < 2) (d : Direction) :
    wordAddr (VG.Proof.TripleDes.X86.keyAddr (VG.Proof.TripleDes.X86.componentBase base c) d j) t =
      addr32 base + BitVec.ofNat 64 (8 * (16 * c + VG.Proof.TripleDes.X86.selectedRound d j) + 4 * t) := by
  have bound := VG.Proof.TripleDes.X86.selectedRound_bound d j hj
  rw [wordAddr, VG.Proof.TripleDes.X86.keyAddr_component]
  unfold addr
  rw [Offset.add_ofNat_add_ofNat]
  exact VG.Proof.Rc2.X86.addr_add (by omega)

theorem readKey_component (m : Mem) (base : BitVec 32)
    (fit : base.toNat + 384 ≤ 2 ^ 32) (c j : Nat) (hc : c < 3) (hj : j < 16) (d : Direction) :
    VG.Proof.TripleDes.X86.readKey m (VG.Proof.TripleDes.X86.keyAddr (VG.Proof.TripleDes.X86.componentBase base c) d j) =
      m.readW (addr32 base + BitVec.ofNat 64 (8 * (16 * c + VG.Proof.TripleDes.X86.selectedRound d j))) 64 := by
  rw [VG.Proof.TripleDes.X86.readKey, VG.Proof.TripleDes.X86.keyWordAddress base fit c j 1 hc hj (by decide) d,
    VG.Proof.TripleDes.X86.keyWordAddress base fit c j 0 hc hj (by decide) d]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  rw [← Offset.add_ofNat_add_ofNat]
  exact VG.Proof.TripleDes.X86.readW_pair m _

theorem ready_of_regions (s : State) (base : BitVec 32) (hok : Ok VG.Proof.TripleDes.X86.sboxCfg s)
    (hb : VG.Proof.TripleDes.X86.scheduleArg s = base) (fit : base.toNat + 384 ≤ 2 ^ 32)
    (hread : ∀ p, (⟨addr32 base, 384⟩ : Region).Contains p 4 → InRegions (s.rd ++ s.wr) p 4)
    (hdis : (⟨addr32 base, 384⟩ : Region).Disjoint ⟨addr32 (s.gpr .ebp), 512⟩)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 1) 4)
    (hargSep : (⟨wordAddr (s.gpr .esp) 1, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.workRegion s)) :
    VG.Proof.TripleDes.X86.Ready (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (addr32 base))) base s := by
  have workSub : Region.Sub (VG.Proof.TripleDes.X86.workRegion s) ⟨addr32 (s.gpr .ebp), 512⟩ :=
    Offset.sub_base _ (by decide)
  have keySub : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
      Region.Sub ⟨wordAddr (VG.Proof.TripleDes.X86.keyAddr (VG.Proof.TripleDes.X86.componentBase base c) d j) t, 4⟩ ⟨addr32 base, 384⟩ := by
    intro c hc d j hj t ht
    rw [VG.Proof.TripleDes.X86.keyWordAddress base fit c j t hc hj ht d]
    have bound := VG.Proof.TripleDes.X86.selectedRound_bound d j hj
    exact Offset.sub_base _ (by omega)
  refine ⟨hok, hb, harg, hargSep, ?_, ?_, ?_, ?_⟩
  · intro c hc d j hj t ht
    apply hread
    rw [VG.Proof.TripleDes.X86.keyWordAddress base fit c j t hc hj ht d]
    have bound := VG.Proof.TripleDes.X86.selectedRound_bound d j hj
    exact Offset.contains_base _ (by omega) (by omega)
  · intro c hc d j hj t ht
    exact (hdis.sub_left (keySub c hc d j hj t ht)).sub_right workSub
  · intro c hc d j hj k hk t ht
    have scratchFit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32 := hok.fit
    apply hdis.symm.sep
    · rw [wordAddr, addr_eq (by omega)]
      exact Offset.contains_base _ (by omega) (by omega)
    · rw [VG.Proof.TripleDes.X86.keyWordAddress base fit c j t hc hj ht d]
      have bound := VG.Proof.TripleDes.X86.selectedRound_bound d j hj
      exact Offset.contains_base _ (by omega) (by omega)
  · intro c hc d j hj
    rw [VG.Proof.TripleDes.X86.readKey_component s.mem base fit c j hc hj d]
    exact (VG.Proof.TripleDes.componentSchedule_readW s.mem (addr32 base) c
      (VG.Proof.TripleDes.X86.selectedRound d j) hc (VG.Proof.TripleDes.X86.selectedRound_bound d j hj)).symm

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.Pre`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight
open VG.Proof.Rc2.X86 (addr32 argContainsCount)
open VG.Spec.TripleDes (Direction)

theorem argument_word (s : State) (i : Nat) : arg s i = s.mem.readW (wordAddr (s.gpr .esp) (i + 1)) 32 := by
  unfold arg argAddr
  apply congrArg (fun p => s.mem.readW p 32)
  change addr (s.gpr .esp) (4 + 4 * i) = addr (s.gpr .esp) (4 * (i + 1))
  exact congrArg (addr (s.gpr .esp)) (by omega)

theorem data_argument (s : State) : VG.Proof.TripleDes.X86.dataArg s = arg s 1 := (VG.Proof.TripleDes.X86.argument_word s 1).symm

theorem scratch_argument (s : State) : VG.Proof.TripleDes.X86.scratchArg s 3 = arg s 2 := (VG.Proof.TripleDes.X86.argument_word s 2).symm

theorem schedule_argument (s : State) : VG.Proof.TripleDes.X86.scheduleArg s = arg s 0 := (VG.Proof.TripleDes.X86.argument_word s 0).symm

theorem headPre_of_contract (d : Direction) (s : State) (hs : (VG.Proof.TripleDes.X86.blockContract d).pre s) :
    VG.Proof.TripleDes.X86.HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (addr32 (arg s 0))))
      (arg s 0) s := by
  obtain ⟨hrd, hwr, keySep, dataSep, argsData, argsScratch, _, _, keyFit, dataFit, scratchFit, spFit⟩ := hs
  have bp : (VG.Proof.TripleDes.X86.prepared s).gpr .ebp = arg s 2 := by rw [VG.Proof.TripleDes.X86.prepared, gpr_setReg_self, VG.Proof.TripleDes.X86.scratch_argument]
  have sp : (VG.Proof.TripleDes.X86.prepared s).gpr .esp = s.gpr .esp := gpr_setReg_of_ne s _ (by decide)
  have saveSub : Region.Sub (VG.Proof.TripleDes.X86.saveRegion s) ⟨addr32 (arg s 2), 512⟩ := by
    rw [VG.Proof.TripleDes.X86.saveRegion, VG.Proof.TripleDes.X86.scratch_argument]
    exact Region.sub_prefix (by decide)
  have workSub : Region.Sub (VG.Proof.TripleDes.X86.workRegion (VG.Proof.TripleDes.X86.prepared s)) ⟨addr32 (arg s 2), 512⟩ := by
    rw [VG.Proof.TripleDes.X86.workRegion, bp]
    exact Offset.sub_base _ (by decide)
  have argContains : ∀ i ∈ [1, 2, 3], (⟨argAddr s 0, 12⟩ : Region).Contains
      (wordAddr (s.gpr .esp) i) 4 := by
    intro i hi
    have hb : 1 ≤ i ∧ i ≤ 3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    rw [wordAddr, addr_eq (by omega)]
    have h := argContainsCount s 3 spFit (i - 1) (by omega)
    rw [show 4 + 4 * (i - 1) = 4 * i by omega] at h
    exact h
  have argSub : ∀ i ∈ [1, 2, 3], Region.Sub ⟨wordAddr (s.gpr .esp) i, 4⟩ ⟨argAddr s 0, 12⟩ := by
    intro i hi a ha
    exact (argContains i hi).byte (by change (a - wordAddr (s.gpr .esp) i).toNat + 1 ≤ 4 at ha; omega)
  have argRead : ∀ i ∈ [1, 2, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4 := by
    intro i hi
    rw [hrd, hwr]
    exact ⟨⟨argAddr s 0, 12⟩, by simp, argContains i hi⟩
  have slots : ∀ i < 128, InRegions (VG.Proof.TripleDes.X86.prepared s).wr (wordAddr ((VG.Proof.TripleDes.X86.prepared s).gpr .ebp) i) 4 := by
    intro i hi
    rw [bp, wordAddr, addr_eq (by omega)]
    change InRegions s.wr _ 4
    rw [hwr]
    exact ⟨⟨addr32 (arg s 2), 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hok : Ok VG.Proof.TripleDes.X86.sboxCfg (VG.Proof.TripleDes.X86.prepared s) := by
    refine ⟨slots, ?_, ?_, ?_⟩
    · intro k hk; change k < 0 at hk; omega
    · change ((VG.Proof.TripleDes.X86.prepared s).gpr .ebp).toNat + 512 ≤ 2 ^ 32
      rw [bp]; exact scratchFit
    · intro k hk j hj; change j < 0 at hj; omega
  have hb : VG.Proof.TripleDes.X86.scheduleArg (VG.Proof.TripleDes.X86.prepared s) = arg s 0 := by
    unfold VG.Proof.TripleDes.X86.scheduleArg
    rw [sp]
    exact (VG.Proof.TripleDes.X86.argument_word s 0).symm
  have ready := VG.Proof.TripleDes.X86.ready_of_regions (VG.Proof.TripleDes.X86.prepared s) (arg s 0) hok hb keyFit
    (by intro p hp
        change InRegions (s.rd ++ s.wr) p 4
        rw [hrd, hwr]
        exact ⟨⟨addr32 (arg s 0), 384⟩, by simp, hp⟩)
    (by rw [bp]; exact keySep)
    (by change InRegions (s.rd ++ s.wr) (wordAddr ((VG.Proof.TripleDes.X86.prepared s).gpr .esp) 1) 4
        rw [sp]; exact argRead 1 (by decide))
    (by rw [sp]; exact (argsScratch.sub_left (argSub 1 (by decide))).sub_right workSub)
  refine ⟨ready, ?_, ?_, ?_, argRead, ?_, ?_, dataSep.sub_right saveSub, ?_⟩
  · rw [VG.Proof.TripleDes.X86.scratch_argument]; exact scratchFit
  · rw [VG.Proof.TripleDes.X86.data_argument]; exact dataFit
  · intro i hi
    rw [VG.Proof.TripleDes.X86.scratch_argument, hwr]
    exact ⟨⟨addr32 (arg s 2), 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · intro i hi
    exact (argsScratch.sub_left (argSub i hi)).sub_right saveSub
  · intro i hi
    rw [VG.Proof.TripleDes.X86.data_argument, wordAddr, addr_eq (by omega), hrd, hwr]
    exact ⟨⟨addr32 (arg s 1), 8⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · intro c hc direction j hj t ht
    have keySub : Region.Sub ⟨wordAddr (VG.Proof.TripleDes.X86.keyAddr (VG.Proof.TripleDes.X86.componentBase (arg s 0) c) direction j) t, 4⟩
        ⟨addr32 (arg s 0), 384⟩ := by
      rw [VG.Proof.TripleDes.X86.keyWordAddress _ keyFit c j t hc hj ht direction]
      have bound := VG.Proof.TripleDes.X86.selectedRound_bound direction j hj
      exact Offset.sub_base _ (by omega)
    exact (keySep.sub_left keySub).sub_right saveSub

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.CorrectBlock`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32 argContainsCount)
open VG.Spec.TripleDes (Direction)

theorem block_correct (d : Direction) (s : State) (hs : (VG.Proof.TripleDes.X86.blockContract d).pre s) :
    WP isa (block d) s (fun s' => abiPreserved s s' ∧ (VG.Proof.TripleDes.X86.blockContract d).post s s') := by
  have hp := VG.Proof.TripleDes.X86.headPre_of_contract d s hs
  obtain ⟨_, hwr, _, _, _, argsScratch, retData, retScratch, _, dataFit, _, spFit⟩ := hs
  have hwrite : ∀ i < 2, InRegions s.wr (wordAddr (VG.Proof.TripleDes.X86.dataArg s) i) 4 := by
    intro i hi
    rw [VG.Proof.TripleDes.X86.data_argument, wordAddr, addr_eq (by omega), hwr]
    exact ⟨⟨addr32 (arg s 1), 8⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (addr32 (VG.Proof.TripleDes.X86.scratchArg s 3) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    obtain ⟨r, hr, hc⟩ := hp.saveWrite i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hargSep : (⟨wordAddr (s.gpr .esp) 2, 4⟩ : Region).Disjoint (VG.Proof.TripleDes.X86.workRegion (VG.Proof.TripleDes.X86.prepared s)) := by
    have sub : Region.Sub ⟨wordAddr (s.gpr .esp) 2, 4⟩ ⟨argAddr s 0, 12⟩ := by
      rw [wordAddr, addr_eq (by omega), VG.Proof.Rc2.X86.argAddr_eq s 0 (by omega)]
      exact Offset.sub _ (by decide) (by decide)
    have workSub : Region.Sub (VG.Proof.TripleDes.X86.workRegion (VG.Proof.TripleDes.X86.prepared s)) ⟨addr32 (arg s 2), 512⟩ := by
      unfold VG.Proof.TripleDes.X86.workRegion VG.Proof.TripleDes.X86.prepared
      rw [VG.X86.RegUpd.gpr_setReg_self, VG.Proof.TripleDes.X86.scratch_argument]
      exact Offset.sub_base _ (by decide)
    exact (argsScratch.sub_left sub).sub_right workSub
  apply WP.mono (VG.Proof.TripleDes.X86.block_ok (Spec.TripleDes.scheduleAt s.mem (addr32 (arg s 0)))
    (arg s 0) d s hp hread hwrite hargSep)
  intro s' hpost
  refine ⟨⟨?_, ?_⟩, hpost.result⟩
  · intro r hr
    have hregs : ∀ r ∈ calleeSaved, r ∈ savedRegs ∨ r = .esp := by decide
    rcases hregs r hr with h | rfl
    · exact hpost.saved r h
    · exact hpost.sp
  · apply hpost.frame.readW (r := ⟨addr32 (s.gpr .esp), 4⟩) (Region.contains_self _ _) _ (by decide)
    intro r hr
    simp only [VG.Proof.TripleDes.X86.blockRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact retData
    · exact retScratch

end VG.Proof.TripleDes.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.TripleDes.X86.VerifiedBlock`. -/
section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)

def blockSatState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x400d then 0x30 else 0
  rd := [⟨0x1000, 384⟩, ⟨0x4004, 12⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 512⟩]

theorem encrypt_verified : Verified target encryptBlock (Spec.TripleDes.encryptBlockContract abi) := by
  refine Verified.of_correct (VG.Proof.TripleDes.X86.block_correct .encrypt)
    (VG.Proof.TripleDes.X86.encryptBlock_constantTime _ _ (fun _ _ h₁ h₂ hp => VG.Proof.TripleDes.X86.blockTaint_agree h₁ h₂ hp)) ?_
  sig_implies [Spec.TripleDes.encryptBlockContract, Spec.TripleDes.blockSig, abi, argSlots, argVal,
    argBytes, addr32, VG.Proof.TripleDes.X86.blockContract, VG.Proof.TripleDes.X86.blockResult]
    [blockSatState, arg, argAddr, Mem.readW, Mem.read] using VG.Proof.TripleDes.X86.blockSatState

theorem decrypt_verified : Verified target decryptBlock (Spec.TripleDes.decryptBlockContract abi) := by
  refine Verified.of_correct (VG.Proof.TripleDes.X86.block_correct .decrypt)
    (VG.Proof.TripleDes.X86.decryptBlock_constantTime _ _ (fun _ _ h₁ h₂ hp => VG.Proof.TripleDes.X86.blockTaint_agree h₁ h₂ hp)) ?_
  sig_implies [Spec.TripleDes.decryptBlockContract, Spec.TripleDes.blockSig, abi, argSlots, argVal,
    argBytes, addr32, VG.Proof.TripleDes.X86.blockContract, VG.Proof.TripleDes.X86.blockResult]
    [blockSatState, arg, argAddr, Mem.readW, Mem.read] using VG.Proof.TripleDes.X86.blockSatState

end VG.Proof.TripleDes.X86

end
