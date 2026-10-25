module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.RoundLit
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Sbox
public import VerifiedGarbage.Proof.TripleDes.Pieces
public import VerifiedGarbage.Proof.Framework.RISCV64.Linear
import VerifiedGarbage.Proof.Framework.Mem

/-!
# The S-boxes' inputs and outputs in a round

`sboxInputs i` forms the six input bits of S-box `i` (E of R, XORed with the
round key) in the low bits of `q 0`–`q 5`; `sboxOutputs i` XORs its four
output bits into L at P's destinations. Both are linear: the evaluator checks
them (`Framework/RISCV64/Linear.lean`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.TripleDes.RISCV64
open VG.Proof.TripleDes (roundChunk roundChunk_bit boxSource boxPiece)

noncomputable def sboxInputsLiterals : Array (Prog isa) :=
  #[sboxInputs0.lit, sboxInputs1.lit, sboxInputs2.lit, sboxInputs3.lit, sboxInputs4.lit,
    sboxInputs5.lit, sboxInputs6.lit, sboxInputs7.lit]

noncomputable def sboxInputsLiteral (i : Nat) : Prog isa :=
  sboxInputsLiterals.getD i (.block [])

noncomputable def sboxOutputsLiterals : Array (Prog isa) :=
  #[sboxOutputs0.lit, sboxOutputs1.lit, sboxOutputs2.lit, sboxOutputs3.lit, sboxOutputs4.lit,
    sboxOutputs5.lit, sboxOutputs6.lit, sboxOutputs7.lit]

noncomputable def sboxOutputsLiteral (i : Nat) : Prog isa :=
  sboxOutputsLiterals.getD i (.block [])

/-- The round key, the one external word, at `kp`. -/
def roundInputCfg : Cfg := { base := kp, slots := 0, ext := kp, exts := 1 }
def roundInputRegs : List (Reg × Nat) := [(rReg, 0)]

def roundInputBits (i j p : Nat) : List Nat :=
  if p = 0 then
    let k := 6 * i + 5 - j
    [32 - Spec.TripleDes.expansion.getD k 1, 64 + (47 - k)]
  else []

def roundInputPost (i : Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 6).map fun j => (q j, roundInputBits i j)

theorem roundInput_check : ∀ i < 8,
    check (lanes 64 7) roundInputCfg (linExt 1) (instrs (sboxInputsLiteral i))
      (linEnv roundInputRegs) (linPost 7 (roundInputPost i)) = true := by
  decide +kernel

/-- No memory. -/
def roundOutputCfg : Cfg := { base := .ra, slots := 0, ext := .ra, exts := 0 }
def roundOutputRegs : List (Reg × Nat) :=
  [(lReg, 0)] ++ (List.range 4).map fun j => (q j, j + 1)

def roundOutputBits (i p : Nat) : List Nat :=
  [p] ++ ((List.range 4).filterMap fun j =>
    let position := 4 * i + 4 - j
    let dst := (Spec.TripleDes.p.toList.findIdx? (· == position)).getD 0
    if p = 31 - dst then some (64 * (j + 1)) else none)

theorem roundOutput_check : ∀ i < 8,
    check (lanes 64 9) roundOutputCfg (linExt 5) (instrs (sboxOutputsLiteral i))
      (linEnv roundOutputRegs) (linPost 9 [(lReg, roundOutputBits i)]) = true := by
  decide +kernel

theorem sboxInputsLiteral_eq : ∀ i < 8,
    sboxInputsLiteral i = .block (sboxInputs i)
  | 0, _ => sboxInputs0.lit_eq.symm
  | 1, _ => sboxInputs1.lit_eq.symm
  | 2, _ => sboxInputs2.lit_eq.symm
  | 3, _ => sboxInputs3.lit_eq.symm
  | 4, _ => sboxInputs4.lit_eq.symm
  | 5, _ => sboxInputs5.lit_eq.symm
  | 6, _ => sboxInputs6.lit_eq.symm
  | 7, _ => sboxInputs7.lit_eq.symm
  | n + 8, h => by omega

theorem roundInputCfg_ok (s : State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr kp) 8) (hal : (s.gpr kp).toNat % 8 = 0) :
    Ok roundInputCfg s where
  slotIn k hk := by simp [roundInputCfg] at hk
  extIn k hk := by
    have hk0 : k = 0 := by simp only [roundInputCfg] at hk; omega
    subst k
    simpa only [roundInputCfg, wordAddr, Nat.mul_zero, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero] using hread
  baseAl h := by simp [roundInputCfg] at h
  extAl _ := hal
  slots := by decide
  sep k hk := by simp [roundInputCfg] at hk

/-- The extraction block reads just one round key and forms six Boolean
input words. It does not change memory, access permissions or other registers. -/
theorem roundInput_ok (i : Nat) (hi : i < 8) (s : State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr kp) 8) (hal : (s.gpr kp).toNat % 8 = 0) :
    ∃ s', runBlock isa (sboxInputs i) s = some s' ∧
      (∀ j < 6, ∀ p < 64, (s'.gpr (q j)).getLsbD p =
        xorBits (fun k => if k = 0 then s.gpr rReg
          else s.mem.readW (s.gpr kp) 64) (roundInputBits i j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxInputs i).all fun op => dst op != some r) = true →
        s'.gpr r = s.gpr r) := by
  have hchk := roundInput_check i hi
  rw [sboxInputsLiteral_eq i hi] at hchk
  let W : Nat → BitVec 64 := fun k =>
    if k = 0 then s.gpr rReg else s.mem.readW (s.gpr kp) 64
  obtain ⟨s', hs', out, rd, wr, sp, keep, frame⟩ := linear_ok hchk
    (roundInputCfg_ok s hread hal) W (fun r k h => by
      simp only [roundInputRegs, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by decide, rfl⟩) (linExt_rel fun j hj => by
      have hj0 : j = 0 := by simp only [roundInputCfg] at hj; omega
      subst j
      exact ⟨by decide, by simp [W, wordAddr, roundInputCfg]⟩)
  refine ⟨s', hs', fun j hj p hp => ?_, rd, wr, sp, ?_, keep⟩
  · exact out (q j) (roundInputBits i j)
      (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) p hp
  · funext a
    apply frame a
    intro r hr hc
    simp only [slotRegion, roundInputCfg, List.mem_singleton] at hr
    subst r
    simp [Region.Contains] at hc

theorem roundInput_bounds : ∀ i < 8, ∀ j < 6,
    32 - Spec.TripleDes.expansion.getD (6 * i + 5 - j) 1 < 64 ∧
    47 - (6 * i + 5 - j) < 64 := by
  decide +kernel

theorem bitOf_low (W : Nat → BitVec 64) (a : Nat) (ha : a < 64) :
    bitOf W a = (W 0).getLsbD a := by
  simp only [bitOf, Nat.div_eq_of_lt ha, Nat.mod_eq_of_lt ha]

theorem bitOf_next (W : Nat → BitVec 64) (a : Nat) (ha : a < 64) :
    bitOf W (64 + a) = (W 1).getLsbD a := by
  have hd : (64 + a) / 64 = 1 := by omega
  simp only [bitOf, hd, Nat.add_mod_left, Nat.mod_eq_of_lt ha]

theorem roundInput_chunk (i : Nat) (hi : i < 8) (s : State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr kp) 8) (hal : (s.gpr kp).toNat % 8 = 0) :
    ∃ s', runBlock isa (sboxInputs i) s = some s' ∧
      inputAt s' 0 = roundChunk i ((s.gpr rReg).setWidth 32)
        ((s.mem.readW (s.gpr kp) 64).setWidth 48) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxInputs i).all fun op => dst op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, bits, rd, wr, sp, mem, keep⟩ := roundInput_ok i hi s hread hal
  refine ⟨s', run, ?_, rd, wr, sp, mem, keep⟩
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [inputAt, getLsbD_ofBits, hj, decide_true, Bool.true_and]
  rw [bits j hj 0 (by decide), roundChunk_bit i j hi hj]
  obtain ⟨hr, hk⟩ := roundInput_bounds i hi j hj
  simp only [roundInputBits, ite_true, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_low _ _ hr, bitOf_next _ _ hk, ite_true]
  rfl

theorem roundOutputBits_shape : ∀ i < 8, ∀ p < 64,
    roundOutputBits i p = [p] ++
      (if p < 32 ∧ boxSource p / 4 = i then
        [64 * (4 - boxSource p % 4)] else []) := by
  decide +kernel

theorem sboxOutputsLiteral_eq : ∀ i < 8,
    sboxOutputsLiteral i = .block (sboxOutputs i)
  | 0, _ => sboxOutputs0.lit_eq.symm
  | 1, _ => sboxOutputs1.lit_eq.symm
  | 2, _ => sboxOutputs2.lit_eq.symm
  | 3, _ => sboxOutputs3.lit_eq.symm
  | 4, _ => sboxOutputs4.lit_eq.symm
  | 5, _ => sboxOutputs5.lit_eq.symm
  | 6, _ => sboxOutputs6.lit_eq.symm
  | 7, _ => sboxOutputs7.lit_eq.symm
  | n + 8, h => by omega

theorem roundOutputCfg_ok (s : State) : Ok roundOutputCfg s where
  slotIn k hk := by simp [roundOutputCfg] at hk
  extIn k hk := by simp [roundOutputCfg] at hk
  baseAl h := by simp [roundOutputCfg] at h
  extAl h := by simp [roundOutputCfg] at h
  slots := by decide
  sep k hk := by simp [roundOutputCfg] at hk

/-- Deposit the four low S-box bits into L, at P's fixed destinations. -/
theorem roundOutput_ok (i : Nat) (hi : i < 8) (s : State) :
    ∃ s', runBlock isa (sboxOutputs i) s = some s' ∧
      (∀ p < 64, (s'.gpr lReg).getLsbD p =
        xorBits (fun k => if k = 0 then s.gpr lReg else s.gpr (q (k - 1)))
          (roundOutputBits i p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxOutputs i).all fun op => dst op != some r) = true →
        s'.gpr r = s.gpr r) := by
  have hchk := roundOutput_check i hi
  rw [sboxOutputsLiteral_eq i hi] at hchk
  let W : Nat → BitVec 64 := fun k =>
    if k = 0 then s.gpr lReg else s.gpr (q (k - 1))
  obtain ⟨s', hs', out, rd, wr, sp, keep, frame⟩ := linear_ok hchk
    (roundOutputCfg_ok s) W (fun r k h => by
      simp only [roundOutputRegs, List.mem_append, List.mem_singleton,
        Prod.mk.injEq, List.mem_map, List.mem_range] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨j, hj, heq⟩
      · exact ⟨by decide, rfl⟩
      · obtain ⟨rfl, rfl⟩ := heq
        refine ⟨by omega, ?_⟩
        simp [W]) (fun j _ hj => by simp [roundOutputCfg] at hj)
  refine ⟨s', hs', fun p hp => ?_, rd, wr, sp, ?_, keep⟩
  · exact out lReg (roundOutputBits i) (by simp) p hp
  · funext a
    apply frame a
    intro r hr hc
    simp only [slotRegion, roundOutputCfg, List.mem_singleton] at hr
    subst r
    simp [Region.Contains] at hc

theorem bitOf_word64 (W : Nat → BitVec 64) (j : Nat) :
    bitOf W (64 * j) = (W j).getLsbD 0 := by
  simp [bitOf]

theorem roundOutput_piece (i : Nat) (hi : i < 8) (s : State) (b : BitVec 4)
    (hb : ∀ j < 4, (s.gpr (q j)).getLsbD 0 = b.getLsbD j) :
    ∃ s', runBlock isa (sboxOutputs i) s = some s' ∧
      s'.gpr lReg = s.gpr lReg ^^^ (boxPiece i b).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxOutputs i).all fun op => dst op != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, bits, rd, wr, sp, mem, keep⟩ := roundOutput_ok i hi s
  refine ⟨s', run, ?_, rd, wr, sp, mem, keep⟩
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [bits p hp, roundOutputBits_shape i hi p hp]
  simp only [BitVec.getLsbD_xor, BitVec.zeroExtend_eq_setWidth,
    BitVec.getLsbD_setWidth, hp, decide_true, Bool.true_and]
  simp only [List.cons_append, List.nil_append, xorBits_cons, bitOf_low _ _ hp, ite_true]
  by_cases h : p < 32 ∧ boxSource p / 4 = i
  · simp only [h]
    have hj : 3 - boxSource p % 4 < 4 := by omega
    simp
    rw [bitOf_word64]
    have hn : 4 - boxSource p % 4 ≠ 0 := by omega
    have heq : 4 - boxSource p % 4 - 1 = 3 - boxSource p % 4 := by omega
    simp only [hn, ite_false, heq]
    rw [hb _ hj]
    simp only [boxPiece, getLsbD_ofBits, h.1, h.2, decide_true, Bool.true_and, ite_true]
  · simp only [h, ite_false, xorBits_nil]
    simp only [boxPiece, getLsbD_ofBits]
    by_cases hp32 : p < 32
    · have hs : boxSource p / 4 ≠ i := by omega
      simp only [hp32, decide_true, Bool.true_and, hs, ite_false]
    · simp only [hp32, decide_false, Bool.false_and]

/-- The registers a round keeps. -/
def roundKept : List Reg := [.ra, .s1, .s2, .s3, .s4, .a0, rReg, kp, cnt, kstep, passes]

theorem roundInput_keeps : ∀ i < 8, (lReg :: roundKept).all
    (fun r => (instrs (sboxInputsLiteral i)).all fun op => dst op != some r) = true := by
  decide +kernel

theorem roundOutput_keeps : ∀ i < 8, roundKept.all
    (fun r => (instrs (sboxOutputsLiteral i)).all fun op => dst op != some r) = true := by
  decide +kernel

theorem roundInput_keep (i : Nat) (hi : i < 8) (r : Reg) (hr : r ∈ lReg :: roundKept) :
    (sboxInputs i).all (fun op => dst op != some r) = true := by
  have h := List.all_eq_true.mp (roundInput_keeps i hi) r hr
  rw [sboxInputsLiteral_eq i hi] at h
  exact h

theorem roundOutput_keep (i : Nat) (hi : i < 8) (r : Reg) (hr : r ∈ roundKept) :
    (sboxOutputs i).all (fun op => dst op != some r) = true := by
  have h := List.all_eq_true.mp (roundOutput_keeps i hi) r hr
  rw [sboxOutputsLiteral_eq i hi] at h
  exact h

end VG.Proof.TripleDes.RISCV64
