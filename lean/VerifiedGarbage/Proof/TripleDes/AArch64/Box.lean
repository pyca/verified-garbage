module

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.TripleDes.AArch64.RoundLit
import VerifiedGarbage.Proof.TripleDes.Permutation
public import VerifiedGarbage.Proof.Framework.AArch64.Linear
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
public import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.TripleDes.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.Straight
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `TripleDes.AArch64.Spills`, which this module and modules that import it used -/

section

/-! ### `TripleDes.AArch64.Sbox`, which this module and modules that import it used -/

section

/-!
# DES S-box machine-code correctness

Untrusted. The kernel checks each allocated scalar circuit on all 64
inputs, then the sound truth-table evaluator lifts that check to every
bit position of arbitrary 64-bit words. This verifies both the circuits
and the allocator's output, including spills.
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.TripleDes.AArch64

noncomputable def sboxLiterals : Array (Prog isa) :=
  #[sbox0.lit, sbox1.lit, sbox2.lit, sbox3.lit, sbox4.lit, sbox5.lit, sbox6.lit, sbox7.lit]

noncomputable def sboxLiteral (i : Nat) : Prog isa := sboxLiterals.getD i (.block [])

def sboxCfg : Cfg := { base := .x2, slots := 64, ext := .x2, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 6).find? (fun k => q k == r)).map inputTable,
    slot := fun _ => none }

def sboxPost (i : Nat) (e : Env Nat) : Bool :=
  (List.range 4).all fun j => e.reg (q j) == some (outputTable i j)

theorem sbox_check : ∀ i < 8,
    check (table 64 64) sboxCfg (fun _ => none) (instrs (sboxLiteral i))
      sboxEnv (sboxPost i) = true := by
  lit_decide

def sboxWrites : List Reg := [.x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

theorem sbox_preserves : ∀ i < 8,
    [Reg.x0, .x1, .x2, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30].all
      (fun r => (instrs (sboxLiteral i)).all fun op => !clobbers op r) = true := by
  decide +kernel

def inputAt (s : State) (p : Nat) : BitVec 6 :=
  ofBits 6 fun j => (s.gpr (q j)).getLsbD p

theorem inputAt_bit (s : State) (p k : Nat) (hk : k < 6) :
    (inputAt s p).toNat.testBit k = (s.gpr (q k)).getLsbD p := by
  simp only [inputAt, BitVec.testBit_toNat, getLsbD_ofBits, hk, decide_true, Bool.true_and]

theorem sboxLiteral_eq : ∀ i < 8, sboxLiteral i = .block (sboxCode i)
  | 0, _ => sbox0.lit_eq.symm
  | 1, _ => sbox1.lit_eq.symm
  | 2, _ => sbox2.lit_eq.symm
  | 3, _ => sbox3.lit_eq.symm
  | 4, _ => sbox4.lit_eq.symm
  | 5, _ => sbox5.lit_eq.symm
  | 6, _ => sbox6.lit_eq.symm
  | 7, _ => sbox7.lit_eq.symm
  | n + 8, h => by omega

/-- Every S-box output bit, for arbitrary input words and any readable/
writable scratch state. Only the fixed scratch region can change. -/
theorem sbox_ok (i : Nat) (hi : i < 8) {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa (sboxCode i) s = some s' ∧
      (∀ j < 4, ∀ p < 64, (s'.gpr (q j)).getLsbD p =
        (Spec.TripleDes.sBox i (inputAt s p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  have codeEq : instrs (sboxLiteral i) = sboxCode i := by rw [sboxLiteral_eq i hi]; rfl
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ (sbox_check i hi)
  rw [codeEq] at he
  have hout : ∀ j < 4, e'.reg (q j) = some (outputTable i j) := by
    intro j hj
    have h := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    exact beq_iff_eq.mp h
  have key : ∀ p < 64, ∃ s', runBlock isa (sboxCode i) s = some s' ∧
      Post (TableRel p (inputAt s p).toNat) sboxCfg (fun _ => none) e' s s'
        (fun r => ((sboxCode i).all fun op => !clobbers op r) = false) := by
    intro p hp
    have hc := (inputAt s p).isLt
    refine run (table_sound hp hc) hok ⟨fun r a h => ?_,
      (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h),
      (fun _ _ h => by cases h)⟩ he
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hqr := List.find?_some hk
    have hk6 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
    simp only [beq_iff_eq] at hqr
    subst hqr
    simp only [TableRel, inputTable, testBit_tableOf, hc, decide_true, Bool.true_and,
      inputAt_bit s p k hk6]
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, p₀.sp, fun r hr => ?_, p₀.frame⟩
  · obtain ⟨s'', hs'', p₁⟩ := key p hp
    obtain rfl := run_unique hs'' hs'
    have h := p₁.rel.reg (q j) _ (hout j hj)
    simp only [TableRel, outputTable, testBit_tableOf, (inputAt s p).isLt,
      decide_true, Bool.true_and] at h
    rw [BitVec.ofNat_toNat] at h
    exact h.symm
  · apply p₀.other r
    have hrest : r ∈ [Reg.x0, .x1, .x2, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30] := by
      revert hr; cases r <;> decide
    have h := List.all_eq_true.mp (sbox_preserves i hi) r hrest
    rw [codeEq] at h
    simp [h]

end VG.Proof.TripleDes.AArch64

end

end

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64

def spillRegion (s : State) : Region := ⟨s.gpr .x2 + BitVec.ofNat 64 32, 384⟩

def spillSafe : Instr → Bool
  | .addImm .x d _ _ | .subImm .x d _ _ | .movz .x d _ _
  | .logic _ .x d _ _ | .ldr .x d _ _ => d != .x2
  | .str .x _ n off => decide (n = .x2 ∧ 32 ≤ off ∧ off + 8 ≤ 416)
  | _ => false

theorem spillSafe_check : ∀ i < 8,
    (instrs (sboxLiteral i)).all spillSafe = true := by decide +kernel

theorem write_frame (s : State) (d : Reg) (v : BitVec 64) (hd : d ≠ .x2) :
    (s.write .x d v).gpr .x2 = s.gpr .x2 ∧
      Frame [spillRegion s] s.mem (s.write .x d v).mem := by
  exact ⟨gpr_write_of_ne _ _ _ (Ne.symm hd), by
    rw [mem_write]; exact Frame.refl _ _⟩

theorem spillStep_frame (i : Instr) (s s' : State)
    (h : spillSafe i = true) (he : exec i s = some s') :
    s'.gpr .x2 = s.gpr .x2 ∧ Frame [spillRegion s] s.mem s'.mem := by
  cases i <;> simp only [spillSafe, Bool.false_eq_true] at h
  case addImm sz d n imm | subImm sz d n imm | movz sz d imm hw =>
    cases sz <;> simp only [Bool.false_eq_true] at h
    have hd : d ≠ .x2 := by simpa using h
    simp only [reduceExec] at he
    split at he <;> [skip; cases he]
    obtain rfl := Option.some.inj he
    exact write_frame _ _ _ hd
  case logic op sz d n m =>
    cases sz <;> simp only [Bool.false_eq_true] at h
    have hd : d ≠ .x2 := by simpa using h
    simp only [reduceExec, Option.some.injEq] at he
    subst s'
    exact write_frame _ _ _ hd
  case ldr sz d n off =>
    cases sz <;> simp only [Bool.false_eq_true] at h
    have hd : d ≠ .x2 := by simpa using h
    simp only [reduceExec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
    obtain ⟨a, _, v, _, rfl⟩ := he
    exact write_frame _ _ _ hd
  case str sz t n off =>
    cases sz <;> simp only [Bool.false_eq_true] at h
    obtain ⟨rfl, hlo, hhi⟩ := of_decide_eq_true h
    simp only [reduceExec, addr, Size.bytes] at he
    split at he <;> [skip; cases he]
    simp only [Option.bind_some, State.store] at he
    split at he <;> [skip; cases he]
    obtain rfl := Option.some.inj he
    refine ⟨rfl, ?_⟩
    change Frame [spillRegion s] s.mem (s.mem.writeW (s.gpr .x2 + BitVec.ofNat 64 off) (s.gpr t))
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
    exact Offset.contains (s.gpr .x2) (by omega_using [hlo]) (by omega_using [hhi]) (by decide)

theorem spillBlock_frame (is : List Instr) (s s' : State)
    (hsafe : is.all spillSafe = true) (he : runBlock isa is s = some s') :
    s'.gpr .x2 = s.gpr .x2 ∧ Frame [spillRegion s] s.mem s'.mem := by
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
    obtain ⟨hg, hf⟩ := spillStep_frame i s s₁ hsafe.1 hi
    obtain ⟨hg', hf'⟩ := ih s₁ hsafe.2 hrest
    refine ⟨hg'.trans hg, hf.trans ?_⟩
    have hr : spillRegion s₁ = spillRegion s := by simp only [spillRegion, hg]
    rw [hr] at hf'
    exact hf'

theorem sbox_spillFrame (i : Nat) (hi : i < 8) (s s' : State)
    (he : runBlock isa (sboxCode i) s = some s') :
    Frame [spillRegion s] s.mem s'.mem := by
  have h := spillSafe_check i hi
  rw [sboxLiteral_eq i hi] at h
  exact (spillBlock_frame _ _ _ h he).2

end VG.Proof.TripleDes.AArch64

end

end

/-! ### `TripleDes.AArch64.Round`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.TripleDes.AArch64

noncomputable def sboxInputsLiterals : Array (Prog isa) :=
  #[sboxInputs0.lit, sboxInputs1.lit, sboxInputs2.lit, sboxInputs3.lit, sboxInputs4.lit, sboxInputs5.lit, sboxInputs6.lit, sboxInputs7.lit]

noncomputable def sboxInputsLiteral (i : Nat) : Prog isa :=
  sboxInputsLiterals.getD i (.block [])

noncomputable def sboxOutputsLiterals : Array (Prog isa) :=
  #[sboxOutputs0.lit, sboxOutputs1.lit, sboxOutputs2.lit, sboxOutputs3.lit, sboxOutputs4.lit, sboxOutputs5.lit, sboxOutputs6.lit, sboxOutputs7.lit]

noncomputable def sboxOutputsLiteral (i : Nat) : Prog isa :=
  sboxOutputsLiterals.getD i (.block [])

def roundInputCfg : Cfg := { base := .x2, slots := 0, ext := .x22, exts := 1 }
def roundInputRegs : List (Reg × Nat) := [(.x20, 0)]

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

def roundOutputCfg : Cfg := { base := .x2, slots := 0, ext := .x2, exts := 0 }
def roundOutputRegs : List (Reg × Nat) :=
  [(.x19, 0)] ++ (List.range 4).map fun j => (q j, j + 1)

def roundOutputBits (i p : Nat) : List Nat :=
  [p] ++ ((List.range 4).filterMap fun j =>
    let position := 4 * i + 4 - j
    let dst := (Spec.TripleDes.p.toList.findIdx? (· == position)).getD 0
    if p = 31 - dst then some (64 * (j + 1)) else none)

theorem roundOutput_check : ∀ i < 8,
    check (lanes 64 9) roundOutputCfg (linExt 5) (instrs (sboxOutputsLiteral i))
      (linEnv roundOutputRegs) (linPost 9 [(.x19, roundOutputBits i)]) = true := by
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
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x22) 8) : Ok roundInputCfg s := by
  refine ⟨?_, ?_, by decide, ?_⟩
  · intro k hk; simp [roundInputCfg] at hk
  · intro k hk
    have hk0 : k = 0 := by simp only [roundInputCfg] at hk; omega_using [hk]
    subst k
    simpa only [roundInputCfg, wordAddr, Nat.mul_zero,
      BitVec.add_zero] using hread
  · intro k hk; simp [roundInputCfg] at hk

/-- The extraction block reads just one round key and forms six Boolean
input words. It does not change memory, access permissions or other registers. -/
theorem roundInput_ok (i : Nat) (hi : i < 8) (s : State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x22) 8) :
    ∃ s', runBlock isa (sboxInputs i) s = some s' ∧
      (∀ j < 6, ∀ p < 64, (s'.gpr (q j)).getLsbD p =
        xorBits (fun k => if k = 0 then s.gpr .x20
          else s.mem.readW (s.gpr .x22) 64) (roundInputBits i j p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxInputs i).all fun op => !clobbers op r) = true →
        s'.gpr r = s.gpr r) := by
  have hchk := roundInput_check i hi
  rw [sboxInputsLiteral_eq i hi] at hchk
  let W : Nat → BitVec 64 := fun k =>
    if k = 0 then s.gpr .x20 else s.mem.readW (s.gpr .x22) 64
  obtain ⟨s', hs', out, rd, wr, sp, keep, frame⟩ := linear_ok hchk
    (roundInputCfg_ok s hread) W (fun r k h => by
      simp only [roundInputRegs, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by decide, rfl⟩) (fun j hj => by
      have hj0 : j = 0 := by simp only [roundInputCfg] at hj; omega_using [hj]
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
  have hd : (64 + a) / 64 = 1 := by omega_using [ha]
  simp only [bitOf, hd, Nat.add_mod_left, Nat.mod_eq_of_lt ha]

def roundChunk (i : Nat) (r : BitVec 32) (k : BitVec 48) : BitVec 6 :=
  ((Spec.TripleDes.permute Spec.TripleDes.expansion r ^^^ k) >>> (6 * (7 - i))).setWidth 6

theorem roundChunk_bit (i j : Nat) (hi : i < 8) (hj : j < 6)
    (r : BitVec 64) (k : BitVec 64) :
    (roundChunk i (r.setWidth 32) (k.setWidth 48)).getLsbD j =
      (r.getLsbD (32 - Spec.TripleDes.expansion.getD (6 * i + 5 - j) 1) ^^
        k.getLsbD (47 - (6 * i + 5 - j))) := by
  have ht : 6 * (7 - i) + j < 48 := by omega_using [hj]
  have heq : 48 - 1 - (6 * (7 - i) + j) = 6 * i + 5 - j := by omega_using [hi]
  have hkey : 6 * (7 - i) + j = 47 - (6 * i + 5 - j) := by omega_using [hi, hj]
  have hsource : 32 - Spec.TripleDes.expansion.getD (6 * i + 5 - j) 1 < 32 := by
    have hb : ∀ t < 48, 1 ≤ Spec.TripleDes.expansion.getD t 1 := by decide +kernel
    have hpos : 6 * i + 5 - j < 48 := by omega_using [hi]
    have := hb _ hpos
    omega_using [this]
  simp only [roundChunk, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]
  rw [VG.Proof.TripleDes.permute_bit _ _ (by decide) _ ht]
  rw [heq]
  simp only [BitVec.getLsbD_setWidth, hsource, ht, decide_true, Bool.true_and]
  rw [hkey]

theorem roundInput_chunk (i : Nat) (hi : i < 8) (s : State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x22) 8) :
    ∃ s', runBlock isa (sboxInputs i) s = some s' ∧
      inputAt s' 0 = roundChunk i ((s.gpr .x20).setWidth 32)
        ((s.mem.readW (s.gpr .x22) 64).setWidth 48) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxInputs i).all fun op => !clobbers op r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, bits, rd, wr, sp, mem, keep⟩ := roundInput_ok i hi s hread
  refine ⟨s', run, ?_, rd, wr, sp, mem, keep⟩
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [inputAt, getLsbD_ofBits, hj, decide_true, Bool.true_and]
  rw [bits j hj 0 (by decide), roundChunk_bit i j hi hj]
  obtain ⟨hr, hk⟩ := roundInput_bounds i hi j hj
  simp only [roundInputBits, ite_true, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_low _ _ hr, bitOf_next _ _ hk, ite_true]
  rfl

def boxSource (p : Nat) : Nat := Spec.TripleDes.p.getD (31 - p) 1 - 1

def boxPiece (i : Nat) (b : BitVec 4) : BitVec 32 :=
  ofBits 32 fun p => if boxSource p / 4 = i then
    b.getLsbD (3 - boxSource p % 4) else false

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

theorem roundOutputCfg_ok (s : State) : Ok roundOutputCfg s := by
  refine ⟨?_, ?_, by decide, ?_⟩
  · intro k hk; simp [roundOutputCfg] at hk
  · intro k hk; simp [roundOutputCfg] at hk
  · intro k hk; simp [roundOutputCfg] at hk

/-- Deposit the four low S-box bits into L, at P's fixed destinations. -/
theorem roundOutput_ok (i : Nat) (hi : i < 8) (s : State) :
    ∃ s', runBlock isa (sboxOutputs i) s = some s' ∧
      (∀ p < 64, (s'.gpr .x19).getLsbD p =
        xorBits (fun k => if k = 0 then s.gpr .x19 else s.gpr (q (k - 1)))
          (roundOutputBits i p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxOutputs i).all fun op => !clobbers op r) = true →
        s'.gpr r = s.gpr r) := by
  have hchk := roundOutput_check i hi
  rw [sboxOutputsLiteral_eq i hi] at hchk
  let W : Nat → BitVec 64 := fun k =>
    if k = 0 then s.gpr .x19 else s.gpr (q (k - 1))
  obtain ⟨s', hs', out, rd, wr, sp, keep, frame⟩ := linear_ok hchk
    (roundOutputCfg_ok s) W (fun r k h => by
      simp only [roundOutputRegs, List.mem_append, List.mem_singleton,
        Prod.mk.injEq, List.mem_map, List.mem_range] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨j, hj, heq⟩
      · exact ⟨by decide, rfl⟩
      · obtain ⟨rfl, rfl⟩ := heq
        refine ⟨by omega_using [hj], ?_⟩
        simp [W]) (fun j hj => by simp [roundOutputCfg] at hj)
  refine ⟨s', hs', fun p hp => ?_, rd, wr, sp, ?_, keep⟩
  · exact out .x19 (roundOutputBits i) (by simp) p hp
  · funext a
    apply frame a
    intro r hr hc
    simp only [slotRegion, roundOutputCfg, List.mem_singleton] at hr
    subst r
    simp [Region.Contains] at hc

theorem bitOf_word (W : Nat → BitVec 64) (j : Nat) :
    bitOf W (64 * j) = (W j).getLsbD 0 := by
  simp [bitOf]

theorem roundOutput_piece (i : Nat) (hi : i < 8) (s : State) (b : BitVec 4)
    (hb : ∀ j < 4, (s.gpr (q j)).getLsbD 0 = b.getLsbD j) :
    ∃ s', runBlock isa (sboxOutputs i) s = some s' ∧
      s'.gpr .x19 = s.gpr .x19 ^^^ (boxPiece i b).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, ((sboxOutputs i).all fun op => !clobbers op r) = true →
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
    have hj : 3 - boxSource p % 4 < 4 := by omega_using []
    simp
    rw [bitOf_word]
    have hn : 4 - boxSource p % 4 ≠ 0 := by omega_using []
    have heq : 4 - boxSource p % 4 - 1 = 3 - boxSource p % 4 := by omega_using []
    simp only [hn, ite_false, heq]
    rw [hb _ hj]
    simp only [boxPiece, getLsbD_ofBits, h.1, h.2, decide_true, Bool.true_and, ite_true]
  · simp only [h, ite_false, xorBits_nil]
    simp only [boxPiece, getLsbD_ofBits]
    by_cases hp32 : p < 32
    · have hs : boxSource p / 4 ≠ i := by omega_using [h, hp32]
      simp only [hp32, decide_true, Bool.true_and, hs, ite_false]
    · simp only [hp32, decide_false, Bool.false_and]

def roundKept : List Reg := [.x0, .x1, .x2, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30]

theorem roundInput_keeps : ∀ i < 8, (.x19 :: roundKept).all
    (fun r => (instrs (sboxInputsLiteral i)).all fun op => !clobbers op r) = true := by
  decide +kernel

theorem roundOutput_keeps : ∀ i < 8, roundKept.all
    (fun r => (instrs (sboxOutputsLiteral i)).all fun op => !clobbers op r) = true := by
  decide +kernel

theorem roundInput_keep (i : Nat) (hi : i < 8) (r : Reg) (hr : r ∈ .x19 :: roundKept) :
    (sboxInputs i).all (fun op => !clobbers op r) = true := by
  have h := List.all_eq_true.mp (roundInput_keeps i hi) r hr
  rw [sboxInputsLiteral_eq i hi] at h
  exact h

theorem roundOutput_keep (i : Nat) (hi : i < 8) (r : Reg) (hr : r ∈ roundKept) :
    (sboxOutputs i).all (fun op => !clobbers op r) = true := by
  have h := List.all_eq_true.mp (roundOutput_keeps i hi) r hr
  rw [sboxOutputsLiteral_eq i hi] at h
  exact h

end VG.Proof.TripleDes.AArch64

end

end

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.TripleDes.AArch64

theorem runBoxes_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

/-- One complete DES S-box contribution, including E/key input extraction,
the Boolean circuit, and P output placement. -/
theorem box_ok (i : Nat) (hi : i < 8) (s : State) (hok : Ok sboxCfg s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .x22) 8) :
    ∃ s', runBlock isa (box i) s = some s' ∧
      s'.gpr .x19 = s.gpr .x19 ^^^
        (boxPiece i (Spec.TripleDes.sBox i
          (roundChunk i ((s.gpr .x20).setWidth 32)
            ((s.mem.readW (s.gpr .x22) 64).setWidth 48)))).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r ∈ roundKept, s'.gpr r = s.gpr r) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, chunk, rd₁, wr₁, sp₁, mem₁, keep₁⟩ := roundInput_chunk i hi s hread
  have kept₁ : ∀ r ∈ .x19 :: roundKept, s₁.gpr r = s.gpr r :=
    fun r hr => keep₁ r (roundInput_keep i hi r hr)
  have hok₁ : Ok sboxCfg s₁ := hok.congr
    (kept₁ .x2 (by decide)) (kept₁ .x2 (by decide)) rd₁ wr₁
  obtain ⟨s₂, run₂, bits, rd₂, wr₂, sp₂, keep₂, _⟩ := sbox_ok i hi hok₁
  have hbits : ∀ j < 4, (s₂.gpr (q j)).getLsbD 0 =
      (Spec.TripleDes.sBox i (roundChunk i ((s.gpr .x20).setWidth 32)
        ((s.mem.readW (s.gpr .x22) 64).setWidth 48))).getLsbD j := by
    intro j hj
    rw [bits j hj 0 (by decide), chunk]
  obtain ⟨s₃, run₃, value, rd₃, wr₃, sp₃, mem₃, keep₃⟩ := roundOutput_piece i hi s₂ _ hbits
  refine ⟨s₃, ?_, ?_, rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁), ?_, ?_⟩
  · simp only [box, runBoxes_append, run₁, Option.bind_some, run₂, run₃]
  · rw [value, keep₂ .x19 (by decide), kept₁ .x19 (by decide)]
  · intro r hr
    rw [keep₃ r (roundOutput_keep i hi r hr), keep₂ r ?_, kept₁ r (List.mem_cons_of_mem _ hr)]
    revert hr; cases r <;> decide
  · have hf := sbox_spillFrame i hi s₁ s₂ run₂
    have hregion : spillRegion s₁ = spillRegion s := by
      simp only [spillRegion, kept₁ .x2 (by decide)]
    rw [hregion, mem₁] at hf
    rw [mem₃]
    exact hf

end VG.Proof.TripleDes.AArch64
