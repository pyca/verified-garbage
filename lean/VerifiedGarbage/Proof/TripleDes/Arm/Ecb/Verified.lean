module

import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.TripleDes.EcbMemory
import VerifiedGarbage.Proof.Rc2.Arm.KeySteps
public import VerifiedGarbage.Proof.TripleDes.Scratch
import VerifiedGarbage.Proof.TripleDes.Arm.Bytes
import VerifiedGarbage.Proof.TripleDes.Arm.Initial
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.TripleDes.Arm.Round
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Reduce
import VerifiedGarbage.Proof.TripleDes.Round
public import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.Framework.AddrArith
import Batteries.Logic
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.Arm.Lookup
public import VerifiedGarbage.Proof.Rc2.Arm.Save
public import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.TripleDes.Arm.WordStore
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.TripleDes.Schedule
public import VerifiedGarbage.Proof.TripleDes.Arm.ConstantTime
import VerifiedGarbage.Proof.TripleDes.Arm.FunctionsLit
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `TripleDes.Arm.Pre`, which only this module used -/

section

/-! ### `TripleDes.Arm.Block`, which only this module used -/

section

/-! ### `TripleDes.Arm.Head`, which only this module used -/

section

/-! ### `TripleDes.Arm.Body`, which only this module used -/

section

/-! ### `TripleDes.Arm.Box`, which only this module used -/

section

/-! ## `Spills` -/

@[expose] public section

section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm

def spillRegion (s : State) : Region := ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 60, 388⟩
def spillSafe : Instr → Bool
  | .mov d _ | .dp _ d _ _ | .ldr d _ _ => d != .r2
  | .str _ n off => decide (n = .r2 ∧ 60 ≤ off ∧ off + 4 ≤ 448)
  | _ => false

theorem spillSafe_check : ∀ i < 8,
    (instrs (sboxLiteral i)).all spillSafe = true := by decide +kernel

theorem write_frame (s : State) (d : Reg) (v : BitVec 32) (hd : d ≠ .r2) :
    (s.setReg d v).gpr .r2 = s.gpr .r2 ∧ Frame [spillRegion s] s.mem (s.setReg d v).mem :=
  ⟨gpr_setReg_of_ne _ _ (Ne.symm hd), by rw [mem_setReg]; exact Frame.refl _ _⟩

theorem spillStep_frame (i : Instr) (s s' : State)
    (fit : (s.gpr .r2).toNat + 512 ≤ 2 ^ 32)
    (h : spillSafe i = true) (he : exec i s = some s') :
    s'.gpr .r2 = s.gpr .r2 ∧ Frame [spillRegion s] s.mem s'.mem := by
  cases i <;> simp only [spillSafe, Bool.false_eq_true] at h
  case mov d op2 =>
    obtain hd : d ≠ .r2 := by simpa using h
    simp only [reduceExec, Option.map_eq_some_iff] at he
    obtain ⟨v, _, rfl⟩ := he
    exact write_frame _ _ _ hd
  case dp op d n op2 =>
    obtain hd : d ≠ .r2 := by simpa using h
    simp only [reduceExec, Option.map_eq_some_iff] at he
    obtain ⟨v, _, rfl⟩ := he
    exact write_frame _ _ _ hd
  case ldr d n off =>
    obtain hd : d ≠ .r2 := by simpa using h
    simp only [reduceExec] at he
    split at he <;> [skip; cases he]
    simp only [Option.map_eq_some_iff] at he
    obtain ⟨v, _, rfl⟩ := he
    exact write_frame _ _ _ hd
  case str t n off =>
    obtain ⟨rfl, hlo, hhi⟩ := of_decide_eq_true h
    simp only [reduceExec] at he
    split at he <;> [skip; cases he]
    simp only [State.store32] at he
    split at he <;> [skip; cases he]
    obtain rfl := Option.some.inj he
    refine ⟨rfl, ?_⟩
    rw [addr_add (by omega_using [fit, hhi])]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (State.addr (s.gpr .r2)) (by omega_using [hlo]) (by omega_using [hhi]) (by decide))

theorem spillBlock_frame (is : List Instr) (s s' : State)
    (fit : (s.gpr .r2).toNat + 512 ≤ 2 ^ 32)
    (hsafe : is.all spillSafe = true) (he : runBlock isa is s = some s') :
    s'.gpr .r2 = s.gpr .r2 ∧ Frame [spillRegion s] s.mem s'.mem := by
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
    obtain ⟨hg, hf⟩ := spillStep_frame i s s₁ fit hsafe.1 hi
    obtain ⟨hg', hf'⟩ := ih s₁ (by rw [hg]; exact fit) hsafe.2 hrest
    refine ⟨hg'.trans hg, hf.trans ?_⟩
    obtain hr : spillRegion s₁ = spillRegion s := by simp only [spillRegion, hg]
    rw [hr] at hf'
    exact hf'

theorem sbox_spillFrame (i : Nat) (hi : i < 8) (s s' : State)
    (fit : (s.gpr .r2).toNat + 512 ≤ 2 ^ 32)
    (he : runBlock isa (sboxCode i) s = some s') : Frame [spillRegion s] s.mem s'.mem := by
  obtain h := spillSafe_check i hi
  rw [sboxLiteral_eq i hi] at h
  exact (spillBlock_frame _ _ _ fit h he).2
end VG.Proof.TripleDes.Arm

end

/-! ## `Box` -/

section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm

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
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4) :
    ∃ s', runBlock isa (box i) s = some s' ∧
      s'.gpr .r10 = s.gpr .r10 ^^^
        (boxPiece i (Spec.TripleDes.sBox i
          (roundChunk i ((s.gpr .r11).setWidth 32)
            ((keyWord s).setWidth 48)))).zeroExtend 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r ∈ roundKept, s'.gpr r = s.gpr r) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, chunk, rd₁, wr₁, sp₁, mem₁, keep₁⟩ := roundInput_chunk i hi s hread
  obtain kept₁ : ∀ r ∈ .r10 :: roundKept, s₁.gpr r = s.gpr r :=
    fun r hr => keep₁ r (roundInput_keep i hi r hr)
  have hok₁ : Ok sboxCfg s₁ := hok.congr
    (kept₁ .r2 (by decide)) (kept₁ .r2 (by decide)) rd₁ wr₁
  obtain ⟨s₂, run₂, bits, rd₂, wr₂, sp₂, keep₂, _⟩ := sbox_ok i hi hok₁
  obtain hbits : ∀ j < 4, (s₂.gpr (q j)).getLsbD 0 =
      (Spec.TripleDes.sBox i (roundChunk i ((s.gpr .r11).setWidth 32)
        ((keyWord s).setWidth 48))).getLsbD j := by
    intro j hj
    rw [bits j hj 0 (by decide), chunk]
  obtain ⟨s₃, run₃, value, rd₃, wr₃, sp₃, mem₃, keep₃⟩ := roundOutput_piece i hi s₂ _ hbits
  refine ⟨s₃, ?_, ?_, rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁), ?_, ?_⟩
  · simp only [box, runBoxes_append, run₁, Option.bind_some, run₂, run₃]
  · rw [value, keep₂ .r10 (by decide), kept₁ .r10 (by decide)]
  · intro r hr
    rw [keep₃ r (roundOutput_keep i hi r hr), keep₂ r ?_, kept₁ r (List.mem_cons_of_mem _ hr)]
    revert hr; cases r <;> decide
  · have hf := sbox_spillFrame i hi s₁ s₂ hok₁.slots run₂
    obtain hregion : spillRegion s₁ = spillRegion s := by
      simp only [spillRegion, kept₁ .r2 (by decide)]
    rw [hregion, mem₁] at hf
    rw [mem₃]
    exact hf

end VG.Proof.TripleDes.Arm

end

end

end

/-! ### `TripleDes.Arm.RoundFunction`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.Arm

open VG VG.Bitslice VG.Spec.TripleDes

theorem boxSource_shape : ∀ j < 32,
    7 - (32 - p.getD (31 - j) 1) / 4 = boxSource j / 4 ∧
    (32 - p.getD (31 - j) 1) % 4 = 3 - boxSource j % 4 ∧
    boxSource j / 4 < 8 := by
  decide +kernel

theorem boxPiece_round_bit (i : Nat) (r : BitVec 32) (k : BitVec 48)
    (j : Nat) (hj : j < 32) :
    (boxPiece i (sBox i (roundChunk i r k))).getLsbD j =
      if boxSource j / 4 = i then (roundFunction r k).getLsbD j else false := by
  simp only [boxPiece, getLsbD_ofBits, hj, decide_true, Bool.true_and]
  by_cases heq : boxSource j / 4 = i
  · simp only [heq, ite_true]
    rw [VG.Proof.TripleDes.roundFunction_bit r k j hj]
    obtain ⟨hidx, hbit, _⟩ := boxSource_shape j hj
    simp only [hidx, hbit, heq, roundChunk]
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
    (List.range 8).foldl (fun out i => out ^^^ boxPiece i (sBox i (roundChunk i r k)))
      (0 : BitVec 32) = roundFunction r k := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain hfold : (fun (out : Bool) i => out ^^
      (boxPiece i (sBox i (roundChunk i r k))).getLsbD j) =
      (fun out i => out ^^ (if boxSource j / 4 = i then
        (roundFunction r k).getLsbD j else false)) := by
    funext out i
    exact congrArg (fun b => out ^^ b) (boxPiece_round_bit i r k j hj)
  obtain hbits := foldl_xor_bits (List.range 8)
    (fun i => boxPiece i (sBox i (roundChunk i r k))) 0 j
  obtain hz : (0 : BitVec 32).getLsbD j = false := by
    change (BitVec.ofNat 32 0).getLsbD j = false
    exact BitVec.getLsbD_zero
  obtain hinit := congrArg (fun b : Bool => (List.range 8).foldl
    (fun out i => out ^^ (boxPiece i (sBox i (roundChunk i r k))).getLsbD j) b) hz
  have hchange := congrArg
    (fun f : Bool → Nat → Bool => (List.range 8).foldl f false) hfold
  exact hbits.trans (hinit.trans (hchange.trans (select_xor _ (boxSource_shape j hj).2.2 _)))

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

end VG.Proof.TripleDes.Arm

end

end


/-! ## `RoundBody` -/

@[expose] public section

section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm

def contribution (r : BitVec 32) (k : BitVec 64) (i : Nat) : BitVec 32 :=
  (boxPiece i (Spec.TripleDes.sBox i
    (roundChunk i (r.setWidth 32) (k.setWidth 48)))).zeroExtend 32

/-- Compose any ordered list of S-boxes. The schedule word and Feistel
right half stay fixed; each contribution is XORed into the left half. -/
theorem boxes_ok (indices : List Nat) (hindices : ∀ i ∈ indices, i < 8)
    (r : BitVec 32) (k : BitVec 64) (s : State) (hok : Ok sboxCfg s)
    (hr : s.gpr .r11 = r) (hk : keyWord s = k)
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4)
    (hsep : ∀ j < 2, (⟨wordAddr (s.gpr .r0) j, 4⟩ : Region).Disjoint (spillRegion s)) :
    ∃ s', runBlock isa (indices.flatMap box) s = some s' ∧
      s'.gpr .r10 = indices.foldl (fun out i => out ^^^ contribution r k i) (s.gpr .r10) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ roundKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  induction indices generalizing s with
  | nil =>
    exact ⟨s, runBlock_nil, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | cons i indices ih =>
    obtain hi : i < 8 := hindices i (List.mem_cons_self)
    obtain ⟨s₁, run₁, value₁, rd₁, wr₁, sp₁, keep₁, frame₁⟩ := box_ok i hi s hok hread
    obtain hregion : spillRegion s₁ = spillRegion s := by
      simp only [spillRegion, keep₁ .r2 (by decide)]
    obtain hr₁ : s₁.gpr .r11 = r := (keep₁ .r11 (by decide)).trans hr
    have hword (j : Nat) (hj : j < 2) :
        s₁.mem.readW (wordAddr (s₁.gpr .r0) j) 32 = s.mem.readW (wordAddr (s.gpr .r0) j) 32 := by
      rw [keep₁ .r0 (by decide)]
      apply frame₁.readW (r := ⟨wordAddr (s.gpr .r0) j, 4⟩) (Region.contains_self _ _)
        (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hsep j hj) (by decide)
    obtain hk₁ : keyWord s₁ = k := by
      unfold keyWord
      rw [hword 0 (by decide), hword 1 (by decide)]
      exact hk
    obtain hread₁ : ∀ j < 2, InRegions (s₁.rd ++ s₁.wr) (wordAddr (s₁.gpr .r0) j) 4 := by
      rw [rd₁, wr₁, keep₁ .r0 (by decide)]
      exact hread
    obtain hsep₁ : ∀ j < 2, (⟨wordAddr (s₁.gpr .r0) j, 4⟩ : Region).Disjoint (spillRegion s₁) := by
      rw [keep₁ .r0 (by decide), hregion]
      exact hsep
    have hok₁ : Ok sboxCfg s₁ := hok.congr
      (keep₁ .r2 (by decide)) (keep₁ .r2 (by decide)) rd₁ wr₁
    obtain ⟨s₂, run₂, value₂, rd₂, wr₂, sp₂, keep₂, frame₂⟩ := ih
      (fun j hj => hindices j (List.mem_cons_of_mem _ hj)) s₁ hok₁ hr₁ hk₁ hread₁ hsep₁
    refine ⟨s₂, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_, ?_⟩
    · simp only [List.flatMap_cons, runBoxes_append, run₁, Option.bind_some, run₂]
    · rw [hr, hk] at value₁
      change s₁.gpr .r10 = s.gpr .r10 ^^^ contribution r k i at value₁
      simpa only [List.foldl_cons, ← value₁] using value₂
    · exact fun q hq => (keep₂ q hq).trans (keep₁ q hq)
    · rw [hregion] at frame₂
      exact frame₁.trans frame₂

theorem contributions_roundFunction (r : BitVec 32) (k : BitVec 64) (l : BitVec 32) :
    (List.range 8).foldl (fun out i => out ^^^ contribution r k i) l =
      l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48) := by
  rw [foldl_xor_start]
  exact congrArg (l ^^^ ·) (by
    simpa only [contribution, BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_eq] using
      boxPieces_eq_roundFunction r (k.setWidth 48))

def roundOuterKept : List Reg := [.r0, .r1, .r2, .r3, .r9]

theorem swapHalves_ok (s : State) :
    ∃ s', runBlock isa swapHalves s = some s' ∧
      s'.gpr .r10 = s.gpr .r11 ∧ s'.gpr .r11 = s.gpr .r10 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ q ∈ roundOuterKept, s'.gpr q = s.gpr q) := by
  open VG.Arm.RegUpd in
  refine ⟨_, by
    simp only [swapHalves, rr, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · simp only [sp_setReg]
  · simp only [mem_setReg]
  · intro q hq
    obtain hneq : q ≠ .lr ∧ q ≠ .r10 ∧ q ≠ .r11 := by revert hq; cases q <;> decide
    simp only [gpr_setReg, hneq.1, hneq.2.1, hneq.2.2, ite_false]

/-- One full Feistel round, with all eight S-boxes and the half swap. -/
theorem roundBody_ok (s : State) (l r : BitVec 32) (k : BitVec 64)
    (hl : s.gpr .r10 = l) (hr : s.gpr .r11 = r)
    (hk : keyWord s = k) (hok : Ok sboxCfg s)
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4)
    (hsep : ∀ j < 2, (⟨wordAddr (s.gpr .r0) j, 4⟩ : Region).Disjoint (spillRegion s)) :
    ∃ s', runBlock isa roundBody s = some s' ∧
      s'.gpr .r10 = r ∧
      s'.gpr .r11 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ roundOuterKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, value, rd₁, wr₁, sp₁, keep₁, frame₁⟩ := boxes_ok (List.range 8)
    (fun i hi => List.mem_range.mp hi) (r) k s hok hr hk hread hsep
  obtain ⟨s₂, run₂, left, right, rd₂, wr₂, sp₂, mem₂, keep₂⟩ := swapHalves_ok s₁
  refine ⟨s₂, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_, ?_⟩
  · simp only [roundBody, runBoxes_append, run₁, Option.bind_some, run₂]
  · exact left.trans ((keep₁ .r11 (by decide)).trans hr)
  · rw [right, value, contributions_roundFunction, hl]
  · intro q hq
    obtain hq' : q ∈ roundKept := by revert hq; cases q <;> decide
    exact (keep₂ q hq).trans (keep₁ q hq')
  · rw [mem₂]
    exact frame₁

end VG.Proof.TripleDes.Arm

end

/-! ## `RoundStep` -/

section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.Straight VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (gpr_subFlags mem_subFlags)

def roundStepKept : List Reg := [.r1, .r2, .r3]

theorem countDown_rules : ∀ n < 17, 1 ≤ n →
    (BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1)) ∧
    (!(BitVec.ofNat 32 n - 1 == 0)) = decide (n ≠ 1) := by decide +kernel

theorem roundAdvance_ok (d : Spec.TripleDes.Direction) (s : State) :
    ∃ s', runBlock isa (roundAdvance d) s = some s' ∧
      s'.gpr .r0 = (if d = .encrypt then s.gpr .r0 + 8 else s.gpr .r0 - 8) ∧
      s'.gpr .r9 = s.gpr .r9 - 1 ∧
      s'.z = ((s.gpr .r9 - 1) == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .r9 → r ≠ .r0 → s'.gpr r = s.gpr r) := by
  cases d <;> refine ⟨_, by
    simp only [roundAdvance, ite_true, reduceCtorEq, ite_false, runBlock_cons,
      exec, Op2.eval, encodable, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false,
    z_setReg, subFlags, rd_setReg, wr_setReg, sp_setReg, mem_setReg]
  all_goals try rfl
  all_goals
    intro r hr₁ hr₂
    simp only [hr₁, hr₂, ite_false]

theorem roundStep_ok (d : Spec.TripleDes.Direction) (s : State)
    (l r : BitVec 32) (k : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn' : n < 17)
    (hl : s.gpr .r10 = l) (hr : s.gpr .r11 = r)
    (hk : keyWord s = k) (hok : Ok sboxCfg s)
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4)
    (hsep : ∀ j < 2, (⟨wordAddr (s.gpr .r0) j, 4⟩ : Region).Disjoint (spillRegion s))
    (hcount : s.gpr .r9 = BitVec.ofNat 32 n) :
    ∃ s', runBlock isa (roundBody ++ roundAdvance d) s = some s' ∧
      s'.gpr .r10 = r ∧
      s'.gpr .r11 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)) ∧
      s'.gpr .r0 = (if d = .encrypt then s.gpr .r0 + 8 else s.gpr .r0 - 8) ∧
      s'.gpr .r9 = BitVec.ofNat 32 (n - 1) ∧
      isa.eval .ne s' = some (decide (n ≠ 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ roundStepKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, left₁, right₁, rd₁, wr₁, sp₁, keep₁, frame₁⟩ :=
    roundBody_ok s l r k hl hr hk hok hread hsep
  obtain ⟨s₂, run₂, ptr₂, count₂, z₂, rd₂, wr₂, sp₂, mem₂, keep₂⟩ := roundAdvance_ok d s₁
  obtain ⟨hsub, hzero⟩ := countDown_rules n hn' hn
  obtain hcount₁ : s₁.gpr .r9 = BitVec.ofNat 32 n := (keep₁ .r9 (by decide)).trans hcount
  refine ⟨s₂, ?_, ?_, ?_, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_, ?_⟩
  · simp only [runBoxes_append, run₁, Option.bind_some, run₂]
  · exact (keep₂ .r10 (by decide) (by decide)).trans left₁
  · exact (keep₂ .r11 (by decide) (by decide)).trans right₁
  · rw [ptr₂, keep₁ .r0 (by decide)]
  · rw [count₂, hcount₁, hsub]
  · change VG.Arm.eval .ne s₂ = _
    simp only [VG.Arm.eval, z₂, hcount₁, hzero]
  · intro q hq
    obtain hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    obtain hneq : q ≠ .r9 ∧ q ≠ .r0 := by revert hq; cases q <;> decide
    exact (keep₂ q hneq.1 hneq.2).trans (keep₁ q hq')
  · rw [mem₂]; exact frame₁

end VG.Proof.TripleDes.Arm

end

/-! ## `Loop` -/

section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix feistelStep)

def keyAddr (base : BitVec 32) (direction : Direction) (j : Nat) : BitVec 32 :=
  base + BitVec.ofNat 32 (8 * (if direction = .encrypt then j else 15 - j))

def readKey (m : Mem) (ptr : BitVec 32) : BitVec 64 :=
  m.readW (wordAddr ptr 1) 32 ++ m.readW (wordAddr ptr 0) 32

theorem readKey_frame {m m' : Mem} {ptr : BitVec 32} {regions : List Region}
    (hf : Frame regions m m')
    (sep : ∀ j < 2, ∀ r ∈ regions, (⟨wordAddr ptr j, 4⟩ : Region).Disjoint r) :
    readKey m' ptr = readKey m ptr := by
  exact congrArg₂ (fun hi lo : BitVec 32 => hi ++ lo)
    (hf.readW (a := wordAddr ptr 1) (w := 32) (r := ⟨wordAddr ptr 1, 4⟩)
      (Region.contains_self _ _) (sep 1 (by decide)) (by decide))
    (hf.readW (a := wordAddr ptr 0) (w := 32) (r := ⟨wordAddr ptr 0, 4⟩)
      (Region.contains_self _ _) (sep 0 (by decide)) (by decide))

theorem keyAddr_step (base : BitVec 32) (direction : Direction) (j : Nat) (hj : j < 15) :
    (if direction = .encrypt then keyAddr base direction j + 8
      else keyAddr base direction j - 8) = keyAddr base direction (j + 1) := by
  cases direction
  · change base + BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 8 = base + BitVec.ofNat 32 (8 * (j + 1))
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega_using [])
  · change base + BitVec.ofNat 32 (8 * (15 - j)) - BitVec.ofNat 32 8 = base + BitVec.ofNat 32 (8 * (15 - (j + 1)))
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      Offset.ofNat_sub_ofNat (by omega_using [hj])]
    exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega_using [])

def endPointer (base : BitVec 32) (d : Direction) : BitVec 32 :=
  if d = .encrypt then base + 128 else base - 8

theorem keyAddr_end (base : BitVec 32) (d : Direction) :
    (if d = .encrypt then keyAddr base d 15 + 8 else keyAddr base d 15 - 8) = endPointer base d := by
  cases d <;> simp only [endPointer, keyAddr, reduceCtorEq, ite_true, ite_false, Nat.reduceSub, Nat.reduceMul]
  · change base + BitVec.ofNat 32 120 + BitVec.ofNat 32 8 = base + BitVec.ofNat 32 128
    rw [Offset.add_ofNat_add_ofNat]
  · rw [BitVec.add_zero]

structure LoopInv (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (n : Nat) (s : State) : Prop where
  positive : 1 ≤ n
  bounded : n ≤ 16
  left : s.gpr .r10 = (roundPrefix keys direction (16 - n) v).1
  right : s.gpr .r11 = (roundPrefix keys direction (16 - n) v).2
  counter : s.gpr .r9 = BitVec.ofNat 32 n
  pointer : s.gpr .r0 = keyAddr base direction (16 - n)
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

structure LoopPost (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .r10 = (roundPrefix keys direction 16 v).1
  right : s.gpr .r11 = (roundPrefix keys direction 16 v).2
  counter : s.gpr .r9 = 0
  pointer : s.gpr .r0 = endPointer base direction
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

theorem loopStep (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base direction j) t, 4⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (readKey origin.mem (keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j)
    (n : Nat) (s : State) (hs : LoopInv keys direction base origin v n s) :
    WP isa (.block (roundBody ++ roundAdvance direction)) s (fun s' =>
      (isa.eval .ne s' = some false ∧ LoopPost keys direction base origin v s') ∨
      (isa.eval .ne s' = some true ∧ ∃ m < n, LoopInv keys direction base origin v m s')) := by
  obtain hj : 16 - n < 16 := by omega_using [hs.positive]
  obtain hwork : spillRegion s = spillRegion origin := by
    simp only [spillRegion, hs.regs .r2 (by decide)]
  have hokS : Ok sboxCfg s := hok.congr
    (hs.regs .r2 (by decide)) (hs.regs .r2 (by decide)) hs.rd hs.wr
  obtain hreadS : ∀ t < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) t) 4 := by
    rw [hs.rd, hs.wr, hs.pointer]; exact hread _ hj
  obtain hsepS : ∀ t < 2, (⟨wordAddr (s.gpr .r0) t, 4⟩ : Region).Disjoint (spillRegion s) := by
    rw [hs.pointer, hwork]; exact hsep _ hj
  obtain hk : (keyWord s).setWidth 48 = roundKey keys direction (16 - n) := by
    change (readKey s.mem (s.gpr .r0)).setWidth 48 = _
    rw [hs.pointer]
    obtain hmem := readKey_frame hs.frame (ptr := keyAddr base direction (16 - n))
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hsep _ hj t ht)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hkeys _ hj)
  obtain ⟨s', run, left, right, ptr, count, flag, rd, wr, sp, regs, frame⟩ :=
    roundStep_ok direction s _ _ (keyWord s) n hs.positive
      (by omega_using [hs.bounded]) hs.left hs.right rfl hokS hreadS hsepS
      hs.counter
  obtain hidx : 16 - (n - 1) = 16 - n + 1 := by
    omega_using [hs.positive, hs.bounded]
  obtain hleft : s'.gpr .r10 = (roundPrefix keys direction (16 - (n - 1)) v).1 := by
    rw [hidx]
    exact left.trans (congrArg (fun pair => pair.1)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  obtain hright : s'.gpr .r11 = (roundPrefix keys direction (16 - (n - 1)) v).2 := by
    rw [hidx]
    obtain hval := congrArg (fun key =>
      ((roundPrefix keys direction (16 - n) v).1 ^^^
        Spec.TripleDes.roundFunction (roundPrefix keys direction (16 - n) v).2 key)) hk
    exact (right.trans hval).trans (congrArg (fun pair => pair.2)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  obtain hframe : Frame [spillRegion origin] origin.mem s'.mem := by
    rw [hwork] at frame
    exact hs.frame.trans frame
  obtain hregs : ∀ q ∈ roundStepKept, s'.gpr q = origin.gpr q :=
    fun q hq => (regs q hq).trans (hs.regs q hq)
  refine WP.of_runBlock ⟨s', run, ?_⟩
  by_cases hlast : n = 1
  · left
    refine ⟨?_, ?_⟩
    · simpa only [hlast, ne_eq, not_true_eq_false, decide_false] using flag
    · subst n
      exact ⟨hleft, hright, count, by
        rw [ptr, hs.pointer]
        exact keyAddr_end base direction, rd.trans hs.rd, wr.trans hs.wr, sp.trans hs.sp, hregs, hframe⟩
  · right
    refine ⟨?_, n - 1, by omega_using [hs.positive], ?_⟩
    · simpa only [hlast, ne_eq, not_false_eq_true, decide_true] using flag
    · refine ⟨by omega_using [hs.positive, hlast], by omega_using [hs.bounded],
        hleft, hright, count, ?_, rd.trans hs.rd, wr.trans hs.wr, sp.trans hs.sp, hregs, hframe⟩
      rw [ptr, hs.pointer, keyAddr_step base direction (16 - n) (by
        omega_using [hs.positive, hlast]), ← hidx]

/-- The complete sixteen-round loop, in either key order. -/
theorem roundsLoop_ok (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .r10 = v.1) (hr : origin.gpr .r11 = v.2)
    (hptr : origin.gpr .r0 = keyAddr base direction 0)
    (hcount : origin.gpr .r9 = BitVec.ofNat 32 16)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base direction j) t, 4⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (readKey origin.mem (keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j) :
    WP isa (.loop (.block (roundBody ++ roundAdvance direction)) .ne)
      origin (LoopPost keys direction base origin v) := by
  apply WP.loop (M := isa) (body := .block (roundBody ++ roundAdvance direction))
    (c := .ne) (Q := LoopPost keys direction base origin v) (LoopInv keys direction base origin v)
    (loopStep keys direction base origin v hok hread hsep hkeys)
    16 origin
  exact ⟨by decide, by decide, hl, hr, hcount, hptr, rfl, rfl, rfl,
    fun _ _ => rfl, Frame.refl _ _⟩

end VG.Proof.TripleDes.Arm

end

/-! ## `PassStart` -/

section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm

def startPointer (ptr : BitVec 32) (offset : Int) : BitVec 32 :=
  if offset < 0 then ptr - BitVec.ofNat 32 offset.natAbs else ptr + BitVec.ofNat 32 offset.natAbs

theorem passStart_ok (offset : Int) (s : State)
    (ho : encodable (BitVec.ofNat 32 offset.natAbs) = true) :
    ∃ s', runBlock isa (passStart offset) s = some s' ∧
      s'.gpr .r0 = startPointer (s.gpr .r0) offset ∧ s'.gpr .r9 = 16 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r0 → r ≠ .r9 → s'.gpr r = s.gpr r) := by
  by_cases h : offset < 0
  all_goals refine ⟨(s.setReg .r0 (startPointer (s.gpr .r0) offset)).setReg .r9 16, by
    simp only [passStart, h, ite_true, ite_false, runBlock_cons, exec, Op2.eval, ho, ite_true,
      Option.map_some, imm, runStep_some, startPointer]
    rfl, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  all_goals try simp only [gpr_setReg, startPointer, h, ite_true, ite_false, reduceCtorEq]
  all_goals try rfl
  all_goals
    intro r hr₀ hr₉
    simp only [hr₀, hr₉, ite_false]
end VG.Proof.TripleDes.Arm

end

/-! ## `Pass` -/

section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix)

structure PassPost (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .r10 = (roundPrefix keys direction 16 v).2
  right : s.gpr .r11 = (roundPrefix keys direction 16 v).1
  pointer : s.gpr .r0 = endPointer base direction
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

/-- The sixteen-round loop and final DES half swap. -/
theorem roundsWithSwap_ok (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .r10 = v.1) (hr : origin.gpr .r11 = v.2)
    (hptr : origin.gpr .r0 = keyAddr base direction 0)
    (hcount : origin.gpr .r9 = BitVec.ofNat 32 16)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base direction j) t, 4⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (readKey origin.mem (keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j) :
    WP isa (.seq (.loop (.block (roundBody ++ roundAdvance direction)) .ne)
      (.block swapHalves)) origin (PassPost keys direction base origin v) := by
  apply WP.seq
  apply WP.mono (roundsLoop_ok keys direction base origin v hok hl hr hptr hcount
    hread hsep hkeys)
  intro s hs
  obtain ⟨s', run, left, right, rd, wr, sp, mem, regs⟩ := swapHalves_ok s
  apply WP.of_runBlock
  refine ⟨s', run, left.trans hs.right, right.trans hs.left, (regs .r0 (by decide)).trans hs.pointer,
    rd.trans hs.rd, wr.trans hs.wr, sp.trans hs.sp, ?_, ?_⟩
  · intro q hq
    obtain hkeep : ∀ r ∈ roundStepKept, r ∈ roundOuterKept := by decide
    exact (regs q (hkeep q hq)).trans (hs.regs q hq)
  · rw [mem]
    exact hs.frame


theorem pass_ok (offset : Int) (ho : encodable (BitVec.ofNat 32 offset.natAbs) = true)
    (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .r10 = v.1) (hr : origin.gpr .r11 = v.2)
    (hptr : startPointer (origin.gpr .r0) offset =
      keyAddr base direction 0)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base direction j) t, 4⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (readKey origin.mem (keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j) :
    WP isa (pass offset direction) origin (PassPost keys direction base origin v) := by
  obtain ⟨s, run, ptr, count, mem, rd, wr, sp, regs⟩ := passStart_ok offset origin ho
  obtain hbase : s.gpr .r2 = origin.gpr .r2 := regs .r2 (by decide) (by decide)
  obtain hwork : spillRegion s = spillRegion origin := by simp only [spillRegion, hbase]
  obtain hkeysS : ∀ j < 16, (readKey s.mem (keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j := by rw [mem]; exact hkeys
  obtain hreadS : ∀ j < 16, ∀ t < 2, InRegions (s.rd ++ s.wr) (wordAddr (keyAddr base direction j) t) 4 := by
    rw [rd, wr]; exact hread
  obtain hsepS : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base direction j) t, 4⟩ : Region).Disjoint (spillRegion s) := by
    rw [hwork]; exact hsep
  obtain htail := roundsWithSwap_ok keys direction base s v
    (hok.congr hbase hbase rd wr)
    ((regs .r10 (by decide) (by decide)).trans hl)
    ((regs .r11 (by decide) (by decide)).trans hr)
    (ptr.trans hptr) count hreadS hsepS hkeysS
  apply WP.seq
  apply WP.of_runBlock
  refine ⟨s, run, WP.mono htail ?_⟩
  intro s' hs
  refine ⟨hs.left, hs.right, hs.pointer, hs.rd.trans rd, hs.wr.trans wr, hs.sp.trans sp, ?_, ?_⟩
  · intro q hq
    obtain hneq : ∀ r ∈ roundStepKept, r ≠ .r9 ∧ r ≠ .r0 := by decide
    exact (hs.regs q hq).trans (regs q (hneq q hq).2 (hneq q hq).1)
  · have hf := hs.frame
    rw [hwork, mem] at hf
    exact hf

end VG.Proof.TripleDes.Arm

end

/-! ## `WordState` -/

section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Proof.TripleDes (desCore roundPrefix)

/-- A DES word held as two 32-bit Feistel registers. -/
structure WordState (x : BitVec 64) (s : State) : Prop where
  left : s.gpr .r10 = ((x >>> 32).setWidth 32)
  right : s.gpr .r11 = (x.setWidth 32)

theorem PassPost.wordState {keys : Spec.TripleDes.DesSchedule}
    {direction : Spec.TripleDes.Direction} {base : BitVec 32} {origin s : State} {x : BitVec 64}
    (hs : PassPost keys direction base origin ((x >>> 32).setWidth 32, x.setWidth 32) s) :
    WordState (desCore keys direction x) s := by
  obtain hcore := VG.Proof.TripleDes.desCore_roundPrefix keys direction x
  let halves := roundPrefix keys direction 16 ((x >>> 32).setWidth 32, x.setWidth 32)
  obtain hleft : ((desCore keys direction x >>> 32).setWidth 32) = halves.2 :=
    (congrArg (fun v : BitVec 64 => ((v >>> 32).setWidth 32)) hcore).trans
      (VG.Proof.TripleDes.appended_left halves.2 halves.1)
  obtain hright : ((desCore keys direction x).setWidth 32) = halves.1 :=
    (congrArg (fun v : BitVec 64 => (v.setWidth 32)) hcore).trans
      (VG.Proof.TripleDes.appended_right halves.2 halves.1)
  exact ⟨hs.left.trans hleft.symm, hs.right.trans hright.symm⟩

end VG.Proof.TripleDes.Arm

end

/-! ## `Ready` -/

section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def componentBase (base : BitVec 32) (component : Nat) : BitVec 32 :=
  base + BitVec.ofNat 32 (128 * component)

structure Ready (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) : Prop where
  spills : Ok sboxCfg s
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    InRegions (s.rd ++ s.wr) (wordAddr (keyAddr (componentBase base c) d j) t) 4
  separate : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    (⟨wordAddr (keyAddr (componentBase base c) d j) t, 4⟩ : Region).Disjoint (spillRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (readKey s.mem (keyAddr (componentBase base c) d j)).setWidth 48 = roundKey (keys c) d j

theorem Ready.congr {keys : Nat → DesSchedule} {base : BitVec 32} {s t : State}
    (hs : Ready keys base s) (hbase : t.gpr .r2 = s.gpr .r2)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : Frame [spillRegion s] s.mem t.mem) : Ready keys base t := by
  obtain hwork : spillRegion t = spillRegion s :=
    congrArg (fun p => (⟨State.addr p + BitVec.ofNat 64 60, 388⟩ : Region)) hbase
  refine ⟨hs.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_⟩
  · rw [hrd, hwr]; exact hs.read
  · rw [hwork]; exact hs.separate
  · intro c hc d j hj
    obtain hmem := readKey_frame hf (ptr := keyAddr (componentBase base c) d j)
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hs.separate c hc d j hj t ht)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hs.values c hc d j hj)

structure Stable (origin s : State) : Prop where
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

theorem Stable.trans {s t u : State} (hs : Stable s t) (ht : Stable t u) : Stable s u := by
  obtain hwork : spillRegion t = spillRegion s :=
    congrArg (fun p => (⟨State.addr p + BitVec.ofNat 64 60, 388⟩ : Region)) (hs.regs .r2 (by decide))
  have hf := ht.frame
  rw [hwork] at hf
  exact ⟨ht.rd.trans hs.rd, ht.wr.trans hs.wr, ht.sp.trans hs.sp,
    fun q hq => (ht.regs q hq).trans (hs.regs q hq), hs.frame.trans hf⟩

theorem pass_word_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (c : Nat) (hc : c < 3) (d : Direction) (offset : Int)
    (ho : encodable (BitVec.ofNat 32 offset.natAbs) = true)
    (hptr : startPointer (s.gpr .r0) offset = keyAddr (componentBase base c) d 0)
    (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (pass offset d) s (fun t => WordState (VG.Proof.TripleDes.desCore (keys c) d x) t ∧
      Ready keys base t ∧ Stable s t ∧ t.gpr .r0 = endPointer (componentBase base c) d) := by
  apply WP.mono (pass_ok offset ho (keys c) d (componentBase base c) s
    ((x >>> 32).setWidth 32, x.setWidth 32) hready.spills hword.left hword.right
    hptr (hready.read c hc d) (hready.separate c hc d) (hready.values c hc d))
  intro t ht
  exact ⟨ht.wordState, hready.congr (ht.regs .r2 (by decide)) ht.rd ht.wr ht.frame,
    ⟨ht.rd, ht.wr, ht.sp, ht.regs, ht.frame⟩, ht.pointer⟩

end VG.Proof.TripleDes.Arm

end

/-! ## `Body` -/

section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (desCore)

theorem threePasses_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (c₀ c₁ c₂ : Nat) (h₀ : c₀ < 3) (h₁ : c₁ < 3) (h₂ : c₂ < 3)
    (d₀ d₁ d₂ : Direction) (o₀ o₁ o₂ : Int)
    (e₀ : encodable (BitVec.ofNat 32 o₀.natAbs) = true)
    (e₁ : encodable (BitVec.ofNat 32 o₁.natAbs) = true)
    (e₂ : encodable (BitVec.ofNat 32 o₂.natAbs) = true)
    (p₀ : startPointer (s.gpr .r0) o₀ = keyAddr (componentBase base c₀) d₀ 0)
    (p₁ : startPointer (endPointer (componentBase base c₀) d₀) o₁ = keyAddr (componentBase base c₁) d₁ 0)
    (p₂ : startPointer (endPointer (componentBase base c₁) d₁) o₂ = keyAddr (componentBase base c₂) d₂ 0)
    (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (.seq (pass o₀ d₀) (.seq (pass o₁ d₁) (pass o₂ d₂))) s
      (fun t => WordState (desCore (keys c₂) d₂ (desCore (keys c₁) d₁ (desCore (keys c₀) d₀ x))) t ∧
        Ready keys base t ∧ Stable s t ∧ t.gpr .r0 = endPointer (componentBase base c₂) d₂) := by
  apply WP.seq
  apply WP.mono (pass_word_ok keys base s x c₀ h₀ d₀ o₀ e₀ p₀ hready hword)
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (pass_word_ok keys base s₁ _ c₁ h₁ d₁ o₁ e₁
    (by rw [hs₁.2.2.2]; exact p₁) hs₁.2.1 hs₁.1)
  intro s₂ hs₂
  apply WP.mono (pass_word_ok keys base s₂ _ c₂ h₂ d₂ o₂ e₂
    (by rw [hs₂.2.2.2]; exact p₂) hs₂.2.1 hs₂.1)
  intro s₃ hs₃
  exact ⟨hs₃.1, hs₃.2.1,
    hs₁.2.2.1.trans (hs₂.2.2.1.trans hs₃.2.2.1), hs₃.2.2.2⟩

theorem passPointers (base : BitVec 32) :
    startPointer base 0 = keyAddr (componentBase base 0) .encrypt 0 ∧
    startPointer (endPointer (componentBase base 0) .encrypt) 120 = keyAddr (componentBase base 1) .decrypt 0 ∧
    startPointer (endPointer (componentBase base 1) .decrypt) 136 = keyAddr (componentBase base 2) .encrypt 0 ∧
    startPointer base 376 = keyAddr (componentBase base 2) .decrypt 0 ∧
    startPointer (endPointer (componentBase base 2) .decrypt) (-120) = keyAddr (componentBase base 1) .encrypt 0 ∧
    startPointer (endPointer (componentBase base 1) .encrypt) (-136) = keyAddr (componentBase base 0) .decrypt 0 := by
  simp only [startPointer, endPointer, componentBase, keyAddr,
    Int.reduceLT, Int.natAbs_neg, ite_true, ite_false, reduceCtorEq,
    Nat.reduceMul, Nat.reduceSub]
  repeat' constructor <;> bv_omega

def blockCore (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) : BitVec 64 :=
  match direction with
  | .encrypt => desCore (keys 2) .encrypt (desCore (keys 1) .decrypt (desCore (keys 0) .encrypt x))
  | .decrypt => desCore (keys 0) .decrypt (desCore (keys 1) .encrypt (desCore (keys 2) .decrypt x))

theorem blockBody_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (direction : Direction) (hptr : s.gpr .r0 = base)
    (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (blockBody direction) s
      (fun t => WordState (blockCore keys direction x) t ∧ Ready keys base t ∧ Stable s t ∧
        t.gpr .r0 = (if direction = .encrypt then base + 384 else base - 8)) := by
  obtain ⟨p₀, p₁, p₂, p₃, p₄, p₅⟩ := passPointers base
  cases direction
  · apply WP.mono (threePasses_ok keys base s x 0 1 2 (by decide) (by decide) (by decide)
      .encrypt .decrypt .encrypt 0 120 136 (by decide) (by decide) (by decide)
      (by rw [hptr]; exact p₀) p₁ p₂ hready hword)
    intro t ht
    refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_⟩
    rw [ht.2.2.2]
    change base + BitVec.ofNat 32 256 + BitVec.ofNat 32 128 = base + BitVec.ofNat 32 384
    rw [Offset.add_ofNat_add_ofNat]
  · apply WP.mono (threePasses_ok keys base s x 2 1 0 (by decide) (by decide) (by decide)
      .decrypt .encrypt .decrypt 376 (-120) (-136) (by decide) (by decide) (by decide)
      (by rw [hptr]; exact p₃) p₄ p₅ hready hword)
    intro t ht
    refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_⟩
    rw [ht.2.2.2]
    change (base + 0) - 8 = base - 8
    exact congrArg (· - (8 : BitVec 32)) (BitVec.add_zero base)
end VG.Proof.TripleDes.Arm

end

end

end


/-! ## `BlockIO` -/

@[expose] public section

section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm

def loadKept : List Reg := [.r0, .r1, .r2, .r3]

theorem readDataWords_ok (s : State) (offset : Nat) (ho : offset + 4 < 4096)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r1 + BitVec.ofNat 32 (offset + 4 * t))) 4) :
    ∃ s', runBlock isa [.ldr .r4 .r1 offset, .ldr .r5 .r1 (offset + 4),
        .rev .r4 .r4, .rev .r5 .r5] s = some s' ∧
      s'.gpr .r4 = rev (s.mem.readW (State.addr (s.gpr .r1 + BitVec.ofNat 32 offset)) 32) ∧
      s'.gpr .r5 = rev (s.mem.readW (State.addr (s.gpr .r1 + BitVec.ofNat 32 (offset + 4))) 32) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r) := by
  obtain h0 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 offset)) 4 := by
    simpa only [Nat.mul_zero, Nat.add_zero] using hr 0 (by decide)
  obtain h1 : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (offset + 4))) 4 := by
    simpa only [Nat.mul_one] using hr 1 (by decide)
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show offset < 4096 from by omega_using [ho], h0, show offset + 4 < 4096 from ho, ite_true, State.load32,
      gpr_setReg, reduceCtorEq, ite_false, rd_setReg, wr_setReg, h1,
      Option.map_some, mem_setReg, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · simp only [sp_setReg]
  · intro r h4 h5; simp only [gpr_setReg, h4, h5, ite_false]


theorem blockLoad_ok (s : State)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (hread : ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4) :
    ∃ s', runBlock isa blockLoad s = some s' ∧
      s'.gpr .r10 = ((Spec.TripleDes.permute Spec.TripleDes.ip
        (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1))))) >>> 32).setWidth 32 ∧
      s'.gpr .r11 = (Spec.TripleDes.permute Spec.TripleDes.ip
        (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1))))).setWidth 32 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r ∈ loadKept, s'.gpr r = s.gpr r) := by
  obtain ⟨s₁, run₁, hi₁, lo₁, mem₁, rd₁, wr₁, sp₁, reg₁⟩ := readDataWords_ok s 0 (by decide)
    (by simpa only [Nat.zero_add] using hread)
  obtain ⟨s₂, run₂, lo₂, hi₂, rd₂, wr₂, sp₂, mem₂, reg₂⟩ := initial_raw_ok s₁
  obtain input : s₁.gpr .r4 ++ s₁.gpr .r5 =
      Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1))) := by
    rw [hi₁, lo₁, decodeBlock_readW]
    simp only [BitVec.add_zero, Nat.zero_add]
    rw [addr_add (by omega_using [fit])]
    rfl
  rw [input] at lo₂ hi₂
  refine ⟨s₂, ?_, hi₂, lo₂, mem₂.trans mem₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_, ?_⟩
  · rw [blockLoad, runBoxes_append, run₁, Option.bind_some, run₂]
  · exact sp₂.trans sp₁
  · intro r hr
    obtain checks : ∀ r ∈ loadKept,
        ((instrs initialPermutation.lit).all fun op => !clobbers op r) = true := by decide +kernel
    obtain unused : ∀ r ∈ loadKept, r ≠ .r4 ∧ r ≠ .r5 := by decide
    exact (reg₂ r (checks r hr)).trans (reg₁ r (unused r hr).1 (unused r hr).2)

end VG.Proof.TripleDes.Arm

end

/-! ## `Save` -/

section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (slotsOf)

theorem blockSave_eq : blockSave = (slotsOf savedRegs).map (fun p => Instr.str p.1 .r2 p.2) := by
  rw [blockSave, slotsOf, List.map_map]; rfl

theorem blockRestore_eq : blockRestore = (slotsOf savedRegs).map (fun p => Instr.ldr p.1 .r2 p.2) := by
  rw [blockRestore, slotsOf, List.map_map]; rfl

theorem slots_ok : Spill.Slots 0 36 (slotsOf savedRegs) := by decide

theorem slot_index : ∀ p ∈ slotsOf savedRegs, ∃ i < 9, p.2 = 4 * i := by decide

def Saved (original current : State) : Prop :=
  Spill.Saved current.mem (State.addr (current.gpr .r2)) original.gpr (slotsOf savedRegs)

structure SavePost (original current : State) : Prop where
  gpr : current.gpr = original.gpr
  rd : current.rd = original.rd
  wr : current.wr = original.wr
  sp : current.sp = original.sp
  saved : Saved original current
  frame : Frame [⟨State.addr (original.gpr .r2), 36⟩] original.mem current.mem

theorem blockSave_ok (s : State)
    (fit : (s.gpr .r2).toNat + 256 ≤ 2 ^ 32)
    (hw : ∀ i < 9, InRegions s.wr (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block blockSave) s (SavePost s) := by
  rw [blockSave_eq, ← List.append_nil (List.map _ _)]
  refine Spill.save_ok _ s _ (fun p hp => ?_) (WP.block_nil ⟨rfl, rfl, rfl, rfl,
    Spill.saveMem_saved _ _ _ _ slots_ok, Spill.saveMem_frame _ _ _ (by decide) _ (by decide)⟩)
  obtain ⟨i, hi, he⟩ := slot_index p hp
  exact ⟨by omega_using [hi, he], by omega_using [fit, hi, he], he ▸ hw i hi⟩

structure RestorePost (original origin current : State) : Prop where
  saved : ∀ r ∈ savedRegs, current.gpr r = original.gpr r
  keep : VG.Proof.Rc2.Arm.Keep savedRegs origin current
  sp : current.sp = origin.sp

theorem blockRestore_ok (original s : State) (hsaved : Saved original s)
    (fit : (s.gpr .r2).toNat + 256 ≤ 2 ^ 32)
    (hread : ∀ i < 9, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block blockRestore) s (RestorePost original s) := by
  rw [blockRestore_eq, ← List.append_nil (List.map _ _)]
  obtain hregs : (slotsOf savedRegs).map Prod.fst = savedRegs := by decide
  refine Spill.restoreList_ok _ s _ (by decide) (fun p hp => ?_)
    fun s' hl ho hm hrd hwr hsp => WP.block_nil ⟨?_, ⟨fun r hr => ho r (hregs ▸ hr), hm, hrd, hwr⟩, hsp⟩
  · obtain ⟨i, hi, he⟩ := slot_index p hp
    obtain hne : ∀ p ∈ slotsOf savedRegs, p.1 ≠ .r2 := by decide
    exact ⟨hne p hp, by omega_using [hi, he], by omega_using [fit, hi, he], he ▸ hread i hi⟩
  · exact Spill.restored_of (hsaved.restored hl) fun r hr => hregs ▸ hr

theorem Saved.congr {original s t : State} (hs : Saved original s)
    (hbase : t.gpr .r2 = s.gpr .r2) (hf : Frame [spillRegion s] s.mem t.mem) :
    Saved original t := by
  unfold Saved; rw [hbase]
  exact Spill.Saved.frame hs slots_ok hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)

end VG.Proof.TripleDes.Arm

end

/-! ## `Head` -/

section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def saveRegion (s : State) : Region := ⟨State.addr (s.gpr .r2), 36⟩

structure HeadPre (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) : Prop where
  spills : Ok sboxCfg s
  scratchFit : (s.gpr .r2).toNat + 256 ≤ 2 ^ 32
  dataFit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32
  pointer : s.gpr .r0 = base
  saveRead : ∀ i < 9, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4
  saveWrite : ∀ i < 9, InRegions s.wr (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4
  dataRead : ∀ t < 2, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4
  dataSeparate : (⟨State.addr (s.gpr .r1), 8⟩ : Region).Disjoint (saveRegion s)
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    InRegions (s.rd ++ s.wr) (wordAddr (keyAddr (componentBase base c) d j) t) 4
  separateWork : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    (⟨wordAddr (keyAddr (componentBase base c) d j) t, 4⟩ : Region).Disjoint (spillRegion s)
  separateSave : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    (⟨wordAddr (keyAddr (componentBase base c) d j) t, 4⟩ : Region).Disjoint (saveRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (readKey s.mem (keyAddr (componentBase base c) d j)).setWidth 48 = roundKey (keys c) d j

structure HeadPost (keys : Nat → DesSchedule) (base : BitVec 32) (original s : State) : Prop where
  word : WordState (Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt original.mem (State.addr (original.gpr .r1))))) s
  ready : Ready keys base s
  saved : Saved original s
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.sp = original.sp
  regs : ∀ q ∈ loadKept, s.gpr q = original.gpr q
  frame : Frame [saveRegion original] original.mem s.mem

theorem ready_afterSave {keys : Nat → DesSchedule} {base : BitVec 32} {s t : State}
    (hp : HeadPre keys base s) (hg : t.gpr = s.gpr) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hf : Frame [saveRegion s] s.mem t.mem) : Ready keys base t := by
  obtain hbase : t.gpr .r2 = s.gpr .r2 := congrFun hg .r2
  refine ⟨hp.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_⟩
  · rw [hrd, hwr]; exact hp.read
  · rw [show spillRegion t = spillRegion s from
      congrArg (fun p => (⟨State.addr p + BitVec.ofNat 64 60, 388⟩ : Region)) hbase]
    exact hp.separateWork
  · intro c hc d j hj
    obtain hm := readKey_frame hf (ptr := keyAddr (componentBase base c) d j)
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.separateSave c hc d j hj t ht)
    exact (congrArg (BitVec.setWidth 48) hm).trans (hp.values c hc d j hj)

theorem blockHead_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State)
    (hp : HeadPre keys base s) : WP isa (.block (blockSave ++ blockLoad)) s (HeadPost keys base s) := by
  apply WP.block_append
  apply WP.mono (blockSave_ok s hp.scratchFit hp.saveWrite)
  intro s₁ hs₁
  obtain hready := ready_afterSave hp hs₁.gpr hs₁.rd hs₁.wr hs₁.frame
  obtain hread₁ : ∀ t < 2, InRegions (s₁.rd ++ s₁.wr)
      (State.addr (s₁.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4 := by
    rw [hs₁.rd, hs₁.wr, hs₁.gpr]; exact hp.dataRead
  obtain hdata : Spec.TripleDes.blockAt s₁.mem (State.addr (s₁.gpr .r1)) =
      Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1)) := by
    rw [hs₁.gpr]
    exact VG.Proof.TripleDes.blockAt_eq_of_frame _ hs₁.frame
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.dataSeparate)
  obtain ⟨s₂, run₂, left₂, right₂, mem₂, rd₂, wr₂, sp₂, regs₂⟩ :=
    blockLoad_ok s₁ (by rw [hs₁.gpr]; exact hp.dataFit) hread₁
  obtain hframe : Frame [spillRegion s₁] s₁.mem s₂.mem := by
    rw [mem₂]; exact Frame.refl _ _
  obtain hinput := congrArg (fun b => Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock b)) hdata
  apply WP.of_runBlock
  refine ⟨s₂, run₂, ?_, hready.congr (regs₂ .r2 (by decide)) rd₂ wr₂ hframe,
    hs₁.saved.congr (regs₂ .r2 (by decide)) hframe,
    rd₂.trans hs₁.rd, wr₂.trans hs₁.wr, sp₂.trans hs₁.sp, ?_, ?_⟩
  · exact ⟨left₂.trans (congrArg (fun x : BitVec 64 => (x >>> 32).setWidth 32) hinput),
      right₂.trans (congrArg (fun x : BitVec 64 => x.setWidth 32) hinput)⟩
  · intro q hq
    exact (regs₂ q hq).trans (congrFun hs₁.gpr q)
  · rw [mem₂]; exact hs₁.frame

end VG.Proof.TripleDes.Arm

end

end

end


/-! ## `Store` -/

@[expose] public section

section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction)

def storeTail (d : Direction) : List Instr :=
  [.rev .r4 .r4, .rev .r5 .r5, .str .r4 .r1 0, .str .r5 .r1 4,
    .dp (if d = .encrypt then .sub else .add) .r0 .r0
      (.imm (if d = .encrypt then 384 else 8))]

theorem storeTail_ok (d : Direction) (s : State)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (hw : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4) :
    ∃ s', runBlock isa (storeTail d) s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (s.gpr .r1))
        (byteRev64 (s.gpr .r4 ++ s.gpr .r5)) ∧
      s'.gpr .r0 = (if d = .encrypt then s.gpr .r0 - 384 else s.gpr .r0 + 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r0 → r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r) := by
  obtain h0 : InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 0)) 4 := by
    simpa only [Nat.mul_zero] using hw 0 (by decide)
  obtain h1 : InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 4)) 4 := by
    simpa only [Nat.mul_one] using hw 1 (by decide)
  cases d <;> refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, storeTail, 
      runBlock_cons, runStep_some, exec, State.store32, h0, h1,
      Op2.eval, gpr_setReg, mem_setReg, wr_setReg]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false,
    rd_setReg, wr_setReg, sp_setReg]
  all_goals try
    simp only [mem_setReg, BitVec.add_zero]
    rw [addr_add (by omega_using [fit])]
    exact (writeW_pair s.mem _ _ _).trans (congrArg (s.mem.writeW _) (revPair _ _))
  all_goals
    intro r h0 h4 h5
    simp only [h0, h4, h5, ite_false]

theorem blockStore_ok (d : Direction) (s : State) (l r : BitVec 32)
    (hl : s.gpr .r10 = l) (hr : s.gpr .r11 = r)
    (fit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (hw : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4) :
    ∃ s', runBlock isa (blockStore d) s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (s.gpr .r1))
        (byteRev64 (Spec.TripleDes.permute Spec.TripleDes.fp (l ++ r))) ∧
      s'.gpr .r0 = (if d = .encrypt then s.gpr .r0 - 384 else s.gpr .r0 + 8) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ loadKept, q ≠ .r0 → s'.gpr q = s.gpr q) := by
  obtain ⟨s₁, run₁, lo₁, hi₁, rd₁, wr₁, sp₁, mem₁, reg₁⟩ := final_raw_ok s
  rw [hl, hr] at lo₁ hi₁
  obtain keeps : ∀ q ∈ loadKept, s₁.gpr q = s.gpr q := by
    intro q hq
    obtain checks : ∀ q ∈ loadKept,
        ((instrs finalPermutation.lit).all fun op => !clobbers op q) = true := by decide +kernel
    exact reg₁ q (checks q hq)
  obtain fit₁ : (s₁.gpr .r1).toNat + 8 ≤ 2 ^ 32 := by rw [keeps .r1 (by decide)]; exact fit
  obtain hw₁ : ∀ t < 2, InRegions s₁.wr (State.addr (s₁.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4 := by
    rw [wr₁, keeps .r1 (by decide)]; exact hw
  obtain ⟨s₂, run₂, mem₂, ptr₂, rd₂, wr₂, sp₂, reg₂⟩ := storeTail_ok d s₁ fit₁ hw₁
  refine ⟨s₂, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_⟩
  · rw [blockStore, ← storeTail, runBoxes_append, run₁, Option.bind_some, run₂]
  · rw [mem₂, mem₁, keeps .r1 (by decide), hi₁, lo₁, VG.Proof.TripleDes.halves_append]
  · rw [ptr₂, keeps .r0 (by decide)]
  · intro q hq h0
    obtain unused : ∀ q ∈ loadKept, q ≠ .r4 ∧ q ≠ .r5 := by decide
    exact (reg₂ q h0 (unused q hq).1 (unused q hq).2).trans (keeps q hq)

end VG.Proof.TripleDes.Arm

end

/-! ## `Tail` -/

section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction)

structure TailPost (original origin : State) (d : Direction) (x : BitVec 64) (s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (State.addr (origin.gpr .r1)) =
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp x)
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  pointer : s.gpr .r0 = (if d = .encrypt then origin.gpr .r0 - 384 else origin.gpr .r0 + 8)
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [⟨State.addr (origin.gpr .r1), 8⟩] origin.mem s.mem

theorem blockTail_ok (original s : State) (d : Direction) (x : BitVec 64)
    (hword : WordState x s) (hsaved : Saved original s)
    (scratchFit : (s.gpr .r2).toNat + 256 ≤ 2 ^ 32)
    (dataFit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32)
    (hsavedRead : ∀ i < 9, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4)
    (hwrite : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4)
    (hsep : (⟨State.addr (s.gpr .r1), 8⟩ : Region).Disjoint (saveRegion s)) :
    WP isa (.block (blockStore d ++ blockRestore)) s (TailPost original s d x) := by
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, mem₁, ptr₁, rd₁, wr₁, sp₁, reg₁⟩ := blockStore_ok d s
    ((x >>> 32).setWidth 32) (x.setWidth 32) hword.left hword.right dataFit hwrite
  rw [VG.Proof.TripleDes.halves_append] at mem₁
  obtain regs₁ : ∀ q ∈ roundStepKept, s₁.gpr q = s.gpr q := by
    intro q hq
    obtain incl : ∀ q ∈ roundStepKept, q ∈ loadKept ∧ q ≠ .r0 := by decide
    exact reg₁ q (incl q hq).1 (incl q hq).2
  obtain frame₁ : Frame [⟨State.addr (s.gpr .r1), 8⟩] s.mem s₁.mem := by
    rw [mem₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain saved₁ : Saved original s₁ := by
    unfold Saved; rw [regs₁ .r2 (by decide)]
    exact Spill.Saved.frame hsaved slots_ok frame₁ fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hsep.sub_right (Offset.sub_base _ (by decide))).symm
  obtain reads₁ : ∀ i < 9, InRegions (s₁.rd ++ s₁.wr)
      (State.addr (s₁.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [rd₁, wr₁, regs₁ .r2 (by decide)]; exact hsavedRead
  apply WP.of_runBlock
  refine ⟨s₁, run₁, ?_⟩
  apply WP.mono (blockRestore_ok original s₁ saved₁
    (by rw [regs₁ .r2 (by decide)]; exact scratchFit) reads₁)
  intro s₂ hs₂
  refine ⟨?_, hs₂.saved, ?_, hs₂.keep.rd.trans rd₁, hs₂.keep.wr.trans wr₁,
    hs₂.sp.trans sp₁, ?_, ?_⟩
  · rw [hs₂.keep.mem, mem₁]
    exact blockAt_writeW s.mem _ _
  · exact (hs₂.keep.reg .r0 (by decide)).trans ptr₁
  · intro q hq
    obtain unused : ∀ q ∈ roundStepKept, q ∉ savedRegs := by decide
    exact (hs₂.keep.reg q (unused q hq)).trans (regs₁ q hq)
  · rw [hs₂.keep.mem]; exact frame₁

end VG.Proof.TripleDes.Arm

end

/-! ## `Block` -/

section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction Schedule)

def blockResult (keys : Schedule) (direction : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.Block :=
  match direction with
  | .encrypt => Spec.TripleDes.encryptBlock keys b
  | .decrypt => Spec.TripleDes.decryptBlock keys b

theorem blockResult_core (keys : Schedule) (direction : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp
      (blockCore (Spec.TripleDes.componentSchedule keys) direction
        (Spec.TripleDes.permute Spec.TripleDes.ip (Spec.TripleDes.decodeBlock b)))) =
      blockResult keys direction b := by
  cases direction
  · exact (VG.Proof.TripleDes.encryptBlock_eq_cores keys b).symm
  · exact (VG.Proof.TripleDes.decryptBlock_eq_cores keys b).symm

def blockRegions (s : State) : List Region := [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 512⟩]

structure BlockPost (keys : Schedule) (direction : Direction) (original s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (State.addr (original.gpr .r1)) =
    blockResult keys direction (Spec.TripleDes.blockAt original.mem (State.addr (original.gpr .r1)))
  pointer : s.gpr .r0 = original.gpr .r0
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.sp = original.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = original.gpr q
  frame : Frame (blockRegions original) original.mem s.mem

theorem block_ok (keys : Schedule) (base : BitVec 32) (direction : Direction) (s : State)
    (hp : HeadPre (Spec.TripleDes.componentSchedule keys) base s)
    (hwrite : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4) :
    WP isa (block direction) s (BlockPost keys direction s) := by
  apply WP.seq
  apply WP.mono (blockHead_ok (Spec.TripleDes.componentSchedule keys) base s hp)
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (blockBody_ok (Spec.TripleDes.componentSchedule keys) base s₁ _ direction ((hs₁.regs .r0 (by decide)).trans hp.pointer) hs₁.ready hs₁.word)
  intro s₂ hs₂
  obtain hregs₂ : ∀ q ∈ roundStepKept, s₂.gpr q = s.gpr q := by
    intro q hq
    obtain hkeep : ∀ r ∈ roundStepKept, r ∈ loadKept := by decide
    exact (hs₂.2.2.1.regs q hq).trans (hs₁.regs q (hkeep q hq))
  obtain saved₂ := hs₁.saved.congr (hs₂.2.2.1.regs .r2 (by decide)) hs₂.2.2.1.frame
  obtain savedRead₂ : ∀ i < 9, InRegions (s₂.rd ++ s₂.wr) (State.addr (s₂.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [hs₂.2.2.1.rd, hs₂.2.2.1.wr, hs₁.rd, hs₁.wr, hregs₂ .r2 (by decide)]
    exact hp.saveRead
  obtain hwrite₂ : ∀ t < 2, InRegions s₂.wr (State.addr (s₂.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4 := by
    rw [hs₂.2.2.1.wr, hs₁.wr, hregs₂ .r1 (by decide)]
    exact hwrite
  apply WP.mono (blockTail_ok s s₂ direction _ hs₂.1 saved₂
    (by rw [hregs₂ .r2 (by decide)]; exact hp.scratchFit)
    (by rw [hregs₂ .r1 (by decide)]; exact hp.dataFit) savedRead₂ hwrite₂
    (by rw [saveRegion, hregs₂ .r1 (by decide), hregs₂ .r2 (by decide)]; exact hp.dataSeparate))
  intro s₃ hs₃
  refine ⟨?_, ?_, hs₃.saved, hs₃.rd.trans (hs₂.2.2.1.rd.trans hs₁.rd),
    hs₃.wr.trans (hs₂.2.2.1.wr.trans hs₁.wr),
    hs₃.sp.trans (hs₂.2.2.1.sp.trans hs₁.sp),
    fun q hq => (hs₃.regs q hq).trans (hregs₂ q hq), ?_⟩
  · have hresult := hs₃.result
    rw [hregs₂ .r1 (by decide)] at hresult
    exact hresult.trans (blockResult_core keys direction _)
  · rw [hs₃.pointer, hs₂.2.2.2, hp.pointer]
    cases direction <;> simp only [reduceCtorEq, ite_true, ite_false,
      BitVec.add_sub_cancel, BitVec.sub_add_cancel]
  · have hf₁ : Frame (blockRegions s) s.mem s₁.mem := hs₁.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨State.addr (s.gpr .r2), 512⟩, by simp [blockRegions], Region.sub_prefix (by decide)⟩)
    obtain hf₂ : Frame (blockRegions s) s₁.mem s₂.mem := hs₂.2.2.1.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨⟨State.addr (s.gpr .r2), 512⟩, by simp [blockRegions], ?_⟩
      obtain hbase := hs₁.regs .r2 (by decide)
      change Region.Sub ⟨State.addr (s₁.gpr .r2) + BitVec.ofNat 64 60, 388⟩ ⟨State.addr (s.gpr .r2), 512⟩
      rw [hbase]
      exact Offset.sub_base _ (by decide))
    obtain hf₃ : Frame (blockRegions s) s₂.mem s₃.mem := hs₃.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      rw [hregs₂ .r1 (by decide)]
      exact ⟨⟨State.addr (s.gpr .r1), 8⟩, by simp [blockRegions], fun _ h => h⟩)
    exact hf₁.trans (hf₂.trans hf₃)

end VG.Proof.TripleDes.Arm

end

end

end


@[expose] public section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction)

def blockContract (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 384⟩
    let data : Region := ⟨State.addr (s.gpr .r1), 8⟩
    let scratch : Region := ⟨State.addr (s.gpr .r2), 512⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .r0).toNat + 384 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 8 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 512 ≤ 2 ^ 32
  post s s' := Spec.TripleDes.blockAt s'.mem (State.addr (s.gpr .r1)) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))) d (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1)))
  pub := PublicRegs [.r0, .r1, .r2]

def selectedRound (d : Direction) (j : Nat) : Nat := if d = .encrypt then j else 15 - j

theorem selectedRound_bound (d : Direction) (j : Nat) (hj : j < 16) : selectedRound d j < 16 := by
  cases d <;> simp only [selectedRound, reduceCtorEq, ite_true, ite_false] <;> omega_arith

theorem keyAddr_component (base : BitVec 32) (c : Nat) (d : Direction) (j : Nat) :
    keyAddr (componentBase base c) d j = base + BitVec.ofNat 32 (8 * (16 * c + selectedRound d j)) := by
  unfold keyAddr componentBase selectedRound
  rw [Offset.add_ofNat_add_ofNat]
  exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega_using [])

theorem keyWordAddress (base : BitVec 32) (fit : base.toNat + 384 ≤ 2 ^ 32)
    (c j t : Nat) (hc : c < 3) (hj : j < 16) (ht : t < 2) (d : Direction) :
    wordAddr (keyAddr (componentBase base c) d j) t =
      State.addr base + BitVec.ofNat 64 (8 * (16 * c + selectedRound d j) + 4 * t) := by
  obtain bound := selectedRound_bound d j hj
  rw [wordAddr, keyAddr_component, Offset.add_ofNat_add_ofNat,
    addr_add (by omega_using [fit, hc, bound, ht])]

theorem readKey_component (m : Mem) (base : BitVec 32)
    (fit : base.toNat + 384 ≤ 2 ^ 32) (c j : Nat) (hc : c < 3) (hj : j < 16) (d : Direction) :
    readKey m (keyAddr (componentBase base c) d j) =
      m.readW (State.addr base + BitVec.ofNat 64 (8 * (16 * c + selectedRound d j))) 64 := by
  rw [readKey, keyWordAddress base fit c j 1 hc hj (by decide) d,
    keyWordAddress base fit c j 0 hc hj (by decide) d]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  rw [← Offset.add_ofNat_add_ofNat]
  exact readW_pair m _

theorem headPre_of_contract (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))))
      (s.gpr .r0) s := by
  obtain ⟨hrd, hwr, keySep, dataSep, keyFit, dataFit, scratchFit⟩ := hs
  obtain scratchWrites : ∀ i < 128, InRegions s.wr (wordAddr (s.gpr .r2) i) 4 := by
    intro i hi
    rw [wordAddr, addr_add (by omega_using [scratchFit, hi]), hwr]
    exact ⟨⟨State.addr (s.gpr .r2), 512⟩, by simp,
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  obtain scratchSaveWrites : ∀ i < 9, InRegions s.wr (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨State.addr (s.gpr .r2), 512⟩, by simp,
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  obtain scratchSaveReads : ∀ i < 9, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    obtain ⟨r, hr, hc⟩ := scratchSaveWrites i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain spills : Ok sboxCfg s := by
    refine ⟨scratchWrites, ?_, scratchFit, ?_⟩
    · intro k hk; change k < 0 at hk; omega
    · intro k hk j hj; change j < 0 at hj; omega
  obtain keySub : ∀ c < 3, ∀ direction : Direction, ∀ j < 16, ∀ t < 2,
      Region.Sub ⟨wordAddr (keyAddr (componentBase (s.gpr .r0) c) direction j) t, 4⟩
        ⟨State.addr (s.gpr .r0), 384⟩ := by
    intro c hc direction j hj t ht
    rw [keyWordAddress _ keyFit c j t hc hj ht direction]
    obtain bound := selectedRound_bound direction j hj
    exact Offset.sub_base _ (by omega_using [hc, bound, ht])
  obtain workSub : Region.Sub (spillRegion s) ⟨State.addr (s.gpr .r2), 512⟩ :=
    Offset.sub_base _ (by decide)
  obtain saveSub : Region.Sub (saveRegion s) ⟨State.addr (s.gpr .r2), 512⟩ :=
    Region.sub_prefix (by decide)
  refine ⟨spills, by omega_using [scratchFit], dataFit, rfl, scratchSaveReads,
    scratchSaveWrites, ?_, dataSep.sub_right saveSub, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [addr_add (by omega_using [dataFit, ht]), hrd, hwr]
    exact ⟨⟨State.addr (s.gpr .r1), 8⟩, by simp,
      Offset.contains_base _ (by omega_using [ht]) (by omega_using [ht])⟩
  · intro c hc direction j hj t ht
    rw [keyWordAddress _ keyFit c j t hc hj ht direction, hrd, hwr]
    obtain bound := selectedRound_bound direction j hj
    exact ⟨⟨State.addr (s.gpr .r0), 384⟩, by simp,
      Offset.contains_base _ (by omega_using [hc, bound, ht]) (by omega_using [hc, bound, ht])⟩
  · intro c hc direction j hj t ht
    exact (keySep.sub_left (keySub c hc direction j hj t ht)).sub_right workSub
  · intro c hc direction j hj t ht
    exact (keySep.sub_left (keySub c hc direction j hj t ht)).sub_right saveSub
  · intro c hc direction j hj
    rw [readKey_component s.mem _ keyFit c j hc hj direction]
    exact (VG.Proof.TripleDes.componentSchedule_readW s.mem (State.addr (s.gpr .r0)) c
      (selectedRound direction j) hc (selectedRound_bound direction j hj)).symm

end VG.Proof.TripleDes.Arm

end

end


/-! ## `Call` -/

@[expose] public section

section

namespace VG.Proof.TripleDes.Arm.Ecb
open VG VG.Arm VG.Impl.TripleDes.Arm

def kept : List Reg := [.r0, .r1, .r2, .r3]
def savedAcrossCall : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

def callContract (d : Spec.TripleDes.Direction) : Contract isa :=
  { blockContract d with
    post := fun s s' => (blockContract d).post s s' ∧ ∀ r ∈ kept, s'.gpr r = s.gpr r }

theorem block_correct' (d : Spec.TripleDes.Direction) (s : State) (hs : (callContract d).pre s) :
    ∃ t s', Exec isa (block d) s t s' ∧ abiPreserved s s' ∧ (callContract d).post s s' := by
  obtain hp := headPre_of_contract d s hs
  obtain writes : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4 := by
    intro t ht
    have fit := hs.2.2.2.2.2.1
    rw [addr_add (by omega_using [fit, ht]), hs.2.1]
    exact ⟨⟨State.addr (s.gpr .r1), 8⟩, by simp,
      Offset.contains_base _ (by omega_using [ht]) (by omega_using [ht])⟩
  obtain ⟨t, s', he, post⟩ := block_ok (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0)))
    (s.gpr .r0) d s hp writes
  refine ⟨t, s', he, ⟨?_, post.sp⟩, post.result, ?_⟩
  · intro r hr
    obtain covered : ∀ r ∈ preserved, r ∈ savedRegs := by decide
    exact post.saved r (covered r hr)
  · intro r hr
    simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact post.pointer
    · exact post.regs .r1 (by decide)
    · exact post.regs .r2 (by decide)
    · exact post.regs .r3 (by decide)

theorem blockCall_eq (d : Spec.TripleDes.Direction) : Impl.TripleDes.Arm.Ecb.blockCall d =
    .call (match d with | .encrypt => "vg_triple_des_encrypt_block" | .decrypt => "vg_triple_des_decrypt_block")
      (block d) := by cases d <;> rfl

structure CallPre (s : State) : Prop where
  reads : Covers [⟨State.addr (s.gpr .r0), 384⟩, ⟨State.addr (s.gpr .r1), 8⟩,
    ⟨State.addr (s.gpr .r2), 512⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 512⟩] s.wr
  keyScratch : (Region.mk (State.addr (s.gpr .r0)) 384).Disjoint ⟨State.addr (s.gpr .r2), 512⟩
  dataScratch : (Region.mk (State.addr (s.gpr .r1)) 8).Disjoint ⟨State.addr (s.gpr .r2), 512⟩
  keyFit : (s.gpr .r0).toNat + 384 ≤ 2 ^ 32
  dataFit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32
  scratchFit : (s.gpr .r2).toNat + 512 ≤ 2 ^ 32

structure CallPost (d : Spec.TripleDes.Direction) (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 512⟩] s.mem s'.mem
  output : Spec.TripleDes.blockAt s'.mem (State.addr (s.gpr .r1)) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1)))

theorem call_ok (d : Spec.TripleDes.Direction) (s : State) (hp : CallPre s) :
    WP isa (Impl.TripleDes.Arm.Ecb.blockCall d) s (CallPost d s) := by
  rw [blockCall_eq]
  refine WP.call (k := callContract d) (block_correct' d)
    (rd := [⟨State.addr (s.gpr .r0), 384⟩])
    (wr := [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 512⟩])
    ?_ hp.reads hp.writes ?_ (by cases d <;> rfl)
  · simp only [callContract, blockContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs)]
    exact ⟨trivial, trivial, hp.keyScratch, hp.dataScratch, hp.keyFit, hp.dataFit, hp.scratchFit⟩
  · intro s' rd wr sp frame callee regs out
    obtain sep : ∀ r ∈ kept, r ∉ linkRegs := by decide
    obtain saved : ∀ r ∈ savedAcrossCall, r ∈ preserved ∧ r ≠ .lr := by decide
    refine ⟨?_, fun r hr => callee r (saved r hr).1 (saved r hr).2, rd, wr, frame, ?_⟩
    · intro r hr
      obtain h := out.2 r hr
      simp only [State.withRegions_gpr, State.callEntry_gpr _ (sep r hr)] at h
      exact h
    · have h := out.1
      change Spec.TripleDes.blockAt s'.mem _ = blockResult _ d _ at h
      simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
        State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs)] at h
      exact h

end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `Pre` -/

section

/-! # Permissions and separation for one ECB step -/

namespace VG.Proof.TripleDes.Arm.Ecb

open VG VG.Arm

abbrev keyR (s : State) : Region := ⟨State.addr (s.gpr .r0), 384⟩
abbrev dataR (s : State) (n : Nat := 1) : Region := ⟨State.addr (s.gpr .r1), 8 * n⟩
abbrev bufR (s : State) : Region := ⟨State.addr (s.gpr .r2), 1024⟩

structure StepPre (s : State) (n : Nat := 1) : Prop where
  reads : Covers [keyR s, dataR s n, bufR s] (s.rd ++ s.wr)
  writes : Covers [dataR s n, bufR s] s.wr
  keyData : (keyR s).Disjoint (dataR s n)
  keyBuf : (keyR s).Disjoint (bufR s)
  dataBuf : (dataR s n).Disjoint (bufR s)
  keyFit : (s.gpr .r0).toNat + 384 ≤ 2 ^ 32
  dataFit : (s.gpr .r1).toNat + 8 * n ≤ 2 ^ 32
  bufFit : (s.gpr .r2).toNat + 1024 ≤ 2 ^ 32

theorem StepPre.call {s : State} (hp : StepPre s) : CallPre s := by
  constructor
  · have hc : Covers [⟨State.addr (s.gpr .r0), 384⟩, ⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 512⟩]
        [keyR s, dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp, by simp⟩
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.reads a n (hc a n h)
  · have hc : Covers [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 512⟩] [dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.writes a n (hc a n h)
  · exact hp.keyBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.dataBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.keyFit
  · exact hp.dataFit
  · omega_using [hp.bufFit]


end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `Slice` -/

section

/-! # Restricting ECB permissions to a consecutive subrange -/

namespace VG.Proof.TripleDes.Arm.Ecb

open VG VG.Arm

theorem StepPre.slice {s s' : State} {n m i : Nat} (hp : StepPre s n) (bound : i + m ≤ n) (hm : 1 ≤ m)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (key : s'.gpr .r0 = s.gpr .r0)
    (buf : s'.gpr .r2 = s.gpr .r2)
    (ptr : s'.gpr .r1 = s.gpr .r1 + BitVec.ofNat 32 (8 * i)) : StepPre s' m := by
  obtain fit : (s.gpr .r1).toNat + 8 * i < 2 ^ 32 := by omega_using [hp.dataFit, bound, hm]
  obtain ptrAddr : State.addr (s'.gpr .r1) = State.addr (s.gpr .r1) + BitVec.ofNat 64 (8 * i) := by
    rw [ptr, addr_add fit]
  obtain sub : Region.Sub (dataR s' m) (dataR s n) := by
    change Region.Sub ⟨State.addr (s'.gpr .r1), 8 * m⟩ ⟨State.addr (s.gpr .r1), 8 * n⟩
    rw [ptrAddr]
    exact Offset.sub_base _ (by omega_using [bound])
  constructor
  · have hc : Covers [keyR s', dataR s' m, bufR s'] [keyR s, dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp [key], by simp⟩
      · exact ⟨dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega_using [bound]⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [rd, wr]
    exact fun a k h => hp.reads a k (hc a k h)
  · have hc : Covers [dataR s' m, bufR s'] [dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega_using [bound]⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [wr]
    exact fun a k h => hp.writes a k (hc a k h)
  · simpa only [keyR, key] using hp.keyData.sub_right sub
  · simpa only [keyR, bufR, key, buf] using hp.keyBuf
  · simpa only [bufR, buf] using hp.dataBuf.sub_left sub
  · rw [key]; exact hp.keyFit
  · rw [ptr]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [fit] : 8 * i < 2 ^ 32), Nat.mod_eq_of_lt fit]
    omega_using [hp.dataFit, bound]
  · rw [buf]; exact hp.bufFit

theorem StepPre.head {s : State} {n : Nat} (hp : StepPre s n) (hn : 1 ≤ n) : StepPre s :=
  hp.slice (i := 0) hn (by decide) rfl rfl rfl rfl (by simp)

end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `Steps` -/

section

namespace VG.Proof.TripleDes.Arm.Ecb
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (Keep gpr_subFlags mem_subFlags rd_subFlags wr_subFlags)

def zeroCount (s : State) : Option Bool := some s.z

theorem eval_zeroCount (s : State) : eval .eq s = zeroCount s := rfl
theorem eval_nonzeroCount (s : State) : eval .ne s = (zeroCount s).map (! ·) := rfl

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.TripleDes.Arm.Ecb.advance s = some s' ∧
      s'.gpr .r1 = s.gpr .r1 + 8 ∧ s'.gpr .r3 = s.gpr .r3 - 1 ∧
      zeroCount s' = some ((s.gpr .r3 - 1) == 0) ∧ Keep [.r1, .r3] s s' := by
  refine ⟨_, by
    simp only [Impl.TripleDes.Arm.Ecb.advance,
      runBlock_cons, exec, Op2.eval, 
      ]
    rfl, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · rfl
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_subFlags, gpr_setReg, hr.1, hr.2, ite_false]
    · simp only [mem_subFlags, mem_setReg]
    · simp only [rd_subFlags, rd_setReg]
    · simp only [wr_subFlags, wr_setReg]

theorem counter_zero (n : Nat) (hn : n < 2 ^ 32) :
    ((BitVec.ofNat 32 n) == (0 : BitVec 32)) = decide (n = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    obtain ht := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at ht
    exact ht
  · intro h; rw [h]; rfl

end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `Body` -/

section

namespace VG.Proof.TripleDes.Arm.Ecb

open VG VG.Arm VG.Spec.TripleDes

structure BodyPost (d : Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .r1 = s.gpr .r1 + 8
  count : s'.gpr .r3 = BitVec.ofNat 32 (n - 1)
  flag : zeroCount s' = some (decide (n = 1))
  reg : ∀ r ∈ kept, r ≠ .r1 → r ≠ .r3 → s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, r ≠ .r3 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame ([dataR s, ⟨State.addr (s.gpr .r2), 512⟩]) s.mem s'.mem
  data : Spec.TripleDes.blockAt s'.mem (State.addr (s.gpr .r1)) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1)))

theorem body_ok (d : Direction) (s : State) (n : Nat) (hn : 1 ≤ n) (bound : n < 2 ^ 32)
    (count : s.gpr .r3 = BitVec.ofNat 32 n) (hp : StepPre s) :
    WP isa (.seq (Impl.TripleDes.Arm.Ecb.blockCall d) (.block Impl.TripleDes.Arm.Ecb.advance)) s (BodyPost d s n) := by
  apply WP.seq
  apply WP.mono (call_ok d s hp.call)
  intro s₁ h₁
  obtain ⟨s₂, run₂, ptr₂, count₂, flag₂, keep₂⟩ := advance_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain count' : s₁.gpr .r3 - 1 = BitVec.ofNat 32 (n - 1) := by
    rw [h₁.reg .r3 (by decide), count]
    exact Offset.ofNat_sub_ofNat hn
  refine ⟨by rw [ptr₂, h₁.reg .r1 (by decide)], count₂.trans count', ?_, ?_, ?_,
    keep₂.rd.trans h₁.rd, keep₂.wr.trans h₁.wr, ?_, ?_⟩
  · rw [flag₂, count']
    rw [counter_zero (n - 1) (by omega_using [bound])]
    obtain he : n - 1 = 0 ↔ n = 1 := by omega_using [hn]
    simp only [he]
  · intro r hr hs hb
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.reg r hr)
  · intro r hr hb
    obtain hs : r ≠ .r1 := by
      obtain fact : ∀ r ∈ savedAcrossCall, r ≠ .r1 := by decide
      exact fact r hr
    exact (keep₂.reg r (by simp [hs, hb])).trans (h₁.callee r hr)
  · rw [keep₂.mem]; exact h₁.mem
  · rw [keep₂.mem]; exact h₁.output

theorem BodyPost.tail {d : Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (hn : 1 ≤ n) : StepPre s' n :=
  hp.slice (i := 1) (by omega_using []) hn h.rd h.wr
    (h.reg .r0 (by decide) (by decide) (by decide))
    (h.reg .r2 (by decide) (by decide) (by decide))
    h.ptr

end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `LoopFrame` -/

section

/-! # Frames for successive ECB blocks -/

namespace VG.Proof.TripleDes.Arm.Ecb

open VG VG.Arm

def stepWrites (s : State) : List Region := [dataR s, ⟨State.addr (s.gpr .r2), 512⟩]

def loopWrites (s : State) (n : Nat) : List Region := [dataR s n, ⟨State.addr (s.gpr .r2), 512⟩]

theorem loopFrame_slice {s s' : State} {n m i : Nat} {a b : Mem}
    (h : Frame (loopWrites s' m) a b) (bound : i + m ≤ n) (fit : (s.gpr .r1).toNat + 8 * i < 2 ^ 32)
    (buf : s'.gpr .r2 = s.gpr .r2)
    (ptr : s'.gpr .r1 = s.gpr .r1 + BitVec.ofNat 32 (8 * i)) :
    Frame (loopWrites s n) a b := by
  apply h.sub
  intro r hr
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨dataR s n, by simp [loopWrites], ?_⟩
    change Region.Sub ⟨State.addr (s'.gpr .r1), 8 * m⟩ ⟨State.addr (s.gpr .r1), 8 * n⟩
    rw [ptr, addr_add fit]
    exact Offset.sub_base _ (by omega_using [bound])
  · refine ⟨⟨State.addr (s.gpr .r2), 512⟩, by simp [loopWrites], ?_⟩
    rw [buf]; exact fun _ h => h

theorem BodyPost.frame {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hn : 1 ≤ n) : Frame (loopWrites s n) s.mem s'.mem :=
  loopFrame_slice (m := 1) (i := 0) h.mem hn (s.gpr .r1).isLt rfl (by simp)

theorem BodyPost.schedule {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hp : StepPre s) :
    Spec.TripleDes.scheduleAt s'.mem (State.addr (s.gpr .r0)) = Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0)) := by
  apply VG.Proof.TripleDes.scheduleAt_eq_of_frame _ h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyData
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))

theorem BodyPost.tailData {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64) :
    Spec.TripleDes.blocksAt s'.mem (State.addr (s.gpr .r1) + 8) n = Spec.TripleDes.blocksAt s.mem (State.addr (s.gpr .r1) + 8) n := by
  obtain sub : Region.Sub ⟨State.addr (s.gpr .r1) + 8, 8 * n⟩ (dataR s (n + 1)) :=
    Offset.sub_base _ (by change 8 + 8 * n ≤ 8 * (n + 1); omega_using [])
  obtain sep : (Region.mk (State.addr (s.gpr .r1) + 8) (8 * n)).Disjoint (dataR s) :=
    Offset.disjoint_base _ (d := 8) (n := 8 * n) (k := 8) (by decide) (by omega_using [bound])
  apply VG.Proof.TripleDes.blocksAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro sep
      ((hp.dataBuf.sub_left sub).sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))

theorem firstBlock_frame {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat} {m : Mem}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64)
    (frame : Frame (loopWrites s' n) s'.mem m) (hn : 1 ≤ n) :
    Spec.TripleDes.blockAt m (State.addr (s.gpr .r1)) = Spec.TripleDes.blockAt s'.mem (State.addr (s.gpr .r1)) := by
  obtain first : Region.Sub (dataR s) (dataR s (n + 1)) := Region.sub_prefix (by change 8 ≤ 8 * (n + 1); omega_using [])
  obtain sep : (dataR s).Disjoint ⟨State.addr (s.gpr .r1) + 8, 8 * n⟩ :=
    Offset.base_disjoint _ (e := 8) (n := 8 * n) (k := 8) (by decide) (by omega_using [bound])
  apply VG.Proof.TripleDes.blockAt_eq_of_frame _ frame
  obtain buf := h.reg .r2 (by decide) (by decide) (by decide)
  obtain ptrAddr : State.addr (s'.gpr .r1) = State.addr (s.gpr .r1) + 8 := by
    rw [h.ptr]
    exact addr_add (k := 8) (by omega_using [hp.dataFit, hn])
  simpa only [loopWrites, dataR, buf, ptrAddr,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro sep
      ((hp.dataBuf.sub_left first).sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))

end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `Loop` -/

section

/-! # Correctness of the ECB loop on complete blocks -/

namespace VG.Proof.TripleDes.Arm.Ecb

open VG VG.Arm
open VG.Proof.TripleDes (blocksAt_cons)

structure LoopPost (d : Spec.TripleDes.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .r1 = s.gpr .r1 + BitVec.ofNat 32 (8 * n)
  count : s'.gpr .r3 = 0
  reg : ∀ r ∈ kept, r ≠ .r1 → r ≠ .r3 → s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, r ≠ .r3 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (loopWrites s n) s.mem s'.mem
  data : Spec.TripleDes.blocksAt s'.mem (State.addr (s.gpr .r1)) n =
    Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.TripleDes.blocksAt s.mem (State.addr (s.gpr .r1)) n)

theorem ecb_cons (keys : Spec.TripleDes.Schedule) (d : Spec.TripleDes.Direction)
    (b : Spec.TripleDes.Block) (bs : List Spec.TripleDes.Block) :
    Spec.TripleDes.ecb keys d (b :: bs) = blockResult keys d b :: Spec.TripleDes.ecb keys d bs := by
  cases d <;> rfl

theorem loop_ok (d : Spec.TripleDes.Direction) (n : Nat) :
    ∀ s : State, 1 ≤ n → 8 * n ≤ 2 ^ 32 → StepPre s n → s.gpr .r3 = BitVec.ofNat 32 n →
      WP isa (.loop (.seq (Impl.TripleDes.Arm.Ecb.blockCall d) (.block Impl.TripleDes.Arm.Ecb.advance)) .ne) s (LoopPost d s n) := by
  induction n with
  | zero => intro s hn; omega
  | succ n ih =>
    intro s hn bound hp count
    obtain ⟨t₁, s₁, exec₁, h₁⟩ := body_ok d s (n + 1) hn (by omega_using [bound]) count (hp.head hn)
    by_cases hz : n = 0
    · subst n
      refine ⟨_, s₁, Exec.loopExit exec₁ ?_, ?_⟩
      · simp only [eval_nonzeroCount, h₁.flag, decide_true, Option.map_some, Bool.not_true]
      · refine ⟨h₁.ptr, h₁.count, h₁.reg, h₁.callee, h₁.rd, h₁.wr, h₁.frame (by decide), ?_⟩
        · rw [blocksAt_cons, blocksAt_cons, ecb_cons]
          simp only [Spec.TripleDes.blocksAt, List.range_zero, List.map_nil,
            Spec.TripleDes.ecb, List.map_nil]
          exact congrArg (· :: []) h₁.data
    · have hp₁ := h₁.tail hp (by omega_using [hz])
      obtain ⟨t₂, s₂, exec₂, h₂⟩ := ih s₁ (by omega_using [hz]) (by omega_using [bound]) hp₁ (by simpa using h₁.count)
      refine ⟨_, s₂, Exec.loopNext exec₁ ?_ exec₂, ?_⟩
      · have he : n + 1 ≠ 1 := by omega_using [hz]
        simp only [eval_nonzeroCount, h₁.flag, he, decide_false, Option.map_some, Bool.not_false]
      · have key := h₁.schedule (hp.head hn)
        obtain tail := h₁.tailData hp (by omega_using [bound])
        have data := h₂.data
        obtain ki := h₁.reg .r0 (by decide) (by decide) (by decide)
        obtain bi := h₁.reg .r2 (by decide) (by decide) (by decide)
        obtain ptrAddr : State.addr (s₁.gpr .r1) = State.addr (s.gpr .r1) + 8 := by
          rw [h₁.ptr]
          exact addr_add (k := 8) (by omega_using [hp.dataFit, hz])
        rw [ki, ptrAddr, key, tail] at data
        refine ⟨?_, h₂.count, ?_, ?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, ?_, ?_⟩
        · rw [h₂.ptr, h₁.ptr, BitVec.add_assoc]
          exact congrArg (s.gpr .r1 + ·) (by
            change BitVec.ofNat 32 8 + BitVec.ofNat 32 (8 * n) = _
            rw [← BitVec.ofNat_add]
            exact congrArg (BitVec.ofNat 32) (by omega_using []))
        · intro r hr hs hb
          exact (h₂.reg r hr hs hb).trans (h₁.reg r hr hs hb)
        · intro r hr hb
          exact (h₂.callee r hr hb).trans (h₁.callee r hr hb)
        · exact (h₁.frame hn).trans (loopFrame_slice (i := 1) h₂.mem (by omega_using []) (by omega_using [hp.dataFit, hz]) bi h₁.ptr)
        · have first := firstBlock_frame h₁ hp (by omega_using [bound]) h₂.mem (by omega_using [hz])
          rw [blocksAt_cons, first, h₁.data, data, blocksAt_cons, ecb_cons]

theorem maybeLoop_ok (d : Spec.TripleDes.Direction) (s : State) (n : Nat) (bound : 8 * n ≤ 2 ^ 32)
    (hp : StepPre s n) (count : s.gpr .r3 = BitVec.ofNat 32 n)
    (initialFlag : zeroCount s = some (decide (n = 0)))
    :
    WP isa (.ite .eq (.block []) (.loop (.seq (Impl.TripleDes.Arm.Ecb.blockCall d) (.block Impl.TripleDes.Arm.Ecb.advance)) .ne)) s (LoopPost d s n) := by
  have flag' := initialFlag
  by_cases hz : n = 0
  · subst n
    apply WP.ite true (by simp only [eval_zeroCount, flag', decide_true])
    · intro _
      apply WP.block_nil
      refine ⟨by simp, count, fun _ _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _, ?_⟩
      · rfl
    · simp
  · apply WP.ite false (by simp only [eval_zeroCount, flag', hz, decide_false])
    · simp
    · intro _
      exact loop_ok d n s (by omega_using [hz]) bound hp count


end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `IO` -/

section

namespace VG.Proof.TripleDes.Arm.Ecb
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (Keep gpr_subFlags mem_subFlags rd_subFlags wr_subFlags)

def savedMem (s : State) : Mem :=
  s.mem.writeW (State.addr (s.gpr .r3) + BitVec.ofNat 64 512) (s.gpr .lr)

theorem save_ok (s : State) (fit : (s.gpr .r3).toNat + 1024 ≤ 2 ^ 32)
    (hw : InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 512) 4) :
    ∃ s', runBlock isa Impl.TripleDes.Arm.Ecb.save s = some s' ∧ Keep [] {s with mem := savedMem s} s' := by
  refine ⟨_, by
    simp only [Impl.TripleDes.Arm.Ecb.save, runBlock_cons, runStep_some, runBlock_nil,
      exec, show (512 : Nat) < 4096 from by decide, ite_true, State.store32,
      addr_add (a := s.gpr .r3) (k := 512) (by omega_using [fit]), hw]
    rfl, ?_⟩
  exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem savedMem_frame (s : State) : Frame [⟨State.addr (s.gpr .r3), 1024⟩] s.mem (savedMem s) :=
  (Frame.refl _ _).writeW List.mem_cons_self _
    (Offset.contains_base _ (by decide : 512 + 4 ≤ 1024) (by decide))

theorem savedMem_link (s : State) :
    (savedMem s).readW (State.addr (s.gpr .r3) + BitVec.ofNat 64 512) 32 = s.gpr .lr := by
  rw [savedMem, Mem.readW_writeW_self32]

theorem setup_ok (s : State) :
    ∃ s', runBlock isa Impl.TripleDes.Arm.Ecb.setup s = some s' ∧
      s'.gpr .r3 = s.gpr .r2 ∧ s'.gpr .r2 = s.gpr .r3 ∧
      zeroCount s' = some (s.gpr .r2 == 0) ∧ Keep [.r12, .r3, .r2] s s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Impl.TripleDes.Arm.Ecb.setup, rr,
      runBlock_cons, runStep_some, exec, Op2.eval, 
      Option.map_some, gpr_setReg]
    rfl, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_subFlags, gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · change some (s.gpr .r2 - 0 == 0) = _
    exact congrArg (fun v : BitVec 32 => some (v == 0)) (by bv_omega)
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_subFlags, gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]
    · simp only [mem_subFlags, mem_setReg]
    · simp only [rd_subFlags, rd_setReg]
    · simp only [wr_subFlags, wr_setReg]

theorem restore_ok (s : State) (lr : BitVec 32)
    (fit : (s.gpr .r2).toNat + 1024 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 512) 4)
    (hv : s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 512) 32 = lr) :
    ∃ s', runBlock isa Impl.TripleDes.Arm.Ecb.restore s = some s' ∧
      s'.gpr .lr = lr ∧ Keep [.lr] s s' := by
  refine ⟨_, by
    simp only [Impl.TripleDes.Arm.Ecb.restore, runBlock_cons, runStep_some, runBlock_nil,
      exec, show (512 : Nat) < 4096 from by decide, ite_true, State.load32,
      addr_add (a := s.gpr .r2) (k := 512) (by omega_using [fit]), hr, Option.map_some, hv]
    rfl, gpr_setReg_self _ _ _, ?_⟩
  exact ⟨fun r h => gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using h), rfl, rfl, rfl⟩

theorem LoopPost.scratchRead {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : LoopPost d s n s') (hp : StepPre s n) (i : Nat) (hi : 512 ≤ i ∧ i + 4 ≤ 1024) :
    s'.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 32 =
      s.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 32 := by
  obtain sub : Region.Sub ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 i, 4⟩ (bufR s) :=
    Offset.sub_base _ hi.2
  obtain sep : (Region.mk (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 4).Disjoint
      ⟨State.addr (s.gpr .r2), 512⟩ := Offset.disjoint_base _ (by omega_using [hi]) (by omega_using [hi])
  apply h.mem.readW (r := ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 i, 4⟩) (Region.contains_self _ _)
    (hn := by decide)
  simpa only [loopWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ((hp.dataBuf.sub_right sub).symm) sep

end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `Contract` -/

section

namespace VG.Proof.TripleDes.Arm.Ecb

open VG VG.Arm

def contract (d : Spec.TripleDes.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 384⟩
    let data : Region := ⟨State.addr (s.gpr .r1), 8 * (s.gpr .r2).toNat⟩
    let buf : Region := ⟨State.addr (s.gpr .r3), 1024⟩
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧
      (s.gpr .r1).toNat + 8 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧ (s.gpr .r0).toNat + 384 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 1024 ≤ 2 ^ 32
  post s s' :=
    Spec.TripleDes.blocksAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
      Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))) d
        (Spec.TripleDes.blocksAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
  pub := PublicRegs [.r0, .r1, .r2, .r3]

end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `Correct` -/

section

namespace VG.Proof.TripleDes.Arm.Ecb
open VG VG.Arm

theorem ecb_correct (d : Spec.TripleDes.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (Impl.TripleDes.Arm.Ecb.ecb d) s
      (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (contract d).post s s') := by
  obtain ⟨hrd, hwr, keyData, keyBuf, dataBuf, fit, keyFit, bufFit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 1024) :
      InRegions s.wr (State.addr (s.gpr .r3) + BitVec.ofNat 64 i) 4 := by
    rw [hwr]
    exact ⟨⟨State.addr (s.gpr .r3), 1024⟩, by simp, Offset.contains_base _ hi (by omega_using [hi])⟩
  rw [Impl.TripleDes.Arm.Ecb.ecb]
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s bufFit (writes 512 (by decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, count₂, buf₂, flag₂, keep₂⟩ := setup_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s.gpr r := keep₁.reg r (by simp)
  rw [g₁] at count₂ buf₂ flag₂
  obtain key₂ := (keep₂.reg .r0 (by decide)).trans (g₁ .r0)
  obtain data₂ := (keep₂.reg .r1 (by decide)).trans (g₁ .r1)
  obtain rd₂ := keep₂.rd.trans keep₁.rd
  obtain wr₂ := keep₂.wr.trans keep₁.wr
  obtain mem₂ : s₂.mem = savedMem s := keep₂.mem.trans keep₁.mem
  obtain scratchFrame : Frame [⟨State.addr (s.gpr .r3), 1024⟩] s.mem s₂.mem := by
    rw [mem₂]; exact savedMem_frame s
  obtain initialKey := VG.Proof.TripleDes.scheduleAt_eq_of_frame (State.addr (s.gpr .r0)) scratchFrame
    (by simpa using keyBuf)
  obtain initialData := VG.Proof.TripleDes.blocksAt_frame scratchFrame (State.addr (s.gpr .r1)) (s.gpr .r2).toNat
    (by simpa using dataBuf)
  obtain hp₂ : StepPre s₂ (s.gpr .r2).toNat := by
    constructor
    · simp only [keyR, dataR, bufR, key₂, data₂, buf₂, rd₂, wr₂, hrd, hwr]
      exact fun _ _ h => h
    · simp only [dataR, bufR, data₂, buf₂, wr₂, hwr]
      exact fun _ _ h => h
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
    · rw [key₂]; exact keyFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
  obtain flag : zeroCount s₂ = some (decide ((s.gpr .r2).toNat = 0)) := by
    obtain hz := counter_zero (s.gpr .r2).toNat (s.gpr .r2).isLt
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hz
    exact flag₂.trans (congrArg some hz)
  apply WP.seq
  apply WP.mono (maybeLoop_ok d s₂ (s.gpr .r2).toNat (by omega_using [fit]) hp₂
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using count₂) flag)
  intro s₃ h₃
  obtain rd₃ := h₃.rd.trans rd₂
  obtain wr₃ := h₃.wr.trans wr₂
  obtain buf₃ := (h₃.reg .r2 (by decide) (by decide) (by decide)).trans buf₂
  obtain readable : InRegions (s₃.rd ++ s₃.wr)
      (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 512) 4 := by
    rw [rd₃, wr₃, buf₃]
    obtain ⟨r, hr, hc⟩ := writes 512 (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain link : s₃.mem.readW (State.addr (s₃.gpr .r2) + BitVec.ofNat 64 512) 32 = s.gpr .lr := by
    obtain h := h₃.scratchRead hp₂ 512 (by decide)
    rw [buf₂, mem₂, savedMem_link] at h
    rw [buf₃]; exact h
  obtain ⟨s₄, run₄, link₄, keep₄⟩ := restore_ok s₃ (s.gpr .lr)
    (by rw [buf₃]; exact bufFit) readable link
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · intro r hr
    by_cases hl : r = .lr
    · subst r; exact link₄
    obtain saved : ∀ r ∈ preserved, r ≠ .lr → r ∈ savedAcrossCall ∧ r ≠ .r3 := by decide
    rw [keep₄.reg r (by simpa only [List.mem_singleton] using hl),
      h₃.callee r (saved r hr hl).1 (saved r hr hl).2]
    obtain sep : ∀ r ∈ preserved, r ≠ .lr → r ∉ [.r12, .r3, .r2] := by decide
    exact (keep₂.reg r (sep r hr hl)).trans (g₁ r)
  · have out := h₃.data
    rw [key₂, data₂, initialKey, initialData] at out
    change Spec.TripleDes.blocksAt s₄.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat = _
    rw [keep₄.mem]; exact out

end VG.Proof.TripleDes.Arm.Ecb

end

/-! ## `Verified` -/

section

namespace VG.Proof.TripleDes.Arm.Ecb

open VG VG.Arm

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1024⟩]

theorem encrypt_correct (s : State) (hs : (contract .encrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.Arm.Ecb.encrypt s t s' ∧ abiPreserved s s' ∧
      (contract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := ecb_correct .encrypt s hs
  change Exec isa Impl.TripleDes.Arm.Ecb.encrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (contract .decrypt).pre s) :
    ∃ t s', Exec isa Impl.TripleDes.Arm.Ecb.decrypt s t s' ∧ abiPreserved s s' ∧
      (contract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := ecb_correct .decrypt s hs
  change Exec isa Impl.TripleDes.Arm.Ecb.decrypt s t s' at he
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

theorem publicRegs_four (s₁ s₂ : State) : PublicRegs [.r0, .r1, .r2, .r3] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
      s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 := by
  simp [PublicRegs]

theorem encrypt_verified : Verified target Impl.TripleDes.Arm.Ecb.encrypt
    (Proof.TripleDes.ecbEncryptScratchContract abi 0) := by
  refine Verified.of_correct encrypt_correct
    (ecbEncrypt_constantTime _) ?_
  sig_implies [Proof.TripleDes.ecbEncryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr, contract, publicRegs_four] [satState] using satState

theorem decrypt_verified : Verified target Impl.TripleDes.Arm.Ecb.decrypt
    (Proof.TripleDes.ecbDecryptScratchContract abi 0) := by
  refine Verified.of_correct decrypt_correct
    (ecbDecrypt_constantTime _) ?_
  sig_implies [Proof.TripleDes.ecbDecryptScratchContract, Proof.TripleDes.ecbScratchContract,
    Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr, contract, publicRegs_four] [satState] using satState

end VG.Proof.TripleDes.Arm.Ecb

end
