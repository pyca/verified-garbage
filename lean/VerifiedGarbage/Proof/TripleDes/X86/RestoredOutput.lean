module

public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.TripleDes.X86.WordStore
public import VerifiedGarbage.Proof.TripleDes.X86.Bytes
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Rc2.X86.Save
public import VerifiedGarbage.Proof.TripleDes.X86.Sbox
public import VerifiedGarbage.Proof.Rc2.X86.KeySteps
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Slots
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.Framework.X86.Taint

/-! ### `TripleDes.X86.Save`, which this module and modules that import it used -/

section

/-! ### `TripleDes.X86.RoundStep`, which this module and modules that import it used -/

section

/-! ### `TripleDes.X86.Round`, which only this module used -/

section

/-! ### `TripleDes.X86.Spills`, which only this module used -/

section

@[expose] public section

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
    (instrs (sboxLiteral i)).all spillSafe = true := by decide +kernel

theorem spillStep_frame (i : Instr) (s s' : State)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (h : spillSafe i = true) (he : exec i s = some s') :
    s'.gpr .ebp = s.gpr .ebp ∧ Frame [spillRegion s] s.mem s'.mem := by
  cases i <;> simp only [spillSafe, Bool.false_eq_true] at h
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
      change (spillRegion s).Contains (addr (s.gpr .ebp) m.disp) 4
      rw [VG.X86.addr_eq (by omega_using [fit, hhi])]
      exact Offset.contains (addr32 (s.gpr .ebp)) (by omega_using [hlo]) (by omega_using [hhi]) (by decide)
    · cases he

theorem spillBlock_frame (is : List Instr) (s s' : State)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (hsafe : is.all spillSafe = true) (he : runBlock isa is s = some s') :
    s'.gpr .ebp = s.gpr .ebp ∧ Frame [spillRegion s] s.mem s'.mem := by
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
    have hr : spillRegion s₁ = spillRegion s := by simp only [spillRegion, hg]
    rw [hr] at hf'
    exact hf'

/-- The saved registers and round counter in scratch slots 0–7 are
outside the S-box's frame, as are the key schedule and block data. -/
theorem sbox_spillFrame (i : Nat) (hi : i < 8) (s s' : State)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (he : runBlock isa (sboxCode i) s = some s') :
    Frame [spillRegion s] s.mem s'.mem := by
  have h := spillSafe_check i hi
  rw [sboxLiteral_eq i hi] at h
  exact (spillBlock_frame _ _ _ fit h he).2

end VG.Proof.TripleDes.X86

end

end


@[expose] public section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.TripleDes.X86
open VG.Proof.TripleDes.X86.Linear

theorem roundInput_bounds : ∀ i < 8, ∀ j < 6,
    32 - Spec.TripleDes.expansion.getD (6 * i + 5 - j) 1 < 32 ∧
    47 - (6 * i + 5 - j) < 64 := by
  decide +kernel

theorem bitOf_low (W : Nat → BitVec 32) (a : Nat) (ha : a < 32) :
    bitOf W a = (W 0).getLsbD a := by
  simp only [bitOf, Nat.div_eq_of_lt ha, Nat.mod_eq_of_lt ha]

def keyWord (s : State) : BitVec 64 :=
  s.mem.readW (wordAddr (s.gpr .edx) 1) 32 ++ s.mem.readW (wordAddr (s.gpr .edx) 0) 32

theorem bitOf_key (s : State) (a : Nat) (ha : a < 64) :
    bitOf (fun k => if k = 0 then s.gpr .edi else
      s.mem.readW (wordAddr (s.gpr .edx) (k - 1)) 32) (32 + a) =
    (keyWord s).getLsbD a := by
  simp only [bitOf, keyWord, BitVec.getLsbD_append]
  by_cases h : a < 32
  · have hd : (32 + a) / 32 = 1 := by omega_using [h]
    simp only [h, ite_true, hd, Nat.add_mod_left, Nat.mod_eq_of_lt h]
    rfl
  · have hd : (32 + a) / 32 = 2 := by omega_using [ha, h]
    have hm : (32 + a) % 32 = a - 32 := by omega_using [ha, h]
    simp only [h, ite_false, hd, hm]
    rfl

def roundChunk (i : Nat) (r : BitVec 32) (k : BitVec 48) : BitVec 6 :=
  ((Spec.TripleDes.permute Spec.TripleDes.expansion r ^^^ k) >>> (6 * (7 - i))).setWidth 6

theorem roundChunk_bit (i j : Nat) (hi : i < 8) (hj : j < 6)
    (r : BitVec 32) (k : BitVec 64) :
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

theorem input_keeps : ∀ i < 8,
    [Reg.esp, .ebp, .esi, .edi, .edx].all (fun r =>
      (instrs (inputLiterals.getD i (.block []))).all fun op => op.dst != some r) = true := by
  decide +kernel

theorem input_keep (i : Nat) (hi : i < 8) (r : Reg)
    (hr : r ∈ [Reg.esp, .ebp, .esi, .edi, .edx]) :
    (sboxInputBits i).all (fun op => op.dst != some r) = true := by
  have h := List.all_eq_true.mp (input_keeps i hi) r hr
  rw [inputLiteral_eq i hi] at h
  exact h

theorem input_spillSafe : ∀ i < 8,
    (instrs (inputLiterals.getD i (.block []))).all spillSafe = true := by decide +kernel

theorem roundInput_chunk (i : Nat) (hi : i < 8) (s : State) (hok : Ok inputCfg s) :
    ∃ s', runBlock isa (sboxInputBits i) s = some s' ∧
      inputAt s' 0 = roundChunk i (s.gpr .edi) ((keyWord s).setWidth 48) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.esp, .ebp, .esi, .edi, .edx], s'.gpr r = s.gpr r) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s', run, bits, rd, wr, keep, _⟩ := roundInput_ok i hi s hok
  have kept : ∀ r ∈ [Reg.esp, .ebp, .esi, .edi, .edx], s'.gpr r = s.gpr r :=
    fun r hr => keep r (input_keep i hi r hr)
  have safe := input_spillSafe i hi
  rw [inputLiteral_eq i hi] at safe
  refine ⟨s', run, ?_, rd, wr, kept, (spillBlock_frame _ _ _ hok.fit safe run).2⟩
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [inputAt, getLsbD_ofBits, hj, decide_true, Bool.true_and,
    kept .ebp (by decide)]
  rw [bits j hj 0 (by decide), ← BitVec.setWidth_eq (s.gpr .edi), roundChunk_bit i j hi hj]
  obtain ⟨hr, hk⟩ := roundInput_bounds i hi j hj
  simp only [inputBits, ite_true, xorBits_cons, xorBits_nil, Bool.xor_false,
    bitOf_low _ _ hr, roundInputs, ite_true]
  have hkey : bitOf (roundInputs s) (32 + (47 - (6 * i + 5 - j))) =
      (keyWord s).getLsbD (47 - (6 * i + 5 - j)) := bitOf_key s _ hk
  rw [hkey]

def boxSource (p : Nat) : Nat := Spec.TripleDes.p.getD (31 - p) 1 - 1

def boxPiece (i : Nat) (b : BitVec 4) : BitVec 32 :=
  ofBits 32 fun p => if boxSource p / 4 = i then
    b.getLsbD (3 - boxSource p % 4) else false

theorem outputBits_shape : ∀ i < 8, ∀ p < 32,
    outputBits i p = [128 + p] ++
      (if boxSource p / 4 = i then [32 * (3 - boxSource p % 4)] else []) := by
  decide +kernel
theorem output_keeps : ∀ i < 8,
    [Reg.esp, .ebp, .edi, .edx, .ebx, .ecx].all (fun r =>
      (instrs (outputLiterals.getD i (.block []))).all fun op => op.dst != some r) = true := by
  decide +kernel

theorem output_keep (i : Nat) (hi : i < 8) (r : Reg)
    (hr : r ∈ [Reg.esp, .ebp, .edi, .edx, .ebx, .ecx]) :
    (sboxOutputs i).all (fun op => op.dst != some r) = true := by
  have h := List.all_eq_true.mp (output_keeps i hi) r hr
  rw [outputLiteral_eq i hi] at h
  exact h

theorem output_spillSafe : ∀ i < 8,
    (instrs (outputLiterals.getD i (.block []))).all spillSafe = true := by decide +kernel

theorem roundOutput_piece (i : Nat) (hi : i < 8) (s : State) (hok : Ok outputCfg s)
    (b : BitVec 4)
    (hb : ∀ j < 4,
      (s.mem.readW (wordAddr (s.gpr .ebp) (16 + j)) 32).getLsbD 0 = b.getLsbD j) :
    ∃ s', runBlock isa (sboxOutputs i) s = some s' ∧
      s'.gpr .esi = s.gpr .esi ^^^ boxPiece i b ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.esp, .ebp, .edi, .edx, .ebx, .ecx], s'.gpr r = s.gpr r) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s', run, bits, rd, wr, keep, _⟩ := roundOutput_ok i hi s hok
  have safe := output_spillSafe i hi
  rw [outputLiteral_eq i hi] at safe
  refine ⟨s', run, ?_, rd, wr, fun r hr => keep r (output_keep i hi r hr),
    (spillBlock_frame _ _ _ hok.fit safe run).2⟩
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [bits p hp, outputBits_shape i hi p hp]
  simp only [BitVec.getLsbD_xor, List.cons_append, List.nil_append, xorBits_cons]
  have hleft : bitOf (roundOutputs s) (128 + p) = (s.gpr .esi).getLsbD p := by
    have h := VG.Proof.TripleDes.X86.Linear.bitOf_word (roundOutputs s) 4 p hp
    exact h
  rw [hleft]
  by_cases h : boxSource p / 4 = i
  · simp only [h, ite_true, xorBits_cons, xorBits_nil, Bool.xor_false]
    have hj : 3 - boxSource p % 4 < 4 := by omega_using []
    have hjne : 3 - boxSource p % 4 ≠ 4 := by omega_using []
    have hbit := VG.Proof.TripleDes.X86.Linear.bitOf_word (roundOutputs s)
      (3 - boxSource p % 4) 0 (by decide)
    simp only [Nat.add_zero] at hbit
    rw [hbit]
    simp only [roundOutputs, hjne, ite_false, hb _ hj, boxPiece, getLsbD_ofBits,
      hp, decide_true, Bool.true_and, h, ite_true]
  · simp only [h, ite_false, xorBits_nil, Bool.xor_false, boxPiece, getLsbD_ofBits,
      hp, decide_true, Bool.true_and]
end VG.Proof.TripleDes.X86

end

end


/-! ## `Box` -/

@[expose] public section

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd VG.Impl.TripleDes.X86

def roundKeyPtr (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .ebp) 4) 32

def roundKeyWord (s : State) : BitVec 64 :=
  s.mem.readW (wordAddr (roundKeyPtr s) 1) 32 ++
    s.mem.readW (wordAddr (roundKeyPtr s) 0) 32

structure BoxPre (s : State) : Prop where
  scratch : Ok sboxCfg s
  read : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (roundKeyPtr s) j) 4
  disjoint : ∀ j < 2, (⟨wordAddr (roundKeyPtr s) j, 4⟩ : Region).Disjoint (spillRegion s)
  sep : ∀ k < 128, ∀ j < 2,
    Mem.Sep (wordAddr (s.gpr .ebp) k) 4 (wordAddr (roundKeyPtr s) j) 4

theorem pointerLoad_ok (s : State) (hok : Ok sboxCfg s) :
    exec (.mov .edx (.mem (memOp .ebp 16))) s = some (s.setReg .edx (roundKeyPtr s)) := by
  have hw := hok.slotIn 4 (by decide)
  have hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 4) 4 := by
    obtain ⟨r, hmem, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hmem, hc⟩
  simp only [exec, readSrc, State.load32, memOp, State.ea]
  change (if InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 4) 4 then
    some (roundKeyPtr s) else none).map (s.setReg .edx) = _
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
theorem box_ok (i : Nat) (hi : i < 8) (s : State) (pre : BoxPre s) :
    ∃ s', runBlock isa (box i) s = some s' ∧
      s'.gpr .esi = s.gpr .esi ^^^ boxPiece i
        (Spec.TripleDes.sBox i (roundChunk i (s.gpr .edi) ((roundKeyWord s).setWidth 48))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.esp, .ebp, .edi], s'.gpr r = s.gpr r) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  let s₀ := s.setReg .edx (roundKeyPtr s)
  have inputOk : Ok inputCfg s₀ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hk; exact pre.scratch.slotIn k hk
    · intro j hj; exact pre.read j hj
    · exact pre.scratch.fit
    · intro k hk j hj; exact pre.sep k hk j hj
  obtain ⟨s₁, run₁, chunk, rd₁, wr₁, keep₁, frame₁⟩ := roundInput_chunk i hi s₀ inputOk
  have hok₁ : Ok sboxCfg s₁ := pre.scratch.congr
    ((keep₁ .ebp (by decide)).trans (gpr_setReg_of_ne s _ (by decide)))
    ((keep₁ .ebp (by decide)).trans (gpr_setReg_of_ne s _ (by decide))) rd₁ wr₁
  obtain ⟨s₂, run₂, bits, rd₂, wr₂, keep₂, _⟩ := sbox_ok i hi hok₁
  have kept₂ : ∀ r ∈ [Reg.esp, .ebp, .esi, .edi], s₂.gpr r = s₁.gpr r := by
    intro r hr; apply keep₂ r
    revert hr; cases r <;> decide
  have hok₂ : Ok outputCfg s₂ := hok₁.congr
    (kept₂ .ebp (by decide)) (kept₂ .ebp (by decide)) rd₂ wr₂
  have hbits : ∀ j < 4,
      (s₂.mem.readW (wordAddr (s₂.gpr .ebp) (16 + j)) 32).getLsbD 0 =
        (Spec.TripleDes.sBox i (roundChunk i (s.gpr .edi)
          ((roundKeyWord s).setWidth 48))).getLsbD j := by
    intro j hj
    rw [kept₂ .ebp (by decide), bits j hj 0 (by decide), chunk]
    rfl
  obtain ⟨s₃, run₃, value, rd₃, wr₃, keep₃, frame₃⟩ := roundOutput_piece i hi s₂ hok₂ _ hbits
  have region₁ : spillRegion s₁ = spillRegion s := by
    simp only [spillRegion, keep₁ .ebp (by decide), s₀, gpr_setReg, reduceCtorEq, ite_false]
  have region₂ : spillRegion s₂ = spillRegion s := by
    simp only [spillRegion, kept₂ .ebp (by decide), keep₁ .ebp (by decide), s₀,
      gpr_setReg, reduceCtorEq, ite_false]
  have frame₂ := sbox_spillFrame i hi s₁ s₂ hok₁.fit run₂
  rw [region₁] at frame₂
  rw [region₂] at frame₃
  have hframe₁ : Frame [spillRegion s] s.mem s₁.mem := frame₁
  refine ⟨s₃, ?_, ?_, rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_,
    hframe₁.trans (frame₂.trans frame₃)⟩
  · simp only [box, sboxInputs, runBoxes_append, runBlock_cons, runBlock_nil,
      pointerLoad_ok s pre.scratch, runStep_some, s₀, run₁, Option.bind_some, run₂, run₃]
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

/-! ## `RoundFunction` -/

section

namespace VG.Proof.TripleDes.X86

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
  have hfold : (fun (out : Bool) i => out ^^
      (boxPiece i (sBox i (roundChunk i r k))).getLsbD j) =
      (fun out i => out ^^ (if boxSource j / 4 = i then
        (roundFunction r k).getLsbD j else false)) := by
    funext out i
    exact congrArg (fun b => out ^^ b) (boxPiece_round_bit i r k j hj)
  have hbits := foldl_xor_bits (List.range 8)
    (fun i => boxPiece i (sBox i (roundChunk i r k))) 0 j
  have hz : (0 : BitVec 32).getLsbD j = false := by
    change (BitVec.ofNat 32 0).getLsbD j = false
    exact BitVec.getLsbD_zero
  have hinit := congrArg (fun b : Bool => (List.range 8).foldl
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

end VG.Proof.TripleDes.X86

end

/-! ## `RoundBody` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd VG.Impl.TripleDes.X86

theorem roundKeyPtr_frame {s s' : State} (pre : BoxPre s)
    (base : s'.gpr .ebp = s.gpr .ebp) (frame : Frame [spillRegion s] s.mem s'.mem) :
    roundKeyPtr s' = roundKeyPtr s := by
  unfold roundKeyPtr
  rw [base]
  apply frame.readW (r := ⟨wordAddr (s.gpr .ebp) 4, 4⟩) (Region.contains_self _ _)
    (fun q hq => ?_) (by decide)
  obtain rfl := List.mem_singleton.mp hq
  change (⟨addr (s.gpr .ebp) 16, 4⟩ : Region).Disjoint (spillRegion s)
  rw [addr_eq (by have h := pre.scratch.fit; change (s.gpr .ebp).toNat + 512 ≤ _ at h; omega_using [h])]
  exact Offset.disjoint _ (by decide) (by decide) (by decide)

theorem BoxPre.frame {s s' : State} (pre : BoxPre s)
    (base : s'.gpr .ebp = s.gpr .ebp) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (frame : Frame [spillRegion s] s.mem s'.mem) :
    BoxPre s' ∧ roundKeyWord s' = roundKeyWord s := by
  have ptr := roundKeyPtr_frame pre base frame
  have region : spillRegion s' = spillRegion s := by simp only [spillRegion, base]
  constructor
  · refine ⟨pre.scratch.congr base base rd wr, ?_, ?_, ?_⟩
    · rw [rd, wr, ptr]; exact pre.read
    · rw [ptr, region]; exact pre.disjoint
    · rw [base, ptr]; exact pre.sep
  · unfold roundKeyWord
    rw [ptr]
    have hword (j : Nat) (hj : j < 2) :
        s'.mem.readW (wordAddr (roundKeyPtr s) j) 32 =
          s.mem.readW (wordAddr (roundKeyPtr s) j) 32 :=
      frame.readW (r := ⟨wordAddr (roundKeyPtr s) j, 4⟩) (Region.contains_self _ _)
        (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact pre.disjoint j hj) (by decide)
    rw [hword 0 (by decide), hword 1 (by decide)]

def contribution (r : BitVec 32) (k : BitVec 64) (i : Nat) : BitVec 32 :=
  boxPiece i (Spec.TripleDes.sBox i (roundChunk i r (k.setWidth 48)))

theorem boxes_ok (indices : List Nat) (hindices : ∀ i ∈ indices, i < 8)
    (r : BitVec 32) (k : BitVec 64) (s : State) (pre : BoxPre s)
    (hr : s.gpr .edi = r) (hk : roundKeyWord s = k) :
    ∃ s', runBlock isa (indices.flatMap box) s = some s' ∧
      s'.gpr .esi = indices.foldl (fun out i => out ^^^ contribution r k i) (s.gpr .esi) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ [Reg.esp, .ebp, .edi], s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  induction indices generalizing s with
  | nil => exact ⟨s, runBlock_nil, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | cons i indices ih =>
    have hi := hindices i List.mem_cons_self
    obtain ⟨s₁, run₁, value₁, rd₁, wr₁, keep₁, frame₁⟩ := box_ok i hi s pre
    obtain ⟨pre₁, key₁⟩ := pre.frame (keep₁ .ebp (by decide)) rd₁ wr₁ frame₁
    obtain ⟨s₂, run₂, value₂, rd₂, wr₂, keep₂, frame₂⟩ := ih
      (fun j hj => hindices j (List.mem_cons_of_mem _ hj)) s₁ pre₁
      ((keep₁ .edi (by decide)).trans hr) (key₁.trans hk)
    refine ⟨s₂, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁,
      fun q hq => (keep₂ q hq).trans (keep₁ q hq), ?_⟩
    · simp only [List.flatMap_cons, runBoxes_append, run₁, Option.bind_some, run₂]
    · rw [hr, hk] at value₁
      change s₁.gpr .esi = s.gpr .esi ^^^ contribution r k i at value₁
      simpa only [List.foldl_cons, ← value₁] using value₂
    · have hregion : spillRegion s₁ = spillRegion s := by
        simp only [spillRegion, keep₁ .ebp (by decide)]
      rw [hregion] at frame₂
      exact frame₁.trans frame₂

theorem contributions_roundFunction (r : BitVec 32) (k : BitVec 64) (l : BitVec 32) :
    (List.range 8).foldl (fun out i => out ^^^ contribution r k i) l =
      l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48) := by
  rw [foldl_xor_start]
  exact congrArg (l ^^^ ·) (boxPieces_eq_roundFunction r (k.setWidth 48))

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
    (hl : s.gpr .esi = l) (hr : s.gpr .edi = r) (hk : roundKeyWord s = k) (pre : BoxPre s) :
    ∃ s', runBlock isa roundBody s = some s' ∧
      s'.gpr .esi = r ∧ s'.gpr .edi = l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esp = s.gpr .esp ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, value, rd₁, wr₁, keep₁, frame₁⟩ := boxes_ok (List.range 8)
    (fun i hi => List.mem_range.mp hi) r k s pre hr hk
  obtain ⟨s₂, run₂, left, right, rd₂, wr₂, mem₂, base₂, sp₂⟩ := swapHalves_ok s₁
  refine ⟨s₂, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁,
    base₂.trans (keep₁ .ebp (by decide)), sp₂.trans (keep₁ .esp (by decide)), ?_⟩
  · simp only [roundBody, runBoxes_append, run₁, Option.bind_some, run₂]
  · exact left.trans ((keep₁ .edi (by decide)).trans hr)
  · rw [right, value, contributions_roundFunction, hl]
  · rw [mem₂]; exact frame₁
end VG.Proof.TripleDes.X86

end

/-! ## `RoundAdvance` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd VG.Impl.TripleDes.X86

def roundCount (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .ebp) 5) 32

def nextPtr (d : Spec.TripleDes.Direction) (s : State) : BitVec 32 :=
  if d = .encrypt then roundKeyPtr s + 8 else roundKeyPtr s - 8

def advanceMem (d : Spec.TripleDes.Direction) (s : State) : Mem :=
  (s.mem.writeW (wordAddr (s.gpr .ebp) 4) (nextPtr d s)).writeW
    (wordAddr (s.gpr .ebp) 5) (roundCount s - 1)

theorem counter_ptr_sep (s : State) (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32) :
    Mem.Sep (wordAddr (s.gpr .ebp) 5) 4 (wordAddr (s.gpr .ebp) 4) 4 := by
  change Mem.Sep (addr (s.gpr .ebp) 20) 4 (addr (s.gpr .ebp) 16) 4
  rw [addr_eq (by omega_using [fit]), addr_eq (by omega_using [fit])]
  exact Offset.sep _ (by decide) (by decide) (by decide)

theorem roundAdvance_ok (d : Spec.TripleDes.Direction) (s : State) (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa (roundAdvance d) s = some s' ∧
      s'.mem = advanceMem d s ∧ s'.zf = some ((roundCount s - 1) == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) := by
  have hw4 := hok.slotIn 4 (by decide)
  have hw5 := hok.slotIn 5 (by decide)
  have hr4 : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 4) 4 := by
    obtain ⟨r, h, hc⟩ := hw4; exact ⟨r, List.mem_append_right _ h, hc⟩
  have hr5 : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .ebp) 5) 4 := by
    obtain ⟨r, h, hc⟩ := hw5; exact ⟨r, List.mem_append_right _ h, hc⟩
  have hsep := counter_ptr_sep s hok.fit
  simp only [wordAddr, addr, sboxCfg] at hw4 hw5 hr4 hr5 hsep
  cases d <;> refine ⟨_, by
    simp only [roundAdvance, reduceCtorEq, ite_true, ite_false, runBlock_cons,
      runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load32, State.store32,
      State.ea, memOp, gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_true, ite_false,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      hw4, hw5, hr4, hr5,
      Option.bind_some, Option.map_some]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp only [mem_setReg, mem_arithFlags, advanceMem, nextPtr, roundKeyPtr,
    roundCount, reduceCtorEq, ite_true, ite_false, wordAddr, addr,
    gpr_setReg, gpr_arithFlags,
    rd_setReg, wr_setReg, rd_arithFlags, wr_arithFlags, zf_setReg, zf_arithFlags]
  all_goals try rw [Mem.readW_writeW_sep hsep (by decide)]
  all_goals try rfl
  all_goals
    intro r hr
    simp only [hr, ite_false]
end VG.Proof.TripleDes.X86

end

/-! ## `RoundStep` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)

def workRegion (s : State) : Region := ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 16, 432⟩

theorem spill_sub_work (s : State) : Region.Sub (spillRegion s) (workRegion s) :=
  Offset.sub _ (by decide) (by decide)

theorem count_spill_disjoint (s : State) (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32) :
    (⟨wordAddr (s.gpr .ebp) 5, 4⟩ : Region).Disjoint (spillRegion s) := by
  change (⟨addr (s.gpr .ebp) 20, 4⟩ : Region).Disjoint (spillRegion s)
  rw [addr_eq (by omega_using [fit])]
  exact Offset.disjoint _ (by decide) (by decide) (by decide)

theorem advance_frame (d : Spec.TripleDes.Direction) (s : State)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32) :
    Frame [workRegion s] s.mem (advanceMem d s) := by
  have h4 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 4) 4 := by
    change (workRegion s).Contains (addr (s.gpr .ebp) 16) 4
    rw [addr_eq (by omega_using [fit])]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  have h5 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 5) 4 := by
    change (workRegion s).Contains (addr (s.gpr .ebp) 20) 4
    rw [addr_eq (by omega_using [fit])]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  exact ((Frame.refl [workRegion s] s.mem).writeW (List.mem_singleton_self _) _ h4).writeW
    (List.mem_singleton_self _) _ h5

theorem countDown_rules : ∀ n < 17, 1 ≤ n →
    (BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1)) ∧
    (!(BitVec.ofNat 32 n - 1 == 0)) = decide (n ≠ 1) := by decide +kernel

theorem roundStep_ok (d : Spec.TripleDes.Direction) (s : State)
    (l r : BitVec 32) (k : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn' : n < 17)
    (hl : s.gpr .esi = l) (hr : s.gpr .edi = r) (hk : roundKeyWord s = k)
    (pre : BoxPre s) (hcount : roundCount s = BitVec.ofNat 32 n) :
    ∃ s', runBlock isa (roundBody ++ roundAdvance d) s = some s' ∧
      s'.gpr .esi = r ∧ s'.gpr .edi = l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48) ∧
      roundKeyPtr s' = nextPtr d s ∧ roundCount s' = BitVec.ofNat 32 (n - 1) ∧
      isa.eval .ne s' = some (decide (n ≠ 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.gpr .esp = s.gpr .esp ∧
      Frame [workRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, left₁, right₁, rd₁, wr₁, base₁, sp₁, frame₁⟩ := roundBody_ok s l r k hl hr hk pre
  obtain ⟨pre₁, _⟩ := pre.frame base₁ rd₁ wr₁ frame₁
  have ptr₁ := roundKeyPtr_frame pre base₁ frame₁
  have count₁ : roundCount s₁ = roundCount s := by
    unfold roundCount
    rw [base₁]
    exact frame₁.readW (r := ⟨wordAddr (s.gpr .ebp) 5, 4⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact count_spill_disjoint s pre.scratch.fit)
      (by decide)
  obtain ⟨s₂, run₂, mem₂, flag₂, rd₂, wr₂, keep₂⟩ := roundAdvance_ok d s₁ pre₁.scratch
  have base₂ : s₂.gpr .ebp = s₁.gpr .ebp := keep₂ _ (by decide)
  have ptr₂ : roundKeyPtr s₂ = nextPtr d s₁ := by
    unfold roundKeyPtr
    rw [base₂, mem₂]
    have hsep : Mem.Sep (wordAddr (s₁.gpr .ebp) 4) 4 (wordAddr (s₁.gpr .ebp) 5) 4 := by
      intro a h4 h5
      exact counter_ptr_sep s₁ pre₁.scratch.fit a h5 h4
    rw [advanceMem, Mem.readW_writeW_sep hsep (by decide), Mem.readW_writeW_self32]
  have count₂ : roundCount s₂ = BitVec.ofNat 32 (n - 1) := by
    unfold roundCount
    rw [base₂, mem₂, advanceMem, Mem.readW_writeW_self32, count₁, hcount,
      (countDown_rules n hn' hn).1]
  refine ⟨s₂, ?_, (keep₂ .esi (by decide)).trans left₁,
    (keep₂ .edi (by decide)).trans right₁, ?_, count₂, ?_, rd₂.trans rd₁, wr₂.trans wr₁,
    base₂.trans base₁, (keep₂ .esp (by decide)).trans sp₁, ?_⟩
  · simp only [runBoxes_append, run₁, Option.bind_some, run₂]
  · rw [ptr₂]; simp only [nextPtr, ptr₁]
  · change VG.X86.eval .ne s₂ = _
    simp only [VG.X86.eval, flag₂, count₁, hcount, Option.map_some, (countDown_rules n hn' hn).2]
  · have hf₁ : Frame [workRegion s] s.mem s₁.mem := frame₁.sub (by
      intro q hq; obtain rfl := List.mem_singleton.mp hq
      exact ⟨_, List.mem_singleton_self _, spill_sub_work s⟩)
    have hf₂ := advance_frame d s₁ pre₁.scratch.fit
    have hwork : workRegion s₁ = workRegion s := by simp only [workRegion, base₁]
    rw [hwork, ← mem₂] at hf₂
    exact hf₁.trans hf₂
end VG.Proof.TripleDes.X86

end

end

end

/-! ## `Initial` -/

@[expose] public section

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
    (hr : ∀ i < 2, InRegions (s.rd ++ s.wr) (wordAddr (dataArg s) i) 4) :
    ∃ s', runBlock isa readHead s = some s' ∧
      s'.gpr .edi = bswap (s.mem.readW (wordAddr (dataArg s) 0) 32) ∧
      s'.gpr .esi = bswap (s.mem.readW (wordAddr (dataArg s) 1) 32) ∧
      Keep [.edi, .esi, .edx] s s' := by
  have h0 := hr 0 (by decide)
  have h1 := hr 1 (by decide)
  simp only [wordAddr, addr, dataArg] at harg h0 h1
  refine ⟨_, by
    simp only [readHead, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
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
        (packedInput 64 32 (s.gpr .esi) (s.gpr .edi))).setWidth 32 ∧
      s'.gpr .ebx = ((Spec.TripleDes.permute Spec.TripleDes.ip
        (packedInput 64 32 (s.gpr .esi) (s.gpr .edi))) >>> 32).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.ip (by decide) 32 32
      (by decide) (by decide) (by decide) (by decide) (by decide)
      .esi .edi .eax .ebx (instrs initialPermutation.lit) initialPermutation_check (by decide +kernel) s
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
    (fit : (dataArg s).toNat + 8 ≤ 2 ^ 32)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4)
    (hr : ∀ i < 2, InRegions (s.rd ++ s.wr) (wordAddr (dataArg s) i) 4) :
    WP isa (.block blockLoad) s (InitialPost (Spec.TripleDes.permute Spec.TripleDes.ip
      (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (addr32 (dataArg s))))) s) := by
  have code : blockLoad = (readHead ++
      permuteCode Spec.TripleDes.ip 64 32 32 .eax .ebx .esi .edi .ecx) ++
      [rr .esi .ebx, rr .edi .eax] := rfl
  rw [code, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, hi₁, lo₁, keep₁⟩ := readHead_ok s harg hr
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, lo₂, hi₂, rd₂, wr₂, sp₂, mem₂, reg₂⟩ := ip_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have input : packedInput 64 32 (s₁.gpr .esi) (s₁.gpr .edi) =
      Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (addr32 (dataArg s))) := by
    rw [packedInput, lo₁, hi₁, decodeBlock_readW]
    simp only [BitVec.setWidth_eq]
    rw [show wordAddr (dataArg s) 0 = addr32 (dataArg s) from by simp [wordAddr, addr, addr32],
      show wordAddr (dataArg s) 1 = addr32 (dataArg s) + 4 from addr_eq (by omega_using [fit])]
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

/-! ## `Save` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32 Keep)

def savedReg (i : Nat) : Reg := savedRegs.getD i .ebp

def scratchArg (s : State) (slot : Nat) : BitVec 32 :=
  s.mem.readW (wordAddr (s.gpr .esp) slot) 32

def Saved (original current : State) : Prop :=
  ∀ i < 4, current.mem.readW (addr32 (current.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 32 =
    original.gpr (savedReg i)

structure SavePost (slot : Nat) (original current : State) : Prop where
  bp : current.gpr .ebp = scratchArg original slot
  rd : current.rd = original.rd
  wr : current.wr = original.wr
  reg : ∀ r, r ≠ .eax → r ≠ .ebp → current.gpr r = original.gpr r
  saved : Saved original current
  frame : Frame [⟨addr32 (scratchArg original slot), 16⟩] original.mem current.mem

theorem saveWithArg_ok (s : State) (slot : Nat)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) slot) 4)
    (fit : (scratchArg s slot).toNat + 512 ≤ 2 ^ 32)
    (hw : ∀ i < 4, InRegions s.wr (addr32 (scratchArg s slot) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (saveWithArg slot)) s (SavePost slot s) := by
  have code : saveWithArg slot =
      (([.mov .eax (.mem (memOp .esp (4 * slot)))] : List Instr) ++
        VG.Proof.Rc2.X86.saveCode .eax savedReg 4) ++ [rr .ebp .eax] := by
    unfold saveWithArg
    congr 1
  rw [code, WP.block_append_iff, WP.block_append_iff]
  let s₀ := s.setReg .eax (scratchArg s slot)
  have load : runBlock isa [.mov .eax (.mem (memOp .esp (4 * slot)))] s = some s₀ := by
    have he : exec (.mov .eax (.mem (memOp .esp (4 * slot)))) s = some s₀ := by
      simp only [exec, readSrc, State.load32, State.ea, memOp]
      change (if InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) slot) 4 then
        some (scratchArg s slot) else none).map (s.setReg .eax) = some s₀
      rw [ite_eq_left harg, Option.map_some]
    simp only [runBlock_cons, he, runStep_some, runBlock_nil]
  refine WP.of_runBlock ⟨s₀, load, ?_⟩
  have ptr₀ : s₀.gpr .eax = scratchArg s slot := gpr_setReg_self _ _ _
  have hw₀ : ∀ i < 4, InRegions s₀.wr (addr32 (s₀.gpr .eax) + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [ptr₀]; exact hw
  apply WP.mono (VG.Proof.Rc2.X86.saveCode_ok s₀ .eax savedReg 4 (by decide)
    (by rw [ptr₀]; omega_using [fit]) hw₀)
  intro s₁ h₁
  refine WP.of_runBlock ⟨s₁.setReg .ebp (s₁.gpr .eax), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, rr, readSrc, Option.map_some], ?_⟩
  have ptr₁ : s₁.gpr .eax = scratchArg s slot := by rw [h₁.1]; exact ptr₀
  refine ⟨ptr₁, h₁.2.1, h₁.2.2.1, ?_, ?_, ?_⟩
  · intro r ha hb
    rw [gpr_setReg_of_ne _ _ hb, h₁.1, gpr_setReg_of_ne _ _ ha]
  · intro i hi
    rw [gpr_setReg_self, mem_setReg, ptr₁, h₁.2.2.2, ptr₀]
    rw [VG.Proof.Rc2.X86.saveMem_read _ _ _ 4 (by decide) i hi]
    have hr : savedReg i ≠ .eax := by
      have h : ∀ i < 4, savedReg i ≠ .eax := by decide
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

theorem blockRestore_ok (original s : State) (hsaved : Saved original s)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr)
      (addr32 (s.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block blockRestore) s (RestorePost original s) := by
  have code : blockRestore = ([rr .eax .ebp] : List Instr) ++
      VG.Proof.Rc2.X86.restoreCode .eax savedReg (List.range 4) := by
    unfold blockRestore
    congr 1
  rw [code, WP.block_append_iff]
  let s₀ := s.setReg .eax (s.gpr .ebp)
  refine WP.of_runBlock ⟨s₀, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, rr, readSrc, Option.map_some]
    rfl, ?_⟩
  have hptr : s₀.gpr .eax = s.gpr .ebp := gpr_setReg_self _ _ _
  have hregs : (List.range 4).map savedReg = savedRegs := by decide
  have separate : ∀ i ∈ List.range 4, savedReg i ≠ .eax := by decide
  have h := VG.Proof.Rc2.X86.restoreCode_ok s₀ .eax savedReg (List.range 4)
    original.gpr (by rw [hptr]; omega_using [fit])
    (fun i hi => by have := List.mem_range.mp hi; omega_using [this]) separate
    (fun i hi => by rw [hptr]; exact hread i (List.mem_range.mp hi))
    (fun i hi => by rw [hptr]; exact hsaved i (List.mem_range.mp hi))
  rw [hregs] at h
  apply WP.mono h
  intro s₁ h₁
  exact ⟨h₁.1, h₁.2.mem, h₁.2.rd, h₁.2.wr,
    (h₁.2.reg .esp (by decide)).trans (gpr_setReg_of_ne s _ (by decide)),
    (h₁.2.reg .eax (by decide)).trans hptr⟩

theorem savedSlot_work_disjoint (s : State) (i : Nat) (hi : i < 4) :
    (⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint (workRegion s) :=
  Offset.disjoint _ (by omega_using [hi]) (by omega_using [hi]) (by decide)

theorem Saved.congr {original s t : State} (hs : Saved original s)
    (hbase : t.gpr .ebp = s.gpr .ebp) (hf : Frame [workRegion s] s.mem t.mem) :
    Saved original t := by
  intro i hi
  rw [hbase]
  have hm := hf.readW (a := addr32 (s.gpr .ebp) + BitVec.ofNat 64 (4 * i)) (w := 32)
    (r := ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 (4 * i), 4⟩)
    (Region.contains_self _ _) (fun q hq => by
      obtain rfl := List.mem_singleton.mp hq
      exact savedSlot_work_disjoint s i hi) (by decide)
  exact hm.trans (hs i hi)

end VG.Proof.TripleDes.X86

end

end

end

/-! ## `FinalPermutation` -/

@[expose] public section

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)

theorem fp_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.fp 64 32 32 .eax .ebx .edi .esi .ecx) s = some s' ∧
      s'.gpr .eax = (Spec.TripleDes.permute Spec.TripleDes.fp
        (packedInput 64 32 (s.gpr .edi) (s.gpr .esi))).setWidth 32 ∧
      s'.gpr .ebx = ((Spec.TripleDes.permute Spec.TripleDes.fp
        (packedInput 64 32 (s.gpr .edi) (s.gpr .esi))) >>> 32).setWidth 32 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, lo, hi, rd, wr, sp, mem, regs⟩ :=
    fixedPermutation_ok Spec.TripleDes.fp (by decide) 32 32
      (by decide) (by decide) (by decide) (by decide) (by decide)
      .edi .esi .eax .ebx (instrs finalPermutation.lit) finalPermutation_check (by decide +kernel) s
  have hcode : permuteCode Spec.TripleDes.fp 64 32 32 .eax .ebx .edi .esi .ecx = instrs finalPermutation.lit :=
    congrArg instrs finalPermutation.lit_eq
  exact ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run,
    lo, hi, rd, wr, sp, mem, regs⟩

end VG.Proof.TripleDes.X86

end

/-! ## `FinalSave` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86

def finalMem (s : State) : Mem :=
  (s.mem.writeW (wordAddr (s.gpr .ebp) 6) (s.gpr .eax)).writeW
    (wordAddr (s.gpr .ebp) 7) (s.gpr .ebx)

theorem finalStores_ok (s : State) (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa [.store (memOp .ebp 24) .eax, .store (memOp .ebp 28) .ebx] s = some s' ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = finalMem s := by
  have h6 := hok.slotIn 6 (by decide)
  have h7 := hok.slotIn 7 (by decide)
  simp only [wordAddr, addr, sboxCfg] at h6 h7
  refine ⟨{s with mem := finalMem s}, by
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
  frame : Frame [workRegion s] s.mem s'.mem

theorem finalSave_ok (s : State) (hok : Ok sboxCfg s) :
    WP isa (.block finalSave) s (FinalSavePost
      (Spec.TripleDes.permute Spec.TripleDes.fp (s.gpr .esi ++ s.gpr .edi)) s) := by
  rw [finalSave, WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, rd₁, wr₁, sp₁, mem₁, regs₁⟩ := fp_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have bp₁ := regs₁ .ebp (by decide +kernel)
  obtain ⟨s₂, run₂, gpr₂, rd₂, wr₂, mem₂⟩ := finalStores_ok s₁ (hok.congr bp₁ bp₁ rd₁ wr₁)
  have hsep : Mem.Sep (wordAddr (s.gpr .ebp) 6) 4 (wordAddr (s.gpr .ebp) 7) 4 := by
    rw [wordAddr, wordAddr, addr_eq (by have h := hok.fit; change (s.gpr .ebp).toNat + 512 ≤ 2^32 at h; omega_using [h]),
      addr_eq (by have h := hok.fit; change (s.gpr .ebp).toNat + 512 ≤ 2^32 at h; omega_using [h])]
    exact Offset.sep _ (by decide) (by decide) (by decide)
  have hm : s₂.mem = (s.mem.writeW (wordAddr (s.gpr .ebp) 6) (s₁.gpr .eax)).writeW
      (wordAddr (s.gpr .ebp) 7) (s₁.gpr .ebx) := by rw [mem₂, finalMem, bp₁, mem₁]
  refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, ?_, by rw [gpr₂]; exact bp₁,
    by rw [gpr₂]; exact sp₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩⟩
  · rw [hm, Mem.readW_writeW_sep hsep (by decide), Mem.readW_writeW_self32, lo₁]
    rfl
  · rw [hm, Mem.readW_writeW_self32, hi₁]
    rfl
  · have h6 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 6) 4 := by
      rw [wordAddr, addr_eq (by have h := hok.fit; change (s.gpr .ebp).toNat + 512 ≤ 2^32 at h; omega_using [h])]
      exact Offset.contains _ (by decide) (by decide) (by decide)
    have h7 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 7) 4 := by
      rw [wordAddr, addr_eq (by have h := hok.fit; change (s.gpr .ebp).toNat + 512 ≤ 2^32 at h; omega_using [h])]
      exact Offset.contains _ (by decide) (by decide) (by decide)
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ h6).writeW
      (List.mem_singleton_self _) _ h7

end VG.Proof.TripleDes.X86

end

/-! ## `RestoredOutput` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)

def finalWord (s : State) : BitVec 64 :=
  s.mem.readW (addr (s.gpr .eax) 28) 32 ++ s.mem.readW (addr (s.gpr .eax) 24) 32

theorem restoredOutput_ok (s : State) (fit : (dataArg s).toNat + 8 ≤ 2 ^ 32)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4)
    (hr : ∀ k ∈ [24, 28], InRegions (s.rd ++ s.wr) (addr (s.gpr .eax) k) 4)
    (hw : ∀ i < 2, InRegions s.wr (wordAddr (dataArg s) i) 4) :
    ∃ s', runBlock isa restoredOutput s = some s' ∧
      s'.mem = s.mem.writeW (addr32 (dataArg s)) (byteRev64 (finalWord s)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) := by
  have hw0 := hw 0 (by decide)
  have hw1 := hw 1 (by decide)
  have h24 := hr 24 (by decide)
  have h28 := hr 28 (by decide)
  simp only [wordAddr, addr, dataArg] at harg hw0 hw1
  simp only [addr] at h24 h28
  refine ⟨_, by
    simp only [restoredOutput, rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.store32, State.ea, memOp, harg, hw0, hw1, h24, h28, ite_true,
      Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_⟩
  · dsimp only [mem_setReg, gpr_setReg, reduceCtorEq, ite_true, ite_false]
    have ha0 : (dataArg s + BitVec.ofNat 32 0).setWidth 64 = addr32 (dataArg s) := by simp [addr32]
    have ha1 : (dataArg s + BitVec.ofNat 32 4).setWidth 64 = addr32 (dataArg s) + 4 := addr_eq (by omega_using [fit])
    change (s.mem.writeW ((dataArg s + BitVec.ofNat 32 0).setWidth 64)
      (bswap (s.mem.readW (addr (s.gpr .eax) 28) 32))).writeW
      ((dataArg s + BitVec.ofNat 32 4).setWidth 64)
      (bswap (s.mem.readW (addr (s.gpr .eax) 24) 32)) = _
    rw [ha0, ha1, writeW_pair, bswapPair]
    rfl
  · rfl
  · rfl
  · intro r ha hc hd
    simp only [gpr_setReg, ha, hc, hd, ite_false]

end VG.Proof.TripleDes.X86

end
