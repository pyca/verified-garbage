import VerifiedGarbage.Proof.TripleDes.X86.Round
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.TripleDes.Round

/-! ## `Box` -/

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
  rw [addr_eq (by have h := pre.scratch.fit; change (s.gpr .ebp).toNat + 512 ≤ _ at h; omega)]
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
  rw [addr_eq (by omega), addr_eq (by omega)]
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
  rw [addr_eq (by omega)]
  exact Offset.disjoint _ (by decide) (by decide) (by decide)

theorem advance_frame (d : Spec.TripleDes.Direction) (s : State)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32) :
    Frame [workRegion s] s.mem (advanceMem d s) := by
  have h4 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 4) 4 := by
    change (workRegion s).Contains (addr (s.gpr .ebp) 16) 4
    rw [addr_eq (by omega)]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  have h5 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 5) 4 := by
    change (workRegion s).Contains (addr (s.gpr .ebp) 20) 4
    rw [addr_eq (by omega)]
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
