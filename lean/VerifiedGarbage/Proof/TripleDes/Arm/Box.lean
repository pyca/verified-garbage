import VerifiedGarbage.Proof.TripleDes.Arm.Sbox
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.TripleDes.Arm.Round

/-! ## `Spills` -/

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
    have hd : d ≠ .r2 := by simpa using h
    simp only [exec, Option.map_eq_some_iff] at he
    obtain ⟨v, _, rfl⟩ := he
    exact write_frame _ _ _ hd
  case dp op d n op2 =>
    have hd : d ≠ .r2 := by simpa using h
    simp only [exec, Option.map_eq_some_iff] at he
    obtain ⟨v, _, rfl⟩ := he
    exact write_frame _ _ _ hd
  case ldr d n off =>
    have hd : d ≠ .r2 := by simpa using h
    simp only [exec] at he
    split at he <;> [skip; cases he]
    simp only [Option.map_eq_some_iff] at he
    obtain ⟨v, _, rfl⟩ := he
    exact write_frame _ _ _ hd
  case str t n off =>
    obtain ⟨rfl, hlo, hhi⟩ := of_decide_eq_true h
    simp only [exec] at he
    split at he <;> [skip; cases he]
    simp only [State.store32] at he
    split at he <;> [skip; cases he]
    obtain rfl := Option.some.inj he
    refine ⟨rfl, ?_⟩
    rw [addr_add (by omega_using [fit, hhi])]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (State.addr (s.gpr .r2)) (by omega) (by omega) (by decide))

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
    have hr : spillRegion s₁ = spillRegion s := by simp only [spillRegion, hg]
    rw [hr] at hf'
    exact hf'

theorem sbox_spillFrame (i : Nat) (hi : i < 8) (s s' : State)
    (fit : (s.gpr .r2).toNat + 512 ≤ 2 ^ 32)
    (he : runBlock isa (sboxCode i) s = some s') : Frame [spillRegion s] s.mem s'.mem := by
  have h := spillSafe_check i hi
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
  have kept₁ : ∀ r ∈ .r10 :: roundKept, s₁.gpr r = s.gpr r :=
    fun r hr => keep₁ r (roundInput_keep i hi r hr)
  have hok₁ : Ok sboxCfg s₁ := hok.congr
    (kept₁ .r2 (by decide)) (kept₁ .r2 (by decide)) rd₁ wr₁
  obtain ⟨s₂, run₂, bits, rd₂, wr₂, sp₂, keep₂, _⟩ := sbox_ok i hi hok₁
  have hbits : ∀ j < 4, (s₂.gpr (q j)).getLsbD 0 =
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
    have hregion : spillRegion s₁ = spillRegion s := by
      simp only [spillRegion, kept₁ .r2 (by decide)]
    rw [hregion, mem₁] at hf
    rw [mem₃]
    exact hf

end VG.Proof.TripleDes.Arm

end
