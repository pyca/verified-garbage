import VerifiedGarbage.Proof.Framework.X86.Taint

/-!
# Taint tracking for x86 (32-bit): code without its displacements

The analysis reads a memory operand's displacement only to find the region
and offset it addresses (`addrOfK`, from the known region bases `bases`) or
the argument it reads (at `esp`). From a taint that knows no region bases
(and no argument that holds one, `argBases`), and so never learns one, it
reads neither but at `esp`, nor any immediate: it checks code with those
displacements and the immediates zeroed (`Code.erase`) exactly as the code
itself (`check_erase`). Code that does the same on different memory (field
arithmetic on different slots of a working space) is then the same code,
which the kernel analyses once from the same taint.
-/

namespace VG.X86

/-- The memory operand with its displacement zeroed, but at `esp`. -/
def MemOp.erase (m : MemOp) : MemOp := bif Taint.regEq m.base .esp then m else { base := m.base }

/-- The operand with its displacement or immediate zeroed. -/
def Src.erase : Src → Src
  | .mem m => .mem m.erase
  | .imm _ => .imm 0
  | .reg r => .reg r

/-- The instruction with its displacements (but at `esp`) and immediates zeroed. -/
def Instr.erase : Instr → Instr
  | .mov d s => .mov d s.erase
  | .store m r => .store m.erase r
  | .alu op d s => .alu op d s.erase
  | .movzx8 d m => .movzx8 d m.erase
  | .store8 m r => .store8 m.erase r
  | i => i

/-- The code with its displacements (but at `esp`) and immediates zeroed,
outside calls and frames. -/
def Code.erase : Prog isa → Prog isa
  | .block is => .block (KList.map Instr.erase is)
  | .seq a b => .seq (erase a) (erase b)
  | .ite c t e => .ite c (erase t) (erase e)
  | .loop b c => .loop (erase b) c
  | .call n b => .call n b
  | .frame p b q => .frame p b q

namespace Taint

/-- No region base is known, nor any argument that holds one. -/
def noBases (τ : T) : Bool := τ.bases.isEmpty && τ.argBases.isEmpty

/-- Every taint of the hint knows no region base. -/
def hintNoBases : VG.Taint.Hint T → Bool
  | .block ms _ => ms.all noBases
  | .seq m h₁ h₂ => noBases m && hintNoBases h₁ && hintNoBases h₂
  | .ite h₁ h₂ => hintNoBases h₁ && hintNoBases h₂
  | .loop σ h => noBases σ && hintNoBases h
  | .call _ => true
  | .frame _ => true

section
variable {τ : T}

theorem noBases_iff : noBases τ = true ↔ τ.bases = [] ∧ τ.argBases = [] := by
  simp only [noBases, Bool.and_eq_true, List.isEmpty_iff]

theorem MemOp.erase_base (m : MemOp) : m.erase.base = m.base := by
  unfold MemOp.erase; cases regEq m.base .esp <;> rfl

theorem addrOfK_nil (h : τ.bases = []) (m : MemOp) : addrOfK τ m = none := by
  unfold addrOfK; rw [h]; rfl

theorem loadBasesK_nil (h : τ.bases = []) (ha : τ.argBases = []) (m : MemOp) : loadBasesK τ m = [] := by
  unfold loadBasesK; rw [addrOfK_nil h, ha]; cases regEq m.base .esp <;> rfl

theorem argPubK_erase (m : MemOp) (w : Nat) : argPubK τ m.erase w = argPubK τ m w := by
  unfold argPubK MemOp.erase
  cases hm : regEq m.base .esp <;> simp only [Bool.cond_true, Bool.cond_false, hm, Bool.false_and]

theorem srcOkK_erase (s : Src) : srcOkK τ s.erase = srcOkK τ s := by
  cases s <;> simp only [Src.erase, srcOkK, MemOp.erase_base]

theorem srcPub_erase (s : Src) : srcPub τ s.erase = srcPub τ s := by
  cases s <;> rfl

theorem loadPubK_erase (h : τ.bases = []) (s : Src) : loadPubK τ s.erase = loadPubK τ s := by
  cases s with
  | mem m => simp only [Src.erase, loadPubK, slotPubK, addrOfK_nil h, argPubK_erase]
  | _ => rfl

theorem movBasesK_erase (h : τ.bases = []) (ha : τ.argBases = []) (d : Reg) (s : Src) :
    movBasesK τ d s.erase = movBasesK τ d s := by
  cases s with
  | mem m => simp only [Src.erase, movBasesK, loadBasesK_nil h ha]
  | _ => rfl

theorem storeStepKD_erase (h : τ.bases = []) (m : MemOp) (w : Nat) (p : Bool) (nb : List Nat) :
    storeStepKD τ m.erase w p nb = storeStepKD τ m w p nb := by
  simp only [storeStepKD, storeSlotsKD, storeWbasesKD, addrOfK_nil h, MemOp.erase_base]

theorem stepKD_erase (h : τ.bases = []) (ha : τ.argBases = []) (i : Instr) :
    stepKD τ i.erase = stepKD τ i := by
  cases i with
  | mov d s => simp only [Instr.erase, stepKD, stepKDFn, srcOkK_erase, srcPub_erase, loadPubK_erase h,
      movBasesK_erase h ha]
  | store m r => simp only [Instr.erase, stepKD, stepKDFn, storeStepKD_erase h]
  | alu op d s => simp only [Instr.erase, stepKD, stepKDFn, srcOkK_erase, srcPub_erase]
  | movzx8 d m => simp only [Instr.erase, stepKD, stepKDFn, MemOp.erase_base]
  | store8 m r => simp only [Instr.erase, stepKD, stepKDFn, storeStepKD_erase h]
  | _ => rfl

theorem killK_nil (h : τ.bases = []) (d : Reg) : killK τ d = [] := by
  unfold killK; rw [h]; rfl

theorem some_cond {b : Bool} {x τ' : T} (hs : (bif b then some x else none) = some τ') :
    b = true ∧ x = τ' := by
  cases b
  · cases hs
  · exact ⟨rfl, Option.some.inj hs⟩

theorem stepKD_noBases (hn : noBases τ = true) {i : Instr} {τ' : T} (hs : stepKD τ i = some τ') :
    noBases τ' = true := by
  obtain ⟨h, ha⟩ := noBases_iff.mp hn
  have st : ∀ {m w p nb}, storeStepKD τ m w p nb = some τ' → noBases τ' = true := by
    intro m w p nb hs
    obtain ⟨-, rfl⟩ := some_cond hs
    exact noBases_iff.mpr ⟨h, ha⟩
  cases i with
  | mov d s =>
    obtain ⟨-, rfl⟩ := some_cond hs
    refine noBases_iff.mpr ⟨?_, ha⟩
    cases s with
    | mem m => show KList.append _ _ = []; rw [killK_nil h, loadBasesK_nil h ha]; rfl
    | reg r => show KList.append _ _ = []; rw [killK_nil h, h]; rfl
    | imm _ => exact killK_nil h d
  | store m r => exact st hs
  | alu op d s =>
    obtain ⟨-, rfl⟩ := some_cond hs
    exact noBases_iff.mpr ⟨killK_nil h d, ha⟩
  | shift op d n =>
    obtain ⟨-, rfl⟩ := some_cond hs
    exact noBases_iff.mpr ⟨killK_nil h d, ha⟩
  | bswap d =>
    obtain ⟨-, rfl⟩ := some_cond hs
    exact noBases_iff.mpr ⟨killK_nil h d, ha⟩
  | movzx8 d m =>
    obtain ⟨-, rfl⟩ := some_cond hs
    exact noBases_iff.mpr ⟨killK_nil h d, ha⟩
  | store8 m r => exact st hs
  | mul r =>
    cases hs
    refine noBases_iff.mpr ⟨?_, ha⟩
    simp only [mulStepKD_eq, mulStep, kill, h, List.filter_nil]
  | _ => cases hs

end

theorem checkBlock_erase (is : List Instr) :
    ∀ τ : T, noBases τ = true → taint.checkBlock τ (KList.map Instr.erase is) = taint.checkBlock τ is := by
  induction is with
  | nil => intro _ _; rfl
  | cons i is ih =>
    intro τ hn
    obtain ⟨h, ha⟩ := noBases_iff.mp hn
    show (stepKD τ i.erase).bind (taint.checkBlock · (KList.map Instr.erase is)) =
      (stepKD τ i).bind (taint.checkBlock · is)
    rw [stepKD_erase h ha]
    cases e : stepKD τ i with
    | none => rfl
    | some τ' => exact ih τ' (stepKD_noBases hn e)

theorem map_take (is : List Instr) (n : Nat) :
    (KList.map Instr.erase is).take n = KList.map Instr.erase (is.take n) := by
  rw [KList.map_eq, KList.map_eq, List.map_take]

theorem map_drop (is : List Instr) (n : Nat) :
    (KList.map Instr.erase is).drop n = KList.map Instr.erase (is.drop n) := by
  rw [KList.map_eq, KList.map_eq, List.map_drop]

theorem checkChunks_erase {chunkSize : Nat} (ms : List T) :
    ∀ (τ : T) (is : List Instr), noBases τ = true → ms.all noBases = true →
      taint.checkChunks chunkSize τ (KList.map Instr.erase is) ms = taint.checkChunks chunkSize τ is ms := by
  induction ms with
  | nil => intro τ is hn _; exact checkBlock_erase is τ hn
  | cons m ms ih =>
    intro τ is hn hms
    simp only [List.all_cons, Bool.and_eq_true] at hms
    simp only [VG.Taint.checkChunks, KList.take_eq, KList.drop_eq, map_take, map_drop, checkBlock_erase _ τ hn]
    cases taint.checkBlock τ (is.take chunkSize) with
    | none => rfl
    | some τ' =>
      simp only [Option.bind_some]
      split
      · exact ih m _ hms.1 hms.2
      · rfl

theorem meet_noBases {τ₁ τ₂ : T} (h₁ : noBases τ₁ = true) : noBases (meet τ₁ τ₂) = true := by
  obtain ⟨h, ha⟩ := noBases_iff.mp h₁
  refine noBases_iff.mpr ⟨?_, ?_⟩
  · simp only [meet, h, List.filter_nil]
  · simp only [meet, ha, List.filter_nil, ite_self]

/-- The analysis of the code without its displacements and immediates is the
analysis of the code, from a taint that knows no region bases, with a hint
whose taints know none either. -/
theorem check_erase (c : Prog isa) :
    ∀ (τ : T) (h : VG.Taint.Hint T), noBases τ = true → hintNoBases h = true →
      taint.check τ (Code.erase c) h = taint.check τ c h := by
  induction c with
  | block is =>
    intro τ h hn hh
    cases h with
    | block ms chunkSize => exact checkChunks_erase ms τ is hn hh
    | _ => rfl
  | seq a b iha ihb =>
    intro τ h hn hh
    cases h with
    | seq mid h₁ h₂ =>
      simp only [hintNoBases, Bool.and_eq_true] at hh
      show (taint.check τ (Code.erase a) h₁).bind _ = (taint.check τ a h₁).bind _
      rw [iha τ h₁ hn hh.1.2, ihb mid h₂ hh.1.1 hh.2]
    | _ => rfl
  | ite c t e iht ihe =>
    intro τ h hn hh
    cases h with
    | ite h₁ h₂ =>
      simp only [hintNoBases, Bool.and_eq_true] at hh
      show (if taint.condPub τ c then _ else none) = (if taint.condPub τ c then _ else none)
      rw [iht τ h₁ hn hh.1, ihe τ h₂ hn hh.2]
    | _ => rfl
  | loop b c ih =>
    intro τ h hn hh
    cases h with
    | loop σ h =>
      simp only [hintNoBases, Bool.and_eq_true] at hh
      show (if taint.le σ τ then _ else none) = (if taint.le σ τ then _ else none)
      rw [ih σ h hh.1 hh.2]
    | _ => rfl
  | call n b _ => intro τ h _ _; rfl
  | frame p b q _ => intro τ h _ _; rfl

end Taint

end VG.X86
