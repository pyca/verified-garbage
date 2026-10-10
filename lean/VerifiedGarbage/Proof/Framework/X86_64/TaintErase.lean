import VerifiedGarbage.Proof.Framework.TaintMap
import VerifiedGarbage.Proof.Framework.X86_64.TaintSym
import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.X86_64.KeepReg

/-!
# Taint tracking for x86-64: code without its displacements

The analysis reads a memory operand's displacement, and an immediate, only
to find the region and offset it addresses (`addrOfK`, from the known region
bases `bases`). From a taint that knows no region bases, and so never
learns one, it reads neither: `taint`, `taintS` and `taintSym L` check code
with its displacements and immediates zeroed (`Code.erase`) exactly as the
code itself (`taint_eraseInv`, …, with `Taint.MapInv.check`). Code that does
the same on different memory (field arithmetic on different slots of a
working space) is then the same code, whose analysis from the same taint
the kernel evaluates once (as in `Proof/Framework/X86/TaintErase.lean`).

`KeepReg.keeps` does not read them either (`KeepReg.keeps_erase`). Its
check passes on what it knows from block to block as a term to evaluate,
different at every block, so the kernel cannot tell that it checks the same
code from the same state: `KeepReg.keepsN` is the same check with that state
written out as a literal (in the common cases), whose checks of equal code
the kernel then evaluates once.
-/

namespace VG.X86_64

/-- The memory operand with its displacement zeroed. -/
def MemOp.erase (m : MemOp) : MemOp := { m with disp := 0 }

/-- The operand with its displacement or immediate zeroed. -/
def Src.erase : Src → Src
  | .mem m => .mem m.erase
  | .imm _ => .imm 0
  | .reg r => .reg r

/-- The instruction with its displacements and immediates zeroed (those of
the integer instructions). -/
def Instr.erase : Instr → Instr
  | .mov d s => .mov d s.erase
  | .mov32 d s => .mov32 d s.erase
  | .store m r => .store m.erase r
  | .store32 m r => .store32 m.erase r
  | .store8 m r => .store8 m.erase r
  | .alu op d s => .alu op d s.erase
  | .alu32 op d s => .alu32 op d s.erase
  | .movzx8 d m => .movzx8 d m.erase
  | .mulx hi lo s => .mulx hi lo s.erase
  | .adcx d s => .adcx d s.erase
  | .adox d s => .adox d s.erase
  | .cmov c d s => .cmov c d s.erase
  | i => i

/-- The code with its displacements and immediates zeroed (also in the
functions it calls). -/
abbrev Code.erase (c : Prog isa) : Prog isa := c.mapBlocks Instr.erase

theorem Code.erase_inline (c : Prog isa) : (Code.erase c).inline = Code.erase c.inline := by
  induction c with
  | block is => rfl
  | seq a b iha ihb => show Code.seq _ _ = Code.seq _ _; rw [iha, ihb]
  | ite c t e iht ihe => show Code.ite c _ _ = Code.ite c _ _; rw [iht, ihe]
  | loop b c ih => exact congrArg (Code.loop · c) ih
  | call n b _ => rfl
  | frame i b j ih => exact congrArg (Code.frame i · j) ih

namespace Taint

section
variable {τ : T}

theorem addrOfK_nil (h : τ.bases = []) (m : MemOp) : addrOfK τ m = none := by
  unfold addrOfK; split <;> simp only [h] <;> rfl

theorem killK_nil (h : τ.bases = []) (d : Reg) : killK τ d = [] := by
  unfold killK; rw [h]; rfl

theorem memPub_erase (m : MemOp) : memPub τ m.erase = memPub τ m := rfl

theorem srcOkK_erase (s : Src) : srcOkK τ s.erase = srcOkK τ s := by
  cases s <;> rfl

theorem srcPub_erase (s : Src) : srcPub τ s.erase = srcPub τ s := by
  cases s <;> rfl

theorem loPub_erase (s : Src) : loPub τ s.erase = loPub τ s := by
  cases s <;> rfl

theorem loadPubK_erase (h : τ.bases = []) (w : Nat) (s : Src) : loadPubK τ w s.erase = loadPubK τ w s := by
  cases s with
  | mem m => simp only [Src.erase, loadPubK, slotPubK, addrOfK_nil h]
  | _ => rfl

theorem movBasesK_erase (d : Reg) (s : Src) : movBasesK τ d s.erase = movBasesK τ d s := by
  cases s <;> rfl

theorem aluBasesK_nil (h : τ.bases = []) (op : AluOp) (d : Reg) (s : Src) (wide : Bool) :
    aluBasesK τ op d s wide = [] := by
  unfold aluBasesK
  split <;> simp only [killK_nil h, h] <;> cases (wide && !_) <;> rfl

theorem storeStepKD_erase (h : τ.bases = []) (m : MemOp) (w : Nat) (p : Bool) :
    storeStepKD τ m.erase w p = storeStepKD τ m w p := by
  simp only [storeStepKD, storeSlotsKD, addrOfK_nil h, memPub_erase]

theorem aluStepK_erase (h : τ.bases = []) (op : AluOp) (d : Reg) (s : Src) (wide : Bool) :
    aluStepK τ op d s.erase wide = aluStepK τ op d s wide := by
  simp only [aluStepK, srcOkK_erase, srcPub_erase, aluBasesK_nil h]

theorem stepKD_erase (h : τ.bases = []) (i : Instr) : stepKD τ i.erase = stepKD τ i := by
  cases i with
  | mov d s => simp only [Instr.erase, stepKD, stepKDFn, srcOkK_erase, srcPub_erase, loadPubK_erase h,
      movBasesK_erase]
  | mov32 d s => simp only [Instr.erase, stepKD, stepKDFn, srcOkK_erase, srcPub_erase, loadPubK_erase h,
      loPub_erase]
  | store m r => simp only [Instr.erase, stepKD, stepKDFn, storeStepKD_erase h]
  | store32 m r => simp only [Instr.erase, stepKD, stepKDFn, storeStepKD_erase h]
  | store8 m r => simp only [Instr.erase, stepKD, stepKDFn, storeStepKD_erase h]
  | alu op d s => simp only [Instr.erase, stepKD, stepKDFn, aluStepK_erase h]
  | alu32 op d s => simp only [Instr.erase, stepKD, stepKDFn, aluStepK_erase h]
  | movzx8 d m => rfl
  | mulx hi lo s => simp only [Instr.erase, stepKD, stepKDFn, mulxStepK, srcOkK_erase, srcPub_erase]
  | adcx d s => simp only [Instr.erase, stepKD, stepKDFn, adxStepK, srcOkK_erase, srcPub_erase]
  | adox d s => simp only [Instr.erase, stepKD, stepKDFn, adxStepK, srcOkK_erase, srcPub_erase]
  | cmov c d s => simp only [Instr.erase, stepKD, stepKDFn, cmovStepK, srcOkK_erase, srcPub_erase,
      loadPubK_erase h]
  | _ => rfl

theorem some_cond {b : Bool} {x τ' : T} (hs : (bif b then some x else none) = some τ') :
    b = true ∧ x = τ' := by
  cases b
  · cases hs
  · exact ⟨rfl, Option.some.inj hs⟩

theorem storeStepK_nil (h : τ.bases = []) {m : MemOp} {w : Nat} {p : Bool} {τ' : T}
    (hs : storeStepK τ m w p = some τ') : τ'.bases = [] := by
  obtain ⟨-, rfl⟩ := some_cond hs; exact h

theorem storeStepKD_nil (h : τ.bases = []) {m : MemOp} {w : Nat} {p : Bool} {τ' : T}
    (hs : storeStepKD τ m w p = some τ') : τ'.bases = [] := by
  obtain ⟨-, rfl⟩ := some_cond hs; exact h

theorem stepKD_nil (h : τ.bases = []) {i : Instr} {τ' : T} (hs : stepKD τ i = some τ') :
    τ'.bases = [] := by
  have k := killK_nil h
  have nx : (noX τ).bases = [] := h
  cases i with
  | mov d s =>
    obtain ⟨-, rfl⟩ := some_cond hs
    show movBasesK τ d s = []
    cases s with
    | reg r => show KList.append _ _ = []; rw [k, h]; rfl
    | _ => exact k d
  | mov32 d s => obtain ⟨-, rfl⟩ := some_cond hs; exact k d
  | store m r => exact storeStepKD_nil h hs
  | store32 m r => exact storeStepKD_nil h hs
  | store8 m r => exact storeStepKD_nil h hs
  | alu op d s => obtain ⟨-, rfl⟩ := some_cond hs; exact aluBasesK_nil h ..
  | alu32 op d s => obtain ⟨-, rfl⟩ := some_cond hs; exact aluBasesK_nil h ..
  | shift32 _ d _ => cases hs; exact k d
  | shift _ d _ => cases hs; exact k d
  | bswap32 d => cases hs; exact k d
  | bswap d => cases hs; exact k d
  | rorx32 d _ _ => cases hs; exact k d
  | rorx d _ _ => cases hs; exact k d
  | andn32 d _ _ => cases hs; exact k d
  | andn d _ _ => cases hs; exact k d
  | imul d _ => cases hs; exact k d
  | movImm64 d _ => cases hs; exact k d
  | leaSym d _ => cases hs; exact k d
  | movzx8 d m => obtain ⟨-, rfl⟩ := some_cond hs; exact k d
  | vpmovmskb _ d _ => cases hs; exact k d
  | movqR d _ => cases hs; exact k d
  | movdquLoad _ m => obtain ⟨-, rfl⟩ := some_cond hs; exact nx
  | movdquStore m _ => exact storeStepK_nil h hs
  | xop op => cases op <;> (cases hs; exact h)
  | vop _ => cases hs; exact nx
  | vmovdquLoad _ _ m => obtain ⟨-, rfl⟩ := some_cond hs; exact nx
  | vbroadcasti128 _ m => obtain ⟨-, rfl⟩ := some_cond hs; exact nx
  | vbinLoad _ _ _ _ m => obtain ⟨-, rfl⟩ := some_cond hs; exact nx
  | vmovdquStore l m _ => cases l <;> exact storeStepK_nil h hs
  | zop _ => cases hs; exact nx
  | vmovdqu32Load _ m => obtain ⟨-, rfl⟩ := some_cond hs; exact nx
  | vbroadcasti32x4 _ m => obtain ⟨-, rfl⟩ := some_cond hs; exact nx
  | vbroadcasti32x4H _ m => obtain ⟨-, rfl⟩ := some_cond hs; exact nx
  | zbcst _ _ _ m => obtain ⟨-, rfl⟩ := some_cond hs; exact nx
  | vpmadd52Load _ _ _ m => obtain ⟨-, rfl⟩ := some_cond hs; exact nx
  | vmovdqu32Store m _ => exact storeStepK_nil h hs
  | eop _ => cases hs; exact nx
  | evLoad _ m => obtain ⟨-, rfl⟩ := some_cond hs; exact nx
  | evMadd52Load _ _ _ m => obtain ⟨-, rfl⟩ := some_cond hs; exact nx
  | evStore m _ => exact storeStepK_nil h hs
  | stmxcsr m => exact storeStepK_nil h hs
  | ldmxcsr m => obtain ⟨-, rfl⟩ := some_cond hs; exact h
  | lfence => cases hs; exact h
  | mul r => cases hs; simp only [mulStep, kill, h, List.filter_nil]
  | mulx hi lo s =>
    obtain ⟨-, rfl⟩ := some_cond hs
    show KList.filter _ (killK τ hi) = []; rw [k]; rfl
  | adcx d s => obtain ⟨-, rfl⟩ := some_cond hs; exact k d
  | adox d s => obtain ⟨-, rfl⟩ := some_cond hs; exact k d
  | cmov _ d s => obtain ⟨-, rfl⟩ := some_cond hs; exact k d
  | push _ => cases hs
  | pop _ _ => cases hs
  | alloc _ => cases hs
  | free _ => cases hs

theorem leK_nil (h : τ.bases = []) {m : T} (hl : leK m τ = true) : m.bases = [] := by
  rw [leK_eq] at hl
  have hb : m.bases.all (τ.bases.contains ·) = true := by
    simp only [le, Bool.and_eq_true] at hl; exact hl.1.1.1.2
  rw [h] at hb
  cases e : m.bases with
  | nil => rfl
  | cons x _ => rw [e] at hb; cases hb

theorem leS_nil (h : τ.bases = []) {m : T} (hl : leS m τ = true) : m.bases = [] := by
  have hb : KList.all m.bases (memB · τ.bases) = true := by
    simp only [leS, Bool.and_eq_true] at hl; exact hl.1.1.1.1.2
  rw [h] at hb
  cases e : m.bases with
  | nil => rfl
  | cons x _ => rw [e] at hb; cases hb

theorem meet_nil {τ₁ τ₂ : T} (h : τ₁.bases = []) : (meet τ₁ τ₂).bases = [] := by
  simp only [meet, h, List.filter_nil]

theorem callStep_nil (h : τ.bases = []) {τ' : T} (hs : callStep τ = some τ') : τ'.bases = [] := by
  unfold callStep at hs
  split at hs <;> [skip; cases hs]
  cases hs; simp only [kill, h, List.filter_nil]

theorem retStep_nil (h : τ.bases = []) {τ' : T} (hs : retStep τ = some τ') : τ'.bases = [] := by
  unfold retStep at hs
  split at hs <;> [skip; cases hs]
  cases hs; simp only [kill, h, List.filter_nil]

end

end Taint

/-- `taint` does not read displacements and immediates, from a taint that
knows no region bases. -/
theorem taint_eraseInv : taint.MapInv Instr.erase (fun τ : Taint.T => τ.bases = []) where
  step i h := Taint.stepKD_erase h i
  step_P _ h hs := Taint.stepKD_nil h hs
  le_P h hl := Taint.leK_nil h hl
  meet_P h := Taint.meet_nil h
  call_P h hs := Taint.callStep_nil h hs
  ret_P h hs := Taint.retStep_nil h hs
  push_P _ _ hs := by cases hs
  pop_P _ _ hs := by cases hs

/-- `taintS` does not read displacements and immediates, from a taint that
knows no region bases. -/
theorem taintS_eraseInv : taintS.MapInv Instr.erase (fun τ : Taint.T => τ.bases = []) where
  step i h := Taint.stepKD_erase h i
  step_P _ h hs := Taint.stepKD_nil h hs
  le_P h hl := Taint.leS_nil h hl
  meet_P h := Taint.meet_nil h
  call_P h hs := Taint.callStep_nil h hs
  ret_P h hs := Taint.retStep_nil h hs
  push_P _ _ hs := by cases hs
  pop_P _ _ hs := by cases hs

theorem Instr.symMov_erase (L : List String) (i : Instr) : i.erase.symMov L = (i.symMov L).erase := by
  cases i <;> try rfl
  rename_i d n
  show (if n ∈ L then _ else _) = Instr.erase (if n ∈ L then _ else _)
  split <;> rfl

/-- `taintSym L` does not read displacements and immediates, from a taint
that knows no region bases. -/
theorem taintSym_eraseInv (L : List String) :
    (taintSym L).MapInv Instr.erase (fun τ : Taint.T => τ.bases = []) where
  step i h := by
    show Taint.stepKD _ (i.erase.symMov L) = Taint.stepKD _ (i.symMov L)
    rw [Instr.symMov_erase]; exact Taint.stepKD_erase h _
  step_P _ h hs := Taint.stepKD_nil h hs
  le_P h hl := Taint.leS_nil h hl
  meet_P h := Taint.meet_nil h
  call_P h hs := Taint.callStep_nil h hs
  ret_P h hs := Taint.retStep_nil h hs
  push_P _ _ hs := by cases hs
  pop_P _ _ hs := by cases hs

namespace KeepReg

theorem step_erase (r : Reg) (a : Abs) (i : Instr) : step r a i.erase = step r a i := by
  cases i <;> rfl

theorem run_erase (r : Reg) (is : List Instr) :
    ∀ ok xs, run r (KList.map Instr.erase is) ok xs = run r is ok xs := by
  induction is with
  | nil => intro _ _; rfl
  | cons i is ih =>
    intro ok xs
    show (bif ok then (bif Nat.beq xs 0 then run r (KList.map Instr.erase is) (step r ⟨true, ⟨0⟩⟩ i.erase).ok
          (step r ⟨true, ⟨0⟩⟩ i.erase).xs.bits
        else run r (KList.map Instr.erase is) (step r ⟨true, ⟨xs⟩⟩ i.erase).ok (step r ⟨true, ⟨xs⟩⟩ i.erase).xs.bits)
      else (bif Nat.beq xs 0 then run r (KList.map Instr.erase is) (step r ⟨false, ⟨0⟩⟩ i.erase).ok
          (step r ⟨false, ⟨0⟩⟩ i.erase).xs.bits
        else run r (KList.map Instr.erase is) (step r ⟨false, ⟨xs⟩⟩ i.erase).ok
          (step r ⟨false, ⟨xs⟩⟩ i.erase).xs.bits)) =
      (bif ok then (bif Nat.beq xs 0 then run r is (step r ⟨true, ⟨0⟩⟩ i).ok (step r ⟨true, ⟨0⟩⟩ i).xs.bits
        else run r is (step r ⟨true, ⟨xs⟩⟩ i).ok (step r ⟨true, ⟨xs⟩⟩ i).xs.bits)
      else (bif Nat.beq xs 0 then run r is (step r ⟨false, ⟨0⟩⟩ i).ok (step r ⟨false, ⟨0⟩⟩ i).xs.bits
        else run r is (step r ⟨false, ⟨xs⟩⟩ i).ok (step r ⟨false, ⟨xs⟩⟩ i).xs.bits))
    simp only [step_erase, ih]

theorem check_erase (r : Reg) (c : Prog isa) : ∀ a, check r (Code.erase c) a = check r c a := by
  induction c with
  | block is => intro a; exact congrArg some (run_erase r is a.ok a.xs.bits)
  | seq c d ihc ihd =>
    intro a
    show (check r (Code.erase c) a).bind (check r (Code.erase d)) = (check r c a).bind (check r d)
    rw [ihc]; exact congrArg _ (funext ihd)
  | ite _ c d ihc ihd =>
    intro a
    show (check r (Code.erase c) a).bind (fun x => (check r (Code.erase d) a).map (meet x)) =
      (check r c a).bind (fun x => (check r d a).map (meet x))
    rw [ihc, ihd]
  | loop b _ ih =>
    intro a
    show (check r (Code.erase b) a).bind _ = (check r b a).bind _
    rw [ih]
  | call _ _ _ => intro _; rfl
  | frame _ _ _ _ => intro _; rfl

/-- `keeps` does not read displacements and immediates. -/
theorem keeps_erase (r : Reg) (c : Prog isa) : keeps r (Code.erase c) = keeps r c := by
  unfold keeps; rw [check_erase]

/-- `a`, written out as a literal if `r` holds its value and is in no SSE
register or only in `xmm0` (as after a field function's call, which saves it
there): the kernel then evaluates the check of the same code from it once
(`checkN`), where `run` would leave a term to evaluate, different at every
block. -/
def Abs.norm (a : Abs) : Abs :=
  bif a.ok then (bif Nat.beq a.xs.bits 0 then ⟨true, ⟨0⟩⟩ else bif Nat.beq a.xs.bits 1 then ⟨true, ⟨1⟩⟩ else a)
  else (bif Nat.beq a.xs.bits 0 then ⟨false, ⟨0⟩⟩ else bif Nat.beq a.xs.bits 1 then ⟨false, ⟨1⟩⟩ else a)

theorem Abs.norm_eq (a : Abs) : a.norm = a := by
  obtain ⟨ok, ⟨xs⟩⟩ := a
  show (bif ok then (bif Nat.beq xs 0 then _ else bif Nat.beq xs 1 then _ else _)
    else (bif Nat.beq xs 0 then _ else bif Nat.beq xs 1 then _ else _)) = _
  cases h₀ : Nat.beq xs 0
  · cases h₁ : Nat.beq xs 1
    · cases ok <;> rfl
    · rw [Nat.eq_of_beq_eq_true h₁]; cases ok <;> rfl
  · rw [Nat.eq_of_beq_eq_true h₀]; cases ok <;> rfl

/-- `run`, with what is known written out before every instruction if `r`
is in `xmm0` alone, as well as in no SSE register. -/
def runN (r : Reg) (is : List Instr) : Bool → Nat → Abs :=
  List.rec (fun ok xs => ⟨ok, ⟨xs⟩⟩)
    (fun i _ ih ok xs =>
      let g := fun a : Abs => ih a.ok a.xs.bits
      bif ok then (bif Nat.beq xs 0 then g (step r ⟨true, ⟨0⟩⟩ i)
        else bif Nat.beq xs 1 then g (step r ⟨true, ⟨1⟩⟩ i) else g (step r ⟨true, ⟨xs⟩⟩ i))
      else (bif Nat.beq xs 0 then g (step r ⟨false, ⟨0⟩⟩ i)
        else bif Nat.beq xs 1 then g (step r ⟨false, ⟨1⟩⟩ i) else g (step r ⟨false, ⟨xs⟩⟩ i))) is

theorem runN_eq (r : Reg) (is : List Instr) : ∀ ok xs, runN r is ok xs = run r is ok xs := by
  induction is with
  | nil => intro _ _; rfl
  | cons i is ih =>
    intro ok xs
    show (bif ok then (bif Nat.beq xs 0 then runN r is (step r ⟨true, ⟨0⟩⟩ i).ok (step r ⟨true, ⟨0⟩⟩ i).xs.bits
          else bif Nat.beq xs 1 then runN r is (step r ⟨true, ⟨1⟩⟩ i).ok (step r ⟨true, ⟨1⟩⟩ i).xs.bits
          else runN r is (step r ⟨true, ⟨xs⟩⟩ i).ok (step r ⟨true, ⟨xs⟩⟩ i).xs.bits)
        else (bif Nat.beq xs 0 then runN r is (step r ⟨false, ⟨0⟩⟩ i).ok (step r ⟨false, ⟨0⟩⟩ i).xs.bits
          else bif Nat.beq xs 1 then runN r is (step r ⟨false, ⟨1⟩⟩ i).ok (step r ⟨false, ⟨1⟩⟩ i).xs.bits
          else runN r is (step r ⟨false, ⟨xs⟩⟩ i).ok (step r ⟨false, ⟨xs⟩⟩ i).xs.bits)) =
      (bif ok then (bif Nat.beq xs 0 then run r is (step r ⟨true, ⟨0⟩⟩ i).ok (step r ⟨true, ⟨0⟩⟩ i).xs.bits
          else run r is (step r ⟨true, ⟨xs⟩⟩ i).ok (step r ⟨true, ⟨xs⟩⟩ i).xs.bits)
        else (bif Nat.beq xs 0 then run r is (step r ⟨false, ⟨0⟩⟩ i).ok (step r ⟨false, ⟨0⟩⟩ i).xs.bits
          else run r is (step r ⟨false, ⟨xs⟩⟩ i).ok (step r ⟨false, ⟨xs⟩⟩ i).xs.bits))
    simp only [ih]
    cases ok <;> cases h₀ : Nat.beq xs 0 <;> cases h₁ : Nat.beq xs 1 <;>
      simp only [Bool.cond_true, Bool.cond_false] <;> rw [Nat.eq_of_beq_eq_true h₁]

/-- `check`, with what is known written out after every block and branch (`Abs.norm`). -/
def checkN (r : Reg) : Prog isa → Abs → Option Abs
  | .block is, a => some (runN r is a.ok a.xs.bits).norm
  | .seq c d, a => (checkN r c a).bind (checkN r d)
  | .ite _ c d, a => (checkN r c a).bind fun x => (checkN r d a).map fun y => (meet x y).norm
  | .loop b _, a => (checkN r b a).bind fun x => bif le a x then some a else none
  | .call .., _ => none
  | .frame .., _ => none

theorem checkN_eq (r : Reg) (c : Prog isa) : ∀ a, checkN r c a = check r c a := by
  induction c with
  | block is => intro a; exact congrArg some ((Abs.norm_eq _).trans (runN_eq r is _ _))
  | seq c d ihc ihd =>
    intro a
    show (checkN r c a).bind (checkN r d) = (check r c a).bind (check r d)
    rw [ihc]; exact congrArg _ (funext ihd)
  | ite _ c d ihc ihd =>
    intro a
    show (checkN r c a).bind (fun x => (checkN r d a).map fun y => (meet x y).norm) =
      (check r c a).bind (fun x => (check r d a).map (meet x))
    simp only [ihc, ihd, Abs.norm_eq]
  | loop b _ ih =>
    intro a
    show (checkN r b a).bind _ = (check r b a).bind _
    rw [ih]
  | call _ _ _ => intro _; rfl
  | frame _ _ _ _ => intro _; rfl

/-- `keeps` by `checkN`. -/
def keepsN (r : Reg) (c : Prog isa) : Bool :=
  match checkN r c ⟨true, ⟨0⟩⟩ with
  | some a => a.ok
  | none => false

theorem keepsN_eq (r : Reg) (c : Prog isa) : keepsN r c = keeps r c := by
  unfold keepsN keeps; rw [checkN_eq]; rfl

end KeepReg

end VG.X86_64
