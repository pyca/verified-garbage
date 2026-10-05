import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.TaintErase

/-!
# Taint tracking for AArch64: code without its immediates and offsets

As `TaintErase.lean`, for every immediate the analysis (`Taint.step`) does not
read: those of `movz` and `movk`, the offsets of loads and stores, the
immediates of `add` and `sub`, and the amounts of shifts and rotations
(`Instr.eraseOff`). The field operations of a curve on different slots of a
working space differ only in their offsets: without them they are the same
code (proven once for any slots), and the kernel, which caches the analysis
of the same code from the same taint, analyses each once.
-/

namespace VG.AArch64

/-- The instruction with every immediate that `Taint.step` does not read zeroed. -/
def Instr.eraseOff : Instr → Instr
  | .movz sz d _ hw => .movz sz d 0 hw
  | .movk sz d _ hw => .movk sz d 0 hw
  | .ldr sz t n _ => .ldr sz t n 0
  | .str sz t n _ => .str sz t n 0
  | .ldrb t n _ => .ldrb t n 0
  | .strb t n _ => .strb t n 0
  | .addImm sz d n _ => .addImm sz d n 0
  | .subImm sz d n _ => .subImm sz d n 0
  | .lsl sz d n _ => .lsl sz d n 0
  | .lsr sz d n _ => .lsr sz d n 0
  | .ror sz d n _ => .ror sz d n 0
  | i => i

/-- The code with the immediates of its instructions erased (`Instr.eraseOff`). -/
def Code.eraseOff : Prog isa → Prog isa
  | .block is => .block (is.map Instr.eraseOff)
  | .seq a b => .seq (eraseOff a) (eraseOff b)
  | .ite c t e => .ite c (eraseOff t) (eraseOff e)
  | .loop b c => .loop (eraseOff b) c
  | .call n b => .call n (eraseOff b)
  | .frame p b q => .frame p (eraseOff b) q

namespace Taint

theorem step_eraseOff (τ : T) (i : Instr) : step τ i.eraseOff = step τ i := by
  cases i <;> rfl

theorem checkBlock_eraseOff (τ : taint.T) (is : List isa.Instr) :
    taint.checkBlock τ (is.map Instr.eraseOff) = taint.checkBlock τ is := by
  induction is generalizing τ with
  | nil => rfl
  | cons i is ih =>
    show (step τ i.eraseOff).bind _ = (step τ i).bind _
    exact congr (congrArg Option.bind (step_eraseOff τ i)) (funext ih)

theorem checkChunks_eraseOff {chunkSize : Nat} (τ : taint.T) (is : List isa.Instr) (ms : List taint.T) :
    taint.checkChunks chunkSize τ (is.map Instr.eraseOff) ms = taint.checkChunks chunkSize τ is ms := by
  induction ms generalizing τ is with
  | nil => exact checkBlock_eraseOff τ is
  | cons m ms ih =>
    simp only [VG.Taint.checkChunks, KList.take_eq, KList.drop_eq, ← List.map_take, ← List.map_drop, ih]
    exact congrArg (Option.bind · _) (checkBlock_eraseOff τ _)

theorem check_eraseOff (τ : taint.T) (c : Prog isa) (h : VG.Taint.Hint taint.T) :
    taint.check τ (Code.eraseOff c) h = taint.check τ c h := by
  induction c generalizing τ h with
  | block is => cases h <;> first | rfl | exact checkChunks_eraseOff τ is _
  | seq a b iha ihb =>
    cases h <;> first | rfl | simp only [Code.eraseOff, VG.Taint.check, iha, ihb]
  | ite c t e iht ihe =>
    cases h <;> first | rfl | simp only [Code.eraseOff, VG.Taint.check, iht, ihe]
  | loop b c ih => cases h <;> first | rfl | simp only [Code.eraseOff, VG.Taint.check, ih]
  | call n b ih => cases h <;> first | rfl | simp only [Code.eraseOff, VG.Taint.check, ih]
  | frame p b q ih => cases h <;> first | rfl | simp only [Code.eraseOff, VG.Taint.check, ih]

end Taint

/-- The analysis of `c` from that of `c'`, which is `c` without its immediates. -/
theorem Taint.isSome_check_of_eraseOff {c c' : Prog isa} (he : Code.eraseOff c = c')
    {τ : taint.T} {hc : VG.Taint.Hint taint.T} (h : (taint.check τ c' hc).isSome = true) :
    (taint.check τ c hc).isSome = true := by
  rw [← Taint.check_eraseOff, he]; exact h

/-- `allInstrs p` of the code without its immediates, for a `p` that does not read them. -/
theorem Code.allInstrs_eraseOff {p : Instr → Bool} (hp : ∀ i, p i.eraseOff = p i)
    (c : Prog isa) : (Code.eraseOff c).allInstrs p = c.allInstrs p := by
  induction c with
  | block is =>
    show Code.allInstrs p (.block (is.map Instr.eraseOff)) = Code.allInstrs p (.block is)
    rw [Code.allInstrs_eq, Code.allInstrs_eq]
    simp only [instrs, List.all_map, Function.comp_def, hp]
  | seq a b iha ihb => simp only [Code.eraseOff, Code.allInstrs, iha, ihb]
  | ite c t e iht ihe => simp only [Code.eraseOff, Code.allInstrs, iht, ihe]
  | loop b c ih => simp only [Code.eraseOff, Code.allInstrs, ih]
  | call n b ih => simp only [Code.eraseOff, Code.allInstrs, ih]
  | frame i b j ih => simp only [Code.eraseOff, Code.allInstrs, ih]

theorem keepsV_eraseOff (i : Instr) : keepsV i.eraseOff = keepsV i := by
  cases i <;> rfl

/-- `keepsV` of `c` from that of `c'`, which is `c` without its immediates. -/
theorem Code.allInstrs_keepsV_of_eraseOff {c c' : Prog isa} (he : Code.eraseOff c = c')
    (h : c'.allInstrs keepsV = true) : c.allInstrs keepsV = true := by
  rw [← Code.allInstrs_eraseOff keepsV_eraseOff, he]; exact h

/-- `keepsV` of `c` from that of `c'`, which is `c` up to immediates. -/
theorem Code.allInstrs_keepsV_of_eraseOff_eq {c c' : Prog isa}
    (he : Code.eraseOff c = Code.eraseOff c') (h : c'.allInstrs keepsV = true) :
    c.allInstrs keepsV = true := by
  rw [← Code.allInstrs_eraseOff keepsV_eraseOff, he, Code.allInstrs_eraseOff keepsV_eraseOff]
  exact h

/-- Whether code has no frames does not depend on its immediates. -/
theorem Code.noFrames_eraseOff (c : Prog isa) : (Code.eraseOff c).noFrames = c.noFrames := by
  induction c <;> simp_all [Code.eraseOff, Code.noFrames]

end VG.AArch64
