import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-!
# Taint tracking for AArch64: code without its immediates

The analysis (`Taint.step`) does not read the immediates of `movz` and `movk`:
it checks code with them zeroed (`Code.eraseImm`) exactly as the code itself
(`check_eraseImm`). Code that builds constants from immediates (e.g. a
selection from tables of points) then has its analysis checked on code whose
copies differ only in those immediates, and are now equal
(`constantTime_eraseImm_of_eq`, with that equality proven once for any
immediates): the kernel builds none of the immediates, and evaluates the
analysis of equal copies from the same taint once.
-/

namespace VG.AArch64

/-- The instruction with the immediate of a `movz` or `movk` zeroed. -/
def Instr.eraseImm : Instr → Instr
  | .movz sz d _ hw => .movz sz d 0 hw
  | .movk sz d _ hw => .movk sz d 0 hw
  | i => i

/-- The code with the immediates of its `movz` and `movk` zeroed. -/
def Code.eraseImm : Prog isa → Prog isa
  | .block is => .block (is.map Instr.eraseImm)
  | .seq a b => .seq (eraseImm a) (eraseImm b)
  | .ite c t e => .ite c (eraseImm t) (eraseImm e)
  | .loop b c => .loop (eraseImm b) c
  | .call n b => .call n (eraseImm b)
  | .frame p b q => .frame p (eraseImm b) q

namespace Taint

theorem step_eraseImm (τ : T) (i : Instr) : step τ i.eraseImm = step τ i := by
  cases i <;> rfl

theorem checkBlock_eraseImm (τ : taint.T) (is : List isa.Instr) :
    taint.checkBlock τ (is.map Instr.eraseImm) = taint.checkBlock τ is := by
  induction is generalizing τ with
  | nil => rfl
  | cons i is ih =>
    show (step τ i.eraseImm).bind _ = (step τ i).bind _
    exact congr (congrArg Option.bind (step_eraseImm τ i)) (funext ih)

theorem checkChunks_eraseImm (τ : taint.T) (is : List isa.Instr) (ms : List taint.T) :
    taint.checkChunks τ (is.map Instr.eraseImm) ms = taint.checkChunks τ is ms := by
  induction ms generalizing τ is with
  | nil => exact checkBlock_eraseImm τ is
  | cons m ms ih =>
    simp only [VG.Taint.checkChunks, ← List.map_take, ← List.map_drop, ih]
    exact congrArg (Option.bind · _) (checkBlock_eraseImm τ _)

theorem check_eraseImm (τ : taint.T) (c : Prog isa) (h : VG.Taint.Hint taint.T) :
    taint.check τ (Code.eraseImm c) h = taint.check τ c h := by
  induction c generalizing τ h with
  | block is => cases h <;> first | rfl | exact checkChunks_eraseImm τ is _
  | seq a b iha ihb =>
    cases h <;> first | rfl | simp only [Code.eraseImm, VG.Taint.check, iha, ihb]
  | ite c t e iht ihe =>
    cases h <;> first | rfl | simp only [Code.eraseImm, VG.Taint.check, iht, ihe]
  | loop b c ih => cases h <;> first | rfl | simp only [Code.eraseImm, VG.Taint.check, ih]
  | call n b ih => cases h <;> first | rfl | simp only [Code.eraseImm, VG.Taint.check, ih]
  | frame p b q ih => cases h <;> first | rfl | simp only [Code.eraseImm, VG.Taint.check, ih]

end Taint

/-- Constant time from the analysis of the code without its immediates. -/
theorem Taint.constantTime_eraseImm {Pre : State → Prop} {Pub : State → State → Prop}
    {c : Prog isa} (τ : taint.T)
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → taint.Agree τ s₁ s₂)
    {hc : VG.Taint.Hint taint.T} (h : (taint.check τ (Code.eraseImm c) hc).isSome = true) :
    ConstantTime isa Pre Pub c :=
  VG.Taint.constantTime (A := taint) τ hpub (hc := hc) (Taint.check_eraseImm τ c hc ▸ h)

/-- Constant time from the analysis of code `c'` that is `c` without its immediates
(e.g. with copies that differ only in immediates made equal). -/
theorem Taint.constantTime_eraseImm_of_eq {Pre : State → Prop} {Pub : State → State → Prop}
    {c c' : Prog isa} (τ : taint.T)
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → taint.Agree τ s₁ s₂)
    (he : Code.eraseImm c = c') {hc : VG.Taint.Hint taint.T}
    (h : (taint.check τ c' hc).isSome = true) : ConstantTime isa Pre Pub c :=
  Taint.constantTime_eraseImm τ hpub (hc := hc) (he ▸ h)

/-- The analysis of `c` from that of `c'`, which is `c` without its immediates. -/
theorem Taint.isSome_check_of_eraseImm {c c' : Prog isa} (he : Code.eraseImm c = c')
    {τ : taint.T} {hc : VG.Taint.Hint taint.T} (h : (taint.check τ c' hc).isSome = true) :
    (taint.check τ c hc).isSome = true := by
  rw [← Taint.check_eraseImm, he]; exact h

/-- `allInstrs p` of the code without its immediates, for a `p` that does not read them. -/
theorem Code.allInstrs_eraseImm {p : Instr → Bool} (hp : ∀ i, p i.eraseImm = p i)
    (c : Prog isa) : (Code.eraseImm c).allInstrs p = c.allInstrs p := by
  induction c with
  | block is =>
    show Code.allInstrs p (.block (is.map Instr.eraseImm)) = Code.allInstrs p (.block is)
    rw [Code.allInstrs_eq, Code.allInstrs_eq]
    simp only [instrs, List.all_map, Function.comp_def, hp]
  | seq a b iha ihb => simp only [Code.eraseImm, Code.allInstrs, iha, ihb]
  | ite c t e iht ihe => simp only [Code.eraseImm, Code.allInstrs, iht, ihe]
  | loop b c ih => simp only [Code.eraseImm, Code.allInstrs, ih]
  | call n b ih => simp only [Code.eraseImm, Code.allInstrs, ih]
  | frame i b j ih => simp only [Code.eraseImm, Code.allInstrs, ih]

theorem keepsV_eraseImm (i : Instr) : keepsV i.eraseImm = keepsV i := by
  cases i <;> rfl

/-- `keepsV` of `c` from that of `c'`, which is `c` without its immediates. -/
theorem Code.allInstrs_keepsV_of_eraseImm {c c' : Prog isa} (he : Code.eraseImm c = c')
    (h : c'.allInstrs keepsV = true) : c.allInstrs keepsV = true := by
  rw [← Code.allInstrs_eraseImm keepsV_eraseImm, he]; exact h

/-- Whether code has no frames does not depend on its immediates. -/
theorem Code.noFrames_eraseImm (c : Prog isa) : (Code.eraseImm c).noFrames = c.noFrames := by
  induction c <;> simp_all [Code.eraseImm, Code.noFrames]

end VG.AArch64
