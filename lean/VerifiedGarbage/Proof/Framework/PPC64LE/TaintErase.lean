module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# Taint tracking for PPC64LE: code without its immediates

The analysis (`Taint.step`) does not read the immediates of `li`, `lis`,
`ori` and `oris`: it checks code with them zeroed (`Code.eraseImm`) exactly
as the code itself (`check_eraseImm`). Code built from constants (e.g. an
initial hash value) then has its analysis checked on the code of one
constant, proven once to have the same immediates erased: the kernel neither
builds the constants nor compares the analyses of two codes. As
`Proof/Framework/AArch64/TaintErase.lean`.
-/

@[expose] public section

namespace VG.PPC64LE

/-- The instruction with the immediate of an `li`, `lis`, `ori` or `oris` zeroed. -/
def Instr.eraseImm : Instr → Instr
  | .li d _ => .li d 0
  | .lis d _ => .lis d 0
  | .ori d n _ => .ori d n 0
  | .oris d n _ => .oris d n 0
  | i => i

/-- The code with those immediates zeroed. -/
def Code.eraseImm : Prog isa → Prog isa
  | .block is => .block (is.map Instr.eraseImm)
  | .seq a b => .seq (eraseImm a) (eraseImm b)
  | .ite c t e => .ite c (eraseImm t) (eraseImm e)
  | .loop b c => .loop (eraseImm b) c
  | .call n b => .call n (eraseImm b)
  | .frame p b q => .frame p (eraseImm b) q
  | .icall i n b nx => .icall i n b nx

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

theorem checkChunks_eraseImm {chunkSize : Nat} (τ : taint.T) (is : List isa.Instr) (ms : List taint.T) :
    taint.checkChunks chunkSize τ (is.map Instr.eraseImm) ms = taint.checkChunks chunkSize τ is ms := by
  induction ms generalizing τ is with
  | nil => exact checkBlock_eraseImm τ is
  | cons m ms ih =>
    simp only [VG.Taint.checkChunks, KList.take_eq, KList.drop_eq, ← List.map_take, ← List.map_drop, ih]
    exact congrArg (Option.bind · _) (checkBlock_eraseImm τ _)

theorem check_eraseImm (τ : taint.T) (c : Prog isa) (h : VG.Taint.Hint taint.T) :
    taint.check τ (Code.eraseImm c) h = taint.check τ c h := by
  induction c generalizing τ h with
  | icall => cases h <;> rfl
  | block is => cases h <;> first | rfl | exact checkChunks_eraseImm τ is _
  | seq a b iha ihb =>
    cases h <;> first | rfl | simp only [Code.eraseImm, VG.Taint.check, iha, ihb]
  | ite c t e iht ihe =>
    cases h <;> first | rfl | simp only [Code.eraseImm, VG.Taint.check, iht, ihe]
  | loop b c ih => cases h <;> first | rfl | simp only [Code.eraseImm, VG.Taint.check, ih]
  | call n b ih => cases h <;> first | rfl | simp only [Code.eraseImm, VG.Taint.check, ih]
  | frame p b q ih => cases h <;> first | rfl | simp only [Code.eraseImm, VG.Taint.check, ih]

end Taint

/-- The analysis of `c` from that of `c'`, which has the same code without
its immediates. -/
theorem Taint.isSome_check_of_eraseImm {c c' : Prog isa} (he : Code.eraseImm c = Code.eraseImm c')
    {τ : taint.T} {hc : VG.Taint.Hint taint.T} (h : (taint.check τ c' hc).isSome = true) :
    (taint.check τ c hc).isSome = true := by
  rw [← Taint.check_eraseImm, he, Taint.check_eraseImm]; exact h

end VG.PPC64LE
