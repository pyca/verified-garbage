module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# RSAES-OAEP encryption on PPC64LE: code without its immediates

Untrusted: everything here is checked by Lean. As `Code.eraseImm`
(`Proof/Framework/PPC64LE/TaintErase.lean`), which zeroes the immediates of
`li`, `lis`, `ori` and `oris`, `zImm` also zeroes those of `addi` and `subi`,
which the analysis does not read either (`check_zImm`). The blocks that use
a hash length (as an immediate) are then checked once, for any hash function,
on their copy for one of them (`isSome_check_of_zImm`), as on AArch64
(`Proof/RsaOaep/AArch64/TaintImm.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE

/-- The instruction with the immediate of an `li`, `addi` or `subi` zeroed. -/
def Instr.zImm : Instr → Instr
  | .li d _ => .li d 0
  | .addi d n _ => .addi d n 0
  | .subi d n _ => .subi d n 0
  | i => i

/-- The code with those immediates zeroed. -/
def zImm : Prog isa → Prog isa
  | .block is => .block (is.map Instr.zImm)
  | .seq a b => .seq (zImm a) (zImm b)
  | .ite c t e => .ite c (zImm t) (zImm e)
  | .loop b c => .loop (zImm b) c
  | .call n b => .call n (zImm b)
  | .frame p b q => .frame p (zImm b) q
  | .icall i n b nx => .icall i n b nx

theorem step_zImm (τ : VG.PPC64LE.Taint.T) (i : Instr) :
    VG.PPC64LE.Taint.step τ (Instr.zImm i) = VG.PPC64LE.Taint.step τ i := by
  cases i <;> rfl

theorem checkBlock_zImm (τ : taint.T) (is : List isa.Instr) :
    taint.checkBlock τ (is.map Instr.zImm) = taint.checkBlock τ is := by
  induction is generalizing τ with
  | nil => rfl
  | cons i is ih =>
    show (VG.PPC64LE.Taint.step τ (Instr.zImm i)).bind _ = (VG.PPC64LE.Taint.step τ i).bind _
    exact congr (congrArg Option.bind (step_zImm τ i)) (funext ih)

theorem checkChunks_zImm {chunkSize : Nat} (τ : taint.T) (is : List isa.Instr) (ms : List taint.T) :
    taint.checkChunks chunkSize τ (is.map Instr.zImm) ms = taint.checkChunks chunkSize τ is ms := by
  induction ms generalizing τ is with
  | nil => exact checkBlock_zImm τ is
  | cons m ms ih =>
    simp only [VG.Taint.checkChunks, KList.take_eq, KList.drop_eq, ← List.map_take, ← List.map_drop, ih]
    exact congrArg (Option.bind · _) (checkBlock_zImm τ _)

theorem check_zImm (τ : taint.T) (c : Prog isa) (h : VG.Taint.Hint taint.T) :
    taint.check τ (zImm c) h = taint.check τ c h := by
  induction c generalizing τ h with
  | icall => cases h <;> rfl
  | block is => cases h <;> first | rfl | exact checkChunks_zImm τ is _
  | seq a b iha ihb => cases h <;> first | rfl | simp only [zImm, VG.Taint.check, iha, ihb]
  | ite c t e iht ihe => cases h <;> first | rfl | simp only [zImm, VG.Taint.check, iht, ihe]
  | loop b c ih => cases h <;> first | rfl | simp only [zImm, VG.Taint.check, ih]
  | call n b ih => cases h <;> first | rfl | simp only [zImm, VG.Taint.check, ih]
  | frame p b q ih => cases h <;> first | rfl | simp only [zImm, VG.Taint.check, ih]

/-- The analysis of `c` from that of `c'`, which has the same code without
those immediates. -/
theorem isSome_check_of_zImm {c c' : Prog isa} (he : zImm c = zImm c') {τ : taint.T}
    {hc : VG.Taint.Hint taint.T} (h : (taint.check τ c' hc).isSome = true) :
    (taint.check τ c hc).isSome = true := by
  rw [← check_zImm, he, check_zImm]; exact h

end VG.Proof.RsaOaep.PPC64LE
