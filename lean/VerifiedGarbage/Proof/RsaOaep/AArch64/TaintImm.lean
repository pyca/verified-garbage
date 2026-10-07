import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
import VerifiedGarbage.Impl.Pbkdf2.Md.AArch64

/-!
# RSAES-OAEP on AArch64: code without its immediates

As `Code.eraseImm` (`Proof/Framework/AArch64/TaintErase.lean`), which
zeroes the immediates of `movz` and `movk`, `zImm` also zeroes those of
`addImm` and `subImm`, which the analysis does not read either
(`check_zImm`). The blocks that use the hash length (`hLen`, as an
immediate) are then checked once, for any hash function, on their copy for
one of them (`check_of_zImm`).
-/

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64

/-- The instruction with the immediate of a `movz`, `movk`, `addImm` or
`subImm` zeroed. -/
def Instr.zImm : Instr → Instr
  | .movz sz d _ hw => .movz sz d 0 hw
  | .movk sz d _ hw => .movk sz d 0 hw
  | .addImm sz d n _ => .addImm sz d n 0
  | .subImm sz d n _ => .subImm sz d n 0
  | i => i

/-- The code with those immediates zeroed. -/
def zImm : Prog isa → Prog isa
  | .block is => .block (is.map Instr.zImm)
  | .seq a b => .seq (zImm a) (zImm b)
  | .ite c t e => .ite c (zImm t) (zImm e)
  | .loop b c => .loop (zImm b) c
  | .call n b => .call n (zImm b)
  | .frame p b q => .frame p (zImm b) q

theorem step_zImm (τ : VG.AArch64.Taint.T) (i : Instr) :
    VG.AArch64.Taint.step τ (Instr.zImm i) = VG.AArch64.Taint.step τ i := by
  cases i <;> rfl

theorem checkBlock_zImm (τ : taint.T) (is : List isa.Instr) :
    taint.checkBlock τ (is.map Instr.zImm) = taint.checkBlock τ is := by
  induction is generalizing τ with
  | nil => rfl
  | cons i is ih =>
    show (VG.AArch64.Taint.step τ (Instr.zImm i)).bind _ = (VG.AArch64.Taint.step τ i).bind _
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
  | block is => cases h <;> first | rfl | exact checkChunks_zImm τ is _
  | seq a b iha ihb =>
    cases h <;> first | rfl | simp only [zImm, VG.Taint.check, iha, ihb]
  | ite c t e iht ihe =>
    cases h <;> first | rfl | simp only [zImm, VG.Taint.check, iht, ihe]
  | loop b c ih => cases h <;> first | rfl | simp only [zImm, VG.Taint.check, ih]
  | call n b ih => cases h <;> first | rfl | simp only [zImm, VG.Taint.check, ih]
  | frame p b q ih => cases h <;> first | rfl | simp only [zImm, VG.Taint.check, ih]

/-- The analysis of `c` from that of `c'`, which differs from it only in
those immediates. -/
theorem check_of_zImm {c c' : Prog isa} (he : zImm c = zImm c') {τ : taint.T} {hc : VG.Taint.Hint taint.T}
    (h : (taint.check τ c' hc).isSome = true) : (taint.check τ c hc).isSome = true := by
  rw [← check_zImm, he, check_zImm]; exact h

/-- A hash function whose code is checked in place of any other's: its
fields are what code with its length as an immediate reads, all zero. -/
def gH : Impl.Pbkdf2.Md.AArch64.Hash where
  P := { N := 0, B := 0, L := 0, so := 0, len := [], out := [] }
  D := 0
  W := 0
  compN := ""
  compC := .block []
  initN := ""
  initC := .block []
  updN := ""
  updC := .block []
  finN := ""
  finC := .block []
  hmacInitN := ""
  hmacFinN := ""
  iterN := ""

end VG.Proof.RsaOaep.AArch64
