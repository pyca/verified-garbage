module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Groups
public import VerifiedGarbage.Impl.Aes.PPC64LE.Crypto.ExpandKey
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

-- separate module: the key loop reuses short SubWord and round-constant groups.
/-! # POWER8 AES key-expansion groups -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE

theorem rotateRight0 (x : BitVec 32) : x.rotateRight 0 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem subWord_ok (s : State) : WP isa (.block Impl.Aes.PPC64LE.Crypto.subWord) s fun t =>
    t.gpr .r9 = (VG.Proof.Aes.KeyWords.sub32 ((s.gpr .r9).setWidth 32)).setWidth 64 ∧ Local [.r9] [.v0] s t := by
  apply WP.of_runBlock
  simp only [Impl.Aes.PPC64LE.Crypto.subWord, runBlock_cons, runStep_some, runBlock_nil,
    reduceExec, reduceVOpEval, Option.map_some, vpr_writeV, gpr_writeV,
    show 0 < 32 by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun r hr => ?_, ?_⟩⟩
  · simp only [RegUpd.gpr_write_self, Size.ext, Size.bits, State.read,
      RegUpd.gpr_write_self, rotateRight0, vdword, Nat.sub_zero, Nat.mul_one, sbox_word]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false, gpr_writeV]
  · simp only [RegUpd.rd_write, rd_writeV]
  · simp only [RegUpd.wr_write, wr_writeV]
  · simp only [List.mem_singleton] at hr
    simp only [vpr_write, vpr_writeV, hr, ite_false]
  · simp only [RegUpd.mem_write, mem_writeV]

def rcNext (v : BitVec 64) : BitVec 64 :=
  ((v + v) ^^^ ((0#64 - (v >>> 7)) &&& 0x1b)) &&& 0xff

theorem rotTail_ok (s : State) : WP isa (.block Impl.Aes.PPC64LE.Crypto.rotTail) s fun t =>
    t.gpr .r9 = (((s.gpr .r9).setWidth 32).rotateRight 8).setWidth 64 ^^^ s.gpr .r6 ∧
      t.gpr .r6 = rcNext (s.gpr .r6) ∧ Local [.r0, .r6, .r8, .r9] [] s t := by
  apply WP.of_runBlock
  simp only [Impl.Aes.PPC64LE.Crypto.rotTail, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
    State.read, Size.ext, Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write, reduceCtorEq,
    ite_true, ite_false,
    show 8 < 32 by decide, show 7 < 64 by decide,
    show 0 < 2^15 by decide, show 27 < 2^15 by decide, show 255 < 2^15 by decide,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun r _ => ?_, ?_⟩⟩
  · exact True.intro
  · simp only [rcNext, BitVec.ofNat_eq_ofNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [vpr_write]
  · simp only [RegUpd.mem_write]

theorem rcNext_rc : ∀ j : Fin 11, 1 ≤ j.val →
    rcNext ((Impl.Aes.KeyWords.rc j).setWidth 64) = (Impl.Aes.KeyWords.rc (j.val+1)).setWidth 64 := by decide

theorem testWord_ok (r : Reg) (imm : Nat) (s : State) (hr : r ≠ .r0) (hi : imm ≤ 2^15) :
    WP isa (.block [.subi .r0 r imm]) s (· = s.write .r0 (s.gpr r - BitVec.ofNat 64 imm)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_subi hr hi, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']

end VG.Proof.Aes.PPC64LE.Crypto
