module

import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Square.CrossPtr
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.X86.Square.Packed
public import VerifiedGarbage.Proof.Mont.X86.Words

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.X86.RegUpd

def double : List Instr := [.xop (.shift .psllq .xmm0 1), .xop (.shift .psllq .xmm1 1),
  .mov .eax (.reg .esi), .alu .and .eax (.imm 4)]

def doubleState (s : State) : State :=
  let t1 := (XOp.shift .psllq .xmm0 1).exec s
  let t2 := (XOp.shift .psllq .xmm1 1).exec t1
  let t3 := t2.setReg .eax (t2.gpr .esi)
  let v := t3.gpr .eax &&& 4
  (arithFlags t3 v false false).setReg .eax v

theorem run_double (s : State) : runBlock isa double s = some (doubleState s) := by rfl

theorem parity4 (k : Nat) : BitVec.ofNat 32 (4*k) &&& (4 : BitVec 32) =
    if k%2=0 then 0 else 4 := by
  rw [show (4 : BitVec 32) = BitVec.twoPow 32 2 from rfl, BitVec.and_twoPow]
  simp only [BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq]
  have bit : (4*k) / 2^2 % 2 = k%2 := by simp [Nat.mul_comm]
  simp only [bit, show decide (2 < 32) = true from rfl, Bool.true_and]
  by_cases e : k%2=0
  · simp [e]
  · have e1 : k%2=1 := by omega
    simp [e1]

theorem shl_one (v : Nat) : (BitVec.ofNat 64 v) <<< 1 = BitVec.ofNat 64 (2*v) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 v * BitVec.ofNat 64 2 = _
  rw [← BitVec.ofNat_mul]
  congr 1
  omega

theorem double_values {s : State} {k l h : Nat}
    (hl : s.xmm .xmm0 = packed (BitVec.ofNat 64 l))
    (hh : s.xmm .xmm1 = packed (BitVec.ofNat 64 h))
    (si : s.gpr .esi = BitVec.ofNat 32 (4*k)) :
    let t := doubleState s
    t.xmm .xmm0 = packed (BitVec.ofNat 64 (2*l)) ∧
    t.xmm .xmm1 = packed (BitVec.ofNat 64 (2*h)) ∧
    t.xmm .xmm3 = s.xmm .xmm3 ∧ t.xmm .xmm7 = s.xmm .xmm7 ∧
    t.mem = s.mem ∧ Keeps [.eax] s t ∧ t.zf = some (decide (k%2=0)) := by
  have shifts : ∀ a : BitVec 64, XShiftOp.eval .psllq (packed a) (1 : BitVec 8) = packed (a <<< 1) :=
    fun a => packed_shl a (by decide)
  have xm : ∀ r, (doubleState s).xmm r =
      if r = .xmm1 then packed (BitVec.ofNat 64 (2*h)) else
      if r = .xmm0 then packed (BitVec.ofNat 64 (2*l)) else s.xmm r := by
    intro r
    simp only [doubleState, XOp.exec, xmm_setReg, xmm_arithFlags]
    simp (disch := decide) only [xmm_setXmm, hh, hl, shifts, shl_one, show XReg.xmm1 ≠ XReg.xmm0 by decide, ↓reduceIte]
  refine ⟨xm .xmm0, xm .xmm1, xm .xmm3, xm .xmm7, rfl, ?_, ?_⟩
  · refine ⟨?_, rfl, rfl⟩
    intro r hr
    have ne : r ≠ .eax := by simpa using hr
    simp only [doubleState, XOp.exec, State.setReg, arithFlags, State.setFlags, gpr_setXmm]
    simp [ne]
  · change some (_ == 0) = _
    simp only [XOp.exec, gpr_setXmm, State.setReg, ↓reduceIte, si, parity4]
    by_cases e : k%2=0 <;> simp [e]

end VG.Proof.Mont.X86.Square
