module

public import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.ESym
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Rsa.X86_64.CrtIfma

/-- The scalar operations map the four lane mask bits to their positions
in the 32-bit generate or propagate mask, then OR into the accumulator. -/
def addCarryRowBits (gt : Bool) (r : VReg) (j : Nat) (s : State) : BitVec 32 :=
  let cmp := (cmpUqMask gt (s.vy r) (s.vy (vreg 24))).setWidth 64
  let bits := ((cmp * 0x00204081) &&& s.gpr .rsi).setWidth 32
  (s.gpr (if gt then .rax else .rcx)).setWidth 32 ||| (bits <<< j)

theorem spreadCarryMask_run (gt : Bool) (r : VReg) (j : Nat) (hj : j < 8) (s : State) :
    ∃ t, runBlock isa (spreadCarryMask gt r j) s = some t ∧
      t.gpr (if gt then .rax else .rcx) = (addCarryRowBits gt r j s).setWidth 64 ∧
      (∀ v, t.vy v = s.vy v) ∧
      (∀ q, q ≠ .rdx → q ≠ (if gt then .rax else .rcx) → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  have h := (show j = 0 ∨ 1 ≤ j ∧ j ≤ 31 by omega)
  rcases h with rfl | ⟨h1, h2⟩
  · cases gt <;> simp [spreadCarryMask, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      execAlu32, readSrc, readSrc32, addCarryRowBits,
      State.setReg32,
      execImul3, State.setReg, arithFlags, State.setFlags, BitVec.ofInt_mul, -BitVec.toInt_setWidth] <;>
      (try constructor) <;> (try intro q hq hd) <;> (try simp [hq, hd]) <;>
      (try intro v; cases v <;> rfl)
  · have h0 : j ≠ 0 := by omega
    cases gt <;> simp [spreadCarryMask, h0, h1, h2, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, execAlu32, execShift32, readSrc, readSrc32, addCarryRowBits,
      State.setReg32,
      execImul3, State.setReg, arithFlags, State.setFlags, BitVec.ofInt_mul, -BitVec.toInt_setWidth] <;>
      (try constructor) <;> (try intro q hq hd) <;> (try simp [hq, hd]) <;>
      (try intro v; cases v <;> rfl)

/-- Move every eighth bit of the aligned carry mask into a four-bit mask. -/
def compactCarryBits (s : State) : BitVec 64 :=
  ((((s.gpr .rax &&& s.gpr .rsi) * 0x01020408) >>> 24) &&& 15)

/-- The value written to memory by a carry row. -/
def normalizedCarryRow (s : State) (r : VReg) : BitVec 256 :=
  lanes256 XBinOp.pand.eval (maskAddQ (compactCarryBits s) (s.vy r) (s.vy r) (s.vy (vreg 25)))
    (s.vy (vreg 24))

private theorem vy_setVy_same (s : State) (r : VReg) (x : BitVec 256) :
    (s.setVy r x).vy r = x := by
  cases r with
  | hi r => simp [State.setVy, State.vy]
  | lo r =>
    simp [State.setVy, State.vy, State.setV, State.ymm]
    exact extract_cat x

private theorem vy_setVy_other (s : State) (r v : VReg) (x : BitVec 256) (h : v ≠ r) :
    (s.setVy r x).vy v = s.vy v := by
  cases r <;> cases v <;> simp_all [State.setVy, State.vy, State.setV, State.ymm]

private theorem setVy_frames (s : State) (r : VReg) (x : BitVec 256) :
    (s.setVy r x).gpr = s.gpr ∧ (s.setVy r x).mem = s.mem ∧
      (s.setVy r x).rd = s.rd ∧ (s.setVy r x).wr = s.wr ∧ (s.setVy r x).mxcsr = s.mxcsr := by
  cases r <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem vy_scalar (s : State) (r : Reg) (b : BitVec 64) (v : VReg)
    (c o z f : Option Bool) :
    ((s.setFlags c o z f).setReg r b).vy v = s.vy v := by
  cases v <;> rfl

/-- The store phase performs one write of the normalized row. -/
theorem store3072Row_run (s : State) (r : VReg) (o : Nat) (hm : vreg 24 ≠ r)
    (hw : InRegions s.wr (s.ea (at_ .r11 o)) 32) :
    ∃ t, runBlock isa (store3072Row r o) s = some t ∧
      t.mem = s.mem.writeW (s.ea (at_ .r11 o)) (normalizedCarryRow s r) ∧
      (∀ v, v ≠ r → t.vy v = s.vy v) ∧
      (∀ q, q ≠ .rdx → t.gpr q = s.gpr q) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  have hh : 1 ≤ (24 : Nat) ∧ 24 ≤ 63 := by decide
  have he : s.ea (at_ .r11 o) = s.gpr .r11 + BitVec.ofInt 64 (Int.ofNat o) := rfl
  rw [he] at hw
  change InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 o) 32 at hw
  simp [store3072Row, runBlock_cons, runStep_some, exec, execAlu,
    execShift, hh, readSrc, execImul3, BitVec.ofInt_mul, arithFlags, State.setFlags, State.setReg,
    EOp.exec, EBinOp.sse, State.store256, State.ea, at_, normalizedCarryRow, compactCarryBits,
    vy_setVy_same, vy_setVy_other, setVy_frames, hm, -BitVec.toInt_and]
  rw [ite_eq_left hw]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, trivial, trivial, trivial⟩
  · cases r <;> rfl
  · intro v h
    cases r <;> cases v <;> simp_all only [State.setVy, State.vy, State.setV, State.ymm,
      reduceCtorEq, VReg.lo.injEq, VReg.hi.injEq, ite_false]
  · intro q h
    simp [h]

/-- Compute the carry-in mask from the two masks accumulated by the row loop. -/
theorem carryMask_run (s : State) :
    ∃ t, runBlock isa
        [.shift .shl .rax 1, .alu .add .rax (.reg .rcx), .alu .xor .rax (.reg .rcx)] s = some t ∧
      t.gpr .rax = ((s.gpr .rcx + (s.gpr .rax <<< 1)) ^^^ s.gpr .rcx) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ (∀ v, t.vy v = s.vy v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  simp [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift,
    readSrc, State.setReg, arithFlags, State.setFlags]
  refine ⟨?_, ?_, ?_⟩
  · rw [BitVec.add_comm]
  · intro r hr
    simp [hr]
  · intro v
    cases v <;> rfl

end VG.Proof.Bignum.X86_64.Ifma
