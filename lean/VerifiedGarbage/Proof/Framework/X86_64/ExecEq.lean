module

public import VerifiedGarbage.TCB.X86_64.Target

/-!
# x86-64: execution lemmas of the taint analysis

How ALU, vector and conditional-move instructions execute, in the forms the
taint analysis (`Taint.lean`) and the calling-convention proofs (`Abi.lean`)
use. They need nothing of the analysis, so a module that uses only them
need not import it.
-/

@[expose] public section

namespace VG.X86_64.Taint

def usesCarry : AluOp → Bool
  | .adc | .sbb => true
  | _ => false

def writes : AluOp → Bool
  | .cmp | .test => false
  | _ => true

/-! ### ALU instructions, uniformly -/

/-- The result, carry and overflow of an ALU operation at width `w`. -/
def aluOut {w : Nat} (op : AluOp) (a b : BitVec w) (cf : Option Bool) :
    Option (BitVec w × Bool × Bool) :=
  match op with
  | .add => let r := a + b; some (r, 2 ^ w ≤ a.toNat + b.toNat, addOverflow a b r)
  | .adc => cf.map fun c =>
    let r := a + b + (BitVec.ofBool c).setWidth w
    (r, 2 ^ w ≤ a.toNat + b.toNat + c.toNat, addOverflow a b r)
  | .sub | .cmp => let r := a - b; some (r, a.toNat < b.toNat, subOverflow a b r)
  | .sbb => cf.map fun c =>
    let r := a - b - (BitVec.ofBool c).setWidth w
    (r, a.toNat < b.toNat + c.toNat, subOverflow a b r)
  | .and | .test => some (a &&& b, false, false)
  | .or => some (a ||| b, false, false)
  | .xor => some (a ^^^ b, false, false)

theorem aluOut_cf {w : Nat} {op : AluOp} (h : usesCarry op = false) (a b : BitVec w)
    (c c' : Option Bool) : aluOut op a b c = aluOut op a b c' := by
  cases op <;> simp_all only [usesCarry, aluOut, Bool.true_eq_false]

theorem execAlu_eq (op : AluOp) (d : Reg) (src : Src) (s : State) :
    execAlu op d src s = (readSrc s src).bind fun b =>
      (aluOut op (s.gpr d) b s.cf).map fun (r, c, o) =>
        if writes op then (arithFlags s r c o).setReg d r else arithFlags s r c o := by
  cases op <;> simp only [execAlu, Nat.reducePow, writes, ↓reduceIte, aluOut, Option.map_some,
      Option.map_map, Function.comp_def, Bool.false_eq_true]

theorem execAlu32_eq (op : AluOp) (d : Reg) (src : Src) (s : State) :
    execAlu32 op d src s = (readSrc32 s src).bind fun b =>
      (aluOut op ((s.gpr d).setWidth 32) b s.cf).map fun (r, c, o) =>
        if writes op then (arithFlags s r c o).setReg32 d r else arithFlags s r c o := by
  cases op <;> simp only [execAlu32, Nat.reducePow, BitVec.toNat_setWidth, writes, ↓reduceIte,
      aluOut, Option.map_some, Option.map_map, Function.comp_def, Bool.false_eq_true]

/-- An SSE instruction on registers changes only the SSE registers. -/
theorem XOp.exec_eq (op : XOp) (s : State) : op.exec s = { s with xmm := (op.exec s).xmm } := by
  cases op <;> rfl

/-- An AVX instruction on registers changes only the vector registers. -/
theorem VOp.exec_eq (op : VOp) (s : State) :
    op.exec s =
      { s with xmm := (op.exec s).xmm, ymmHi := (op.exec s).ymmHi, zmmHi := (op.exec s).zmmHi } := by
  cases op <;> simp only [VOp.exec] <;> (try split) <;> rfl

/-- An AVX-512 instruction on registers changes only the vector registers. -/
theorem ZOp.exec_eq (op : ZOp) (s : State) :
    op.exec s =
      { s with xmm := (op.exec s).xmm, ymmHi := (op.exec s).ymmHi, zmmHi := (op.exec s).zmmHi } := by
  cases op <;> rfl

/-- An `EVEX.256` instruction's write changes only the vector registers. -/
theorem setVy_eq (s : State) (r : VReg) (v : BitVec 256) :
    s.setVy r v =
      { s with
        xmm := (s.setVy r v).xmm
        ymmHi := (s.setVy r v).ymmHi
        zmmHi := (s.setVy r v).zmmHi
        ymmH := (s.setVy r v).ymmH
        zmmHiH := (s.setVy r v).zmmHiH } := by
  cases r <;> rfl

/-- An `EVEX.256` instruction on registers changes only the vector registers. -/
theorem EOp.exec_eq (op : EOp) (s : State) :
    op.exec s =
      { s with
        xmm := (op.exec s).xmm
        ymmHi := (op.exec s).ymmHi
        zmmHi := (op.exec s).zmmHi
        ymmH := (op.exec s).ymmH
        zmmHiH := (op.exec s).zmmHiH } := by
  cases op <;> exact setVy_eq _ _ _

/-- What `cmovcc d, src` computes: the source and the condition, and `d`
written if the condition holds. -/
theorem execCmov_some {cc : Cond} {d : Reg} {src : Src} {s s' : State}
    (h : execCmov cc d src s = some s') :
    ∃ v c, readSrc s src = some v ∧ eval cc s = some c ∧ s' = if c then s.setReg d v else s := by
  simp only [execCmov] at h
  split at h
  · cases h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, c, hc, rfl⟩ := h
    exact ⟨v, c, hv, hc, rfl⟩

end VG.X86_64.Taint
