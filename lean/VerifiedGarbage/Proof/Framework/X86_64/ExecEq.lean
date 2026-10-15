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

theorem setReg_ne {s : State} {d r : Reg} {v : BitVec 64} (h : r ≠ d) : (s.setReg d v).gpr r = s.gpr r := by
  simp only [State.setReg, h, ↓reduceIte]

/-- The general-purpose register an instruction writes, if it writes exactly
one (none for stores and SSE instructions, and for `mul` and `mulx`, which
write two). -/
def dstOf : Instr → Option Reg
  | .mov d _ | .mov32 d _ | .alu _ d _ | .alu32 _ d _ | .shift32 _ d _ | .bswap32 d
  | .rorx32 d .. | .andn32 d .. | .rorx d .. | .andn d .. | .movzx8 d _ | .bswap d | .shift _ d _
  | .movImm64 d _ | .leaSym d _ | .adcx d _ | .adox d _ | .cmov _ d _ | .vpmovmskb _ d _
  | .movqR d _ | .imul d _ => some d
  | .store .. | .store32 .. | .store8 .. | .movdquLoad .. | .movdquStore .. | .xop _ | .vop _
  | .vmovdquLoad .. | .vmovdquStore .. | .vbroadcasti128 .. | .vbinLoad .. | .zop _ | .vmovdqu32Load ..
  | .vmovdqu32Store .. | .vbroadcasti32x4 .. | .vbroadcasti32x4H .. | .zbcst .. | .vpmadd52Load .. | .stmxcsr _ | .ldmxcsr _
  | .eop _ | .evLoad .. | .evStore .. | .evMadd52Load .. | .kLoad .. | .kStore .. | .lfence
  | .mul _ | .mulx .. | .push _ | .pop .. | .alloc _ | .free _ => none

/-- Whether an instruction may write the general-purpose register `r`. -/
def clobbers (i : Instr) (r : Reg) : Bool :=
  match i with
  | .mul _ => r == .rax || r == .rdx
  | .mulx hi lo _ => r == hi || r == lo
  -- The push and pop of a frame move `rsp`, and the pop loads `d`.
  | .push _ | .alloc _ | .free _ => r == .rsp
  | .pop d _ => r == .rsp || r == d
  | _ => dstOf i == some r

theorem cmov_gpr (s : State) (d : Reg) (c : Bool) (v : BitVec 64) (r : Reg) :
    (if c then s.setReg d v else s).gpr r = if r = d then (if c then v else s.gpr d) else s.gpr r := by
  cases c <;> by_cases h : r = d <;>
    simp only [h, State.setReg, Bool.false_eq_true, ↓reduceIte]

theorem cmov_flags (s : State) (d : Reg) (c : Bool) (v : BitVec 64) :
    (if c then s.setReg d v else s).cf = s.cf ∧ (if c then s.setReg d v else s).zf = s.zf ∧
      (if c then s.setReg d v else s).sf = s.sf ∧ (if c then s.setReg d v else s).of = s.of := by
  cases c <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- An instruction that writes one general-purpose register changes nothing
else but the flags. -/
theorem exec_nonstore_xmm {i : Instr} {d : Reg} (hd : dstOf i = some d) {s s' : State}
    (h : exec i s = some s') :
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧ s'.xmm = s.xmm ∧ ∀ r, r ≠ d → s'.gpr r = s.gpr r := by
  cases i <;> simp only [dstOf, Option.some.injEq, reduceCtorEq] at hd <;> subst hd
  case mov src =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case mov32 src =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case alu op src =>
    simp only [exec, execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h
    split
    · exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
    · exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  case alu32 op src =>
    simp only [exec, execAlu32_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h
    split
    · exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
    · exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  case shift32 op _ n =>
    simp only [exec, execShift32] at h
    split at h
    · cases op <;> simp only [Option.some.injEq] at h <;> subst h <;>
        exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
    · cases h
  case bswap32 =>
    simp only [exec, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case rorx32 r n =>
    simp only [exec, execRorx32] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
    · cases h
  case andn32 a b =>
    simp only [exec, execAndn32, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case rorx r n =>
    simp only [exec, execRorx] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
    · cases h
  case andn a b =>
    simp only [exec, execAndn, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case imul r =>
    simp only [exec, execImul, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case movzx8 m =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case bswap =>
    simp only [exec, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case shift op _ n =>
    simp only [exec, execShift] at h
    split at h
    · cases op <;> simp only [Option.some.injEq] at h <;> subst h <;>
        exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
    · cases h
  case movImm64 v =>
    simp only [exec, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case leaSym name =>
    simp only [exec, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case vpmovmskb len r =>
    simp only [exec, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case movqR r =>
    simp only [exec, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case adcx src =>
    simp only [exec, execAdcx] at h
    split at h
    · cases h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, _, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case adox src =>
    simp only [exec, execAdox] at h
    split at h
    · cases h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, _, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩
  case cmov cc src =>
    obtain ⟨_, c, -, -, rfl⟩ := execCmov_some h
    cases c
    · exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, fun r h => setReg_ne h⟩

theorem exec_nonstore {i : Instr} {d : Reg} (hd : dstOf i = some d) {s s' : State}
    (h : exec i s = some s') :
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧ ∀ r, r ≠ d → s'.gpr r = s.gpr r :=
  let ⟨a, b, c, _, e⟩ := exec_nonstore_xmm hd h
  ⟨a, b, c, e⟩

theorem execMul_gpr (r : Reg) (s : State) {q : Reg} (h₁ : q ≠ .rax) (h₂ : q ≠ .rdx) :
    (execMul r s).gpr q = s.gpr q := by
  simp only [execMul, State.setReg, Nat.reducePow, State.setFlags, BitVec.ofNat_eq_ofNat, h₂,
      ↓reduceIte, h₁]

theorem mulx_gpr {hi lo : Reg} (s : State) (v w : BitVec 64) {q : Reg} (h₁ : q ≠ hi)
    (h₂ : q ≠ lo) : ((s.setReg lo w).setReg hi v).gpr q = s.gpr q := by
  rw [setReg_ne h₁, setReg_ne h₂]

end VG.X86_64.Taint
