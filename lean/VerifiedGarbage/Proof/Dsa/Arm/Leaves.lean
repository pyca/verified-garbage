module

public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Timing
public import VerifiedGarbage.Impl.Dsa.Arm.SignVerify
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Timing
meta import VerifiedGarbage.Impl.Dsa.Arm.SignVerify
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# DSA on 32-bit ARM: the parts whose traces a taint analysis checks

Each part below leaks a trace that depends only on registers known public
when it starts: `r12` (the working space), and `r11` and `lr` where a part
reads through them. Their code differs between instances only in offsets and
`movw` immediates, or repeats a part whose analysis keeps its taint, so one
instance is analysed (`erased_relCT`, `flatMap_relCT`). Which registers are
public where a part starts follows from what both runs compute
(`SameTrace`, in the proofs that use these).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout

/-- `r12` public. -/
abbrev T0 : taint.T := wsT false false

/-- `r12` and `r11` public. -/
abbrev T1 : taint.T := wsT true false

/-- `r12` and `r10` public. -/
def T10 : taint.T := Taint.ofRegs [.r12, .r10]

theorem T10_noBase : Taint.NoBase T10 := Taint.noBase_ofRegs _

theorem flatMap_relCT {α : Type} (xs : List α) (f : α → List Instr) {P : State → State → Prop}
    (H : ∀ x, RelCT isa P (.block (f x)) P) : RelCT isa P (.block (xs.flatMap f)) P := by
  induction xs with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons x xs ih =>
    rw [List.flatMap_cons]
    exact RelCT.block_append (RelCT.seq (H x) ih)

theorem pointer_relCT (p : Pointer) : RelCT isa (VG.Arm.Taint.Agree T0) (.block (Core.pointer p)) (VG.Arm.Taint.Agree T0) := by
  cases p with
  | input f =>
    exact erased_relCT (c₀ := .block [.ldr .r11 .r12 0])
      (VG.Taint.hintOf taint T0 (.block [.ldr .r11 .r12 0])) rfl (wsT_noBase _ _) rfl
  | «local» o =>
    exact erased_relCT (c₀ := .block (ptr .r11 0)) (VG.Taint.hintOf taint T0 (.block (ptr .r11 0))) rfl
      (wsT_noBase _ _) rfl
  | signatureS =>
    exact erased_relCT (c₀ := .block (Core.pointer .signatureS))
      (VG.Taint.hintOf taint T0 (.block (Core.pointer .signatureS))) rfl (wsT_noBase _ _) rfl

theorem loadZeros_relCT (k : Nat) :
    RelCT isa (VG.Arm.Taint.Agree T10) (.block ((List.range k).flatMap fun j => [.mov .r4 (.imm 0), .str .r4 .r10 (4 * j)]))
      (VG.Arm.Taint.Agree T10) :=
  flatMap_relCT _ _ fun _ => erased_relCT (c₀ := .block [.mov .r4 (.imm 0), .str .r4 .r10 0])
    (VG.Taint.hintOf taint T10 (.block [.mov .r4 (.imm 0), .str .r4 .r10 0])) rfl T10_noBase rfl

theorem zeroPad_relCT (k : Nat) :
    RelCT isa (VG.Arm.Taint.Agree T10) (zeroPad k) (VG.Arm.Taint.Agree T10) := by
  unfold zeroPad
  split
  · exact loadZeros_relCT k
  · exact erased_relCT (c₀ := zeroPadLoop 1)
      (VG.Taint.hintOf taint T10 (zeroPadLoop 1)) rfl T10_noBase rfl

theorem loadComponent_relCT (len n out : Nat) :
    RelCT isa (VG.Arm.Taint.Agree T1) (loadComponent len n out) (VG.Arm.Taint.Agree T10) := by
  unfold loadComponent
  refine RelCT.assoc (RelCT.seq ?_ (zeroPad_relCT _))
  exact erased_relCT (c₀ := .seq (.block ([.movw .r8 0, .dp .add .r8 .r11 (.reg .r8)] ++ ptr .r10 0 ++ ptr .r9 0))
      (ptrLoop .r10 [.ldr .r4 .r8 0, .rev .r4 .r4, .str .r4 .r10 0, .dp .sub .r8 .r8 (.imm 4), bump .r10 4]))
    (VG.Taint.hintOf taint T1 (.seq (.block ([.movw .r8 0, .dp .add .r8 .r11 (.reg .r8)] ++ ptr .r10 0 ++ ptr .r9 0))
      (ptrLoop .r10 [.ldr .r4 .r8 0, .rev .r4 .r4, .str .r4 .r10 0, .dp .sub .r8 .r8 (.imm 4), bump .r10 4])))
    rfl (wsT_noBase _ _) rfl

theorem store_relCT (len output : Nat) : RelCT isa (VG.Arm.Taint.Agree T0) (Core.store len output) (VG.Arm.Taint.Agree T0) :=
  erased_relCT (c₀ := Core.store 4 0) (VG.Taint.hintOf taint T0 (Core.store 4 0)) rfl (wsT_noBase _ _) rfl

/-- A constant's words: each stored through `r10`, which stays public. -/
theorem setConstWords_relCT (k x : Nat) :
    RelCT isa (VG.Arm.Taint.Agree T10) (.block ((List.range k).flatMap fun j =>
      if x >>> (32 * j) % 2 ^ 32 = 0 then [] else movImm (x >>> (32 * j)) ++
        ([.str .r4 .r10 (4 * j)] : List Instr)))
      (VG.Arm.Taint.Agree T10) := by
  refine flatMap_relCT _ _ fun j => ?_
  split
  · exact RelCT.block_nil (fun _ _ h => h)
  · exact erased_relCT (c₀ := .block [.movw .r4 0, .movt .r4 (BitVec.ofNat 16 (x >>> (32 * j) >>> 16)), .str .r4 .r10 0])
      (VG.Taint.hintOf taint T10 (.block [.movw .r4 0, .movt .r4 (BitVec.ofNat 16 (x >>> (32 * j) >>> 16)),
        .str .r4 .r10 0])) rfl T10_noBase rfl

theorem setConst_relCT (k o x : Nat) : RelCT isa (VG.Arm.Taint.Agree T0) (Dynamic.setConst k o x) (VG.Arm.Taint.Agree T10) := by
  unfold Dynamic.setConst
  refine RelCT.seq (zeros_relCT false false k o) (RelCT.block_append (RelCT.seq ?_ (setConstWords_relCT k x)))
  exact erased_relCT (c₀ := .block (ptr .r10 0)) (VG.Taint.hintOf taint T0 (.block (ptr .r10 0))) rfl
    (wsT_noBase _ _) rfl

/-- Fewer public registers. -/
theorem agree_weaken {τ σ : taint.T} (h : taint.le σ τ = true) {s₁ s₂ : State} (A : VG.Arm.Taint.Agree τ s₁ s₂) :
    VG.Arm.Taint.Agree σ s₁ s₂ :=
  taint.le_sound h A

theorem relCT_weaken {P : State → State → Prop} {c : Prog isa} {τ σ : taint.T} (H : RelCT isa P c (VG.Arm.Taint.Agree τ))
    (h : taint.le σ τ = true) : RelCT isa P c (VG.Arm.Taint.Agree σ) :=
  H.mono (fun _ _ x => x) fun _ _ A => agree_weaken h A

theorem checkRange_relCT (k a m flag : Nat) :
    RelCT isa (VG.Arm.Taint.Agree T0) (checkRange k a m flag) (VG.Arm.Taint.Agree T0) :=
  erased_relCT (c₀ := checkRange 1 0 0 0) (VG.Taint.hintOf taint T0 (checkRange 1 0 0 0)) rfl (wsT_noBase _ _) rfl

theorem lessThan_relCT (k a b : Nat) :
    RelCT isa (VG.Arm.Taint.Agree T0) (lessThan k a b) (VG.Arm.Taint.Agree T0) :=
  erased_relCT (c₀ := lessThan 1 0 0) (VG.Taint.hintOf taint T0 (lessThan 1 0 0)) rfl (wsT_noBase _ _) rfl

theorem lessThanConstant_relCT (k a tmp x : Nat) :
    RelCT isa (VG.Arm.Taint.Agree T0) (lessThanConstant k a tmp x) (VG.Arm.Taint.Agree T0) :=
  RelCT.seq (relCT_weaken (setConst_relCT k tmp x) rfl) (lessThan_relCT k a tmp)

theorem lowerTwo_relCT (n : Nat) :
    RelCT isa (VG.Arm.Taint.Agree T0) (Validate.lowerTwo n) (VG.Arm.Taint.Agree T0) :=
  RelCT.seq (lessThanConstant_relCT _ _ _ _)
    (erased_relCT (c₀ := .block (allOnes ++ [.dp .eor .r2 .r2 (.reg .r4)] ++ Validate.accumulate))
      (VG.Taint.hintOf taint T0 (.block (allOnes ++ [.dp .eor .r2 .r2 (.reg .r4)] ++ Validate.accumulate)))
      rfl (wsT_noBase _ _) rfl)

theorem equalAcc_relCT (k a b : Nat) :
    RelCT isa (VG.Arm.Taint.Agree T0) (.seq (equal k a b) (.block Validate.accumulate)) (VG.Arm.Taint.Agree T0) :=
  erased_relCT (c₀ := .seq (equal 1 0 0) (.block Validate.accumulate))
    (VG.Taint.hintOf taint T0 (.seq (equal 1 0 0) (.block Validate.accumulate))) rfl (wsT_noBase _ _) rfl

theorem checkZero_relCT (k a flag : Nat) (want : Bool) :
    RelCT isa (VG.Arm.Taint.Agree T0) (checkZero k a flag want) (VG.Arm.Taint.Agree T0) := by
  cases want
  · exact erased_relCT (c₀ := checkZero 1 0 0 false) (VG.Taint.hintOf taint T0 (checkZero 1 0 0 false)) rfl
      (wsT_noBase _ _) rfl
  · exact erased_relCT (c₀ := checkZero 1 0 0 true) (VG.Taint.hintOf taint T0 (checkZero 1 0 0 true)) rfl
      (wsT_noBase _ _) rfl

theorem subWords_relCT (k o a b : Nat) :
    RelCT isa (VG.Arm.Taint.Agree T0) (subWords k o a b) (VG.Arm.Taint.Agree T0) :=
  erased_relCT (c₀ := subWords 1 0 0 0) (VG.Taint.hintOf taint T0 (subWords 1 0 0 0)) rfl (wsT_noBase _ _) rfl

theorem modulusMinus_relCT (n amount : Nat) :
    RelCT isa (VG.Arm.Taint.Agree T0) (modulusMinus n amount) (VG.Arm.Taint.Agree T0) :=
  RelCT.seq (relCT_weaken (setConst_relCT _ _ _) rfl) (subWords_relCT _ _ _ _)

theorem ordinaryMul_relCT (n : Nat) :
    RelCT isa (VG.Arm.Taint.Agree T0) (ordinaryMul n) (VG.Arm.Taint.Agree T0) :=
  RelCT.seq (mul_relCT false false _ _ _ _ _ _) (mul_relCT false false _ _ _ _ _ _)

theorem ordinaryAdd_relCT (n : Nat) :
    RelCT isa (VG.Arm.Taint.Agree T0) (ordinaryAdd n) (VG.Arm.Taint.Agree T0) :=
  addD_relCT false false _ _ _ _ _

theorem reduceHead_relCT (input : Pointer) (count : Core.Count) :
    RelCT isa (VG.Arm.Taint.Agree T0) (.block (Core.pointer input ++ Core.countEnd count)) (VG.Arm.Taint.Agree T0) := by
  cases count with
  | imm len =>
    exact RelCT.block_append (RelCT.seq (pointer_relCT input)
      (erased_relCT (c₀ := .block (Core.countEnd (.imm 0))) (VG.Taint.hintOf taint T0 (.block (Core.countEnd (.imm 0))))
        rfl (wsT_noBase _ _) rfl))
  | field f =>
    exact RelCT.block_append (RelCT.seq (pointer_relCT input)
      (erased_relCT (c₀ := .block (Core.countEnd (.field .p))) (VG.Taint.hintOf taint T0
        (.block (Core.countEnd (.field .p)))) rfl (wsT_noBase _ _) rfl))

theorem doubles_eraseOff (n k : Nat) : Code.eraseOff (doubles n k) = Code.eraseOff (doubles 1 k) := by
  unfold doubles
  split
  · rfl
  · rfl

theorem streamHead_eraseOff (k : Nat) :
    Code.eraseOff (@Code.block Instr Cond (([.ldrb .r4 .r11 0] : List Instr) ++ ptr .r10 k ++
        ([.str .r4 .r10 0] : List Instr))) =
      Code.eraseOff (@Code.block Instr Cond (([.ldrb .r4 .r11 0] : List Instr) ++ ptr .r10 0 ++
        ([.str .r4 .r10 0] : List Instr))) := rfl

theorem streamStep_eraseOff (n : Nat) : Code.eraseOff (streamStep n) = Code.eraseOff (streamStep 1) := by
  simp only [streamStep, reduceStep, eraseOff_seq, addD_eraseOff, doubles_eraseOff n 8, streamHead_eraseOff]

theorem reduceStream_eraseOff (n : Nat) : Code.eraseOff (reduceStream n) = Code.eraseOff (reduceStream 1) := by
  simp only [reduceStream, eraseOff_seq, eraseOff_ite, eraseOff_loop, zeros_eraseOff, streamStep_eraseOff n]

theorem reduceStream_relCT (n : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT true true)) (reduceStream n) (VG.Arm.Taint.Agree (wsT true true)) :=
  erased_relCT _ (reduceStream_eraseOff n) (wsT_noBase _ _) (by taint_decide)

theorem storeComponent_relCT (len input : Nat) :
    RelCT isa (VG.Arm.Taint.Agree T1) (storeComponent len input) (VG.Arm.Taint.Agree T0) :=
  erased_relCT (c₀ := storeComponent 4 0) (VG.Taint.hintOf taint T1 (storeComponent 4 0)) rfl (wsT_noBase _ _) rfl

theorem block_relCT_T0 (is : List Instr) (h : (taint.checkBlock T0 is).map (taint.le T0) = some true) :
    RelCT isa (VG.Arm.Taint.Agree T0) (.block is) (VG.Arm.Taint.Agree T0) :=
  relCT_of_check (h := .block []) h

theorem outBlock_relCT (qLen : Nat) (second : Bool) :
    RelCT isa (VG.Arm.Taint.Agree T0)
      (.block (SignVerify.outputPointer qLen second ++ ([.ldr .r3 .r12 (Layout.field .mask)] : List Instr)))
      (VG.Arm.Taint.Agree T0) := by
  cases second
  · exact erased_relCT (c₀ := .block (SignVerify.outputPointer 0 false ++ [.ldr .r3 .r12 0]))
      (VG.Taint.hintOf taint T0 (.block (SignVerify.outputPointer 0 false ++ [.ldr .r3 .r12 0]))) rfl
      (wsT_noBase _ _) rfl
  · exact erased_relCT (c₀ := .block (SignVerify.outputPointer 0 true ++ [.ldr .r3 .r12 0]))
      (VG.Taint.hintOf taint T0 (.block (SignVerify.outputPointer 0 true ++ [.ldr .r3 .r12 0]))) rfl
      (wsT_noBase _ _) rfl

theorem result_relCT : RelCT isa (VG.Arm.Taint.Agree T0) (.block SignVerify.result) (VG.Arm.Taint.Agree T0) :=
  relCT_of_check (h := .block []) rfl

end VG.Proof.Dsa.Arm
