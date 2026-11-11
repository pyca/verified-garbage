module

public import VerifiedGarbage.Proof.Bignum.Arm.PrimeR2From
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowCopyCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWideCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Bignum.Arm.SubModArray
import VerifiedGarbage.Proof.Bignum.Arm.SubModArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopCT
import VerifiedGarbage.Proof.Bignum.Arm.R2CT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowCopy
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowHalf
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeAcceptance
import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptanceCT
import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulus
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.PreparePrime
import VerifiedGarbage.Proof.Bignum.Arm.PrepareAcceptedPrimeCT
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayoutCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Bignum.Arm.PrimeR2From
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowCopyCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
meta import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWideCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
meta import VerifiedGarbage.Proof.Bignum.Arm.MontOp
meta import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SubModArray
meta import VerifiedGarbage.Proof.Bignum.Arm.SubModArrayCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
meta import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopCT
meta import VerifiedGarbage.Proof.Bignum.Arm.R2CT
meta import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowCopy
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowHalf
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPrime
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeAcceptance
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptanceCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
meta import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulus
meta import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
meta import VerifiedGarbage.Proof.Bignum.Arm.PreparePrime
meta import VerifiedGarbage.Proof.Bignum.Arm.PrepareAcceptedPrimeCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayoutCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.Stack
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge

-- separate module: its taint checks need meta imports of the fold's steps, which its importer does not.

/-! # A factor's `R² mod p` from `R² mod n` is constant-time

The fold's branches and counts depend only on the widths `w` and `v`, which
both runs share; its arrays and the factor stay secret. The headers' widths
are read through public pointers: the main workspace's from frame slot 8,
the narrow one's from r0.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest)

/-! ## Blocks and branches on public data -/

/-- A relational fact proven from the related states. -/
theorem relCT_of_pre {P Q : State → State → Prop} {c : Prog isa} (h : ∀ s t, P s t → RelCT isa P c Q) :
    RelCT isa P c Q :=
  fun s t tr1 tr2 u w hp e1 e2 => h s t hp s t tr1 tr2 u w hp e1 e2

/-- A branch both runs take the same way. -/
theorem crt_ite_ct {P1 P2 : State → Prop} {c : Cond} {a b : Prog isa} {cond : Bool}
    (h1 : ∀ s, P1 s → isa.eval c s = some cond) (h2 : ∀ s, P2 s → isa.eval c s = some cond)
    (ha : cond = true → RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) a (fun _ _ => True))
    (hb : cond = false → RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) b (fun _ _ => True)) :
    RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) (.ite c a b) (fun _ _ => True) := by
  refine RelCT.ite (fun s t h => (h1 s h.1).trans (h2 t h.2.1).symm) ?_ ?_
  · cases cond
    · exact RelCT.of_false fun s t h => by rw [h1 s h.1.1] at h; cases h.2
    · exact (ha rfl).mono (fun _ _ h => h.1) (fun _ _ _ => trivial)
  · cases cond
    · exact (hb rfl).mono (fun _ _ h => h.1) (fun _ _ _ => trivial)
    · exact RelCT.of_false fun s t h => by rw [h1 s h.1.1] at h; cases h.2

/-- A block whose loads are through r0 alone, with r0 public. -/
theorem r0Block_ct {P : State → State → Prop} {l : List Instr} {hc : Taint.Hint _}
    (r0 : ∀ s t, P s t → s.gpr .r0 = t.gpr .r0)
    (h : (taint.check (Taint.ofRegs [.r0]) (.block l) hc).isSome = true) :
    RelCT isa P (.block l) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.r0]) (fun s t hp => Taint.agree_ofRegs (by simpa using r0 s t hp)) h

/-- A block that loads the main workspace's pointer from frame slot 8 into r1,
then loads through it and r0. -/
theorem ctxBlock_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {child : BitVec 32} {slot v : Nat}
    {l : List Instr} {hc : Taint.Hint _}
    (h : (taint.check (Taint.ofRegs [.r0, .r1]) (.block l) hc).isSome = true) :
    RelCT isa (CrtCopyPair g bs1 bs2 child slot v) (.block (.ldrSp .r1 8 :: l)) (fun _ _ => True) := by
  let P := fun (s : State) => s.gpr .r0 = crtN g.base g.words ∧ s.gpr .r1 = g.base
  have one (s : State) {bs : Fin 7 → List Byte} (h : CrtCopyCtx g bs child slot v s) :
      WP isa (.block [.ldrSp .r1 8]) s P := by
    refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide)
      (addr_add (by have := h.shared.stack.nowrap; omega)) (h.shared.stack.read (by decide)) fun t a => WP.block_nil ?_
    exact ⟨(a.other .r0 (by decide)).trans h.ready.ptr, a.gpr.trans h.shared.savedMain⟩
  have first := RelCT.wp ((loadStack_ct .r1 8).mono (P' := CrtCopyPair g bs1 bs2 child slot v)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)) (fun s t h => ⟨one s h.1, one t h.2.1⟩)
  change RelCT isa _ (.block ([.ldrSp .r1 8] ++ l)) _
  apply RelCT.block_append
  refine first.seq (RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r1]) ?_ h)
  intro s t hp
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.2.1.1.trans hp.2.2.1.symm
  · exact hp.2.1.2.trans hp.2.2.2.symm

/-! ## The fold's reduction -/

/-- The fold's context, and arrays `os` below the modulus. -/
def FoldBound (g : CrtGeometry) (bs : Fin 7 → List Byte) (v : Nat) (os : List Nat) (s : State) : Prop :=
  CrtCopyCtx g bs (crtP g.base g.words) 224 v s ∧
    ∀ o ∈ os, numAt s.mem (State.addr (crtN g.base g.words)) v o < numAt s.mem (State.addr (crtN g.base g.words)) v 0

theorem foldOperand {o : Nat} (h : o = 1 ∨ o = 4 ∨ o = 5 ∨ o = 6 ∨ o = 7) : Operand o := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]

/-- A step that writes array `o'` keeps the bounds of the others. -/
theorem FoldBound.after {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {v o' : Nat}
    {os : List Nat} {rs : List Reg} (h : FoldBound g bs v os s)
    (ready : ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t)
    (keeps : Keeps (State.addr (crtN g.base g.words)) (workspaceWords g.words) v o' s.mem t.mem)
    (ho' : o' ≠ 0) (hos : ∀ o ∈ os, o ≠ o' ∧ (o = 1 ∨ o = 4 ∨ o = 5 ∨ o = 6 ∨ o = 7))
    (frame : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem)
    (rest : Rest rs s t) : FoldBound g bs v os t := by
  have fits : arrAt v 8 ≤ 8 * workspaceWords g.words := h.1.ready.width ▸ h.1.ready.layout.2.2.1
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine ⟨h.1.after_narrow ready frame rest, fun o ho => ?_⟩
  rw [keeps_array_num keeps fits (foldOperand (hos o ho).2) (hos o ho).1,
    keeps_array_num keeps fits op0 (Ne.symm ho')]
  exact h.2 o ho

theorem FoldBound.sub {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {v : Nat} {os os' : List Nat}
    (h : FoldBound g bs v os s) (sub : ∀ o ∈ os', o ∈ os) : FoldBound g bs v os' s :=
  ⟨h.1, fun o ho => h.2 o (sub o ho)⟩

theorem FoldBound.cons {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {v o : Nat} {os : List Nat}
    (h : FoldBound g bs v os s)
    (b : numAt s.mem (State.addr (crtN g.base g.words)) v o < numAt s.mem (State.addr (crtN g.base g.words)) v 0) :
    FoldBound g bs v (o :: os) s :=
  ⟨h.1, fun q hq => by
    rcases List.mem_cons.mp hq with rfl | hq
    · exact b
    · exact h.2 q hq⟩

theorem FoldBound.get {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {v o : Nat} {os : List Nat}
    (h : FoldBound g bs v os s) (ho : o ∈ os := by decide) :
    numAt s.mem (State.addr (crtN g.base g.words)) v o < numAt s.mem (State.addr (crtN g.base g.words)) v 0 :=
  h.2 o ho

theorem foldReduce_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {v : Nat} (half : g.words ≤ 2 * v) :
    RelCT isa (fun s t => FoldBound g bs1 v [] s ∧ FoldBound g bs2 v [] t ∧ s.sp = t.sp) foldReduce
      (fun _ _ => True) := by
  have large (s : State) {bs : Fin 7 → List Byte} {os : List Nat} (h : FoldBound g bs v os s) :
      1 < numAt s.mem (State.addr (crtN g.base g.words)) v 0 := h.1.ready.modulus
  have fits (s : State) {bs : Fin 7 → List Byte} {os : List Nat} (h : FoldBound g bs v os s) :
      arrAt v 8 ≤ 8 * workspaceWords g.words := h.1.ready.width ▸ h.1.ready.layout.2.2.1
  -- Each step in each run.
  have w1 (s : State) {bs : Fin 7 → List Byte} (h : FoldBound g bs v [] s) : WP isa (smallConst 7 1) s (FoldBound g bs v [7]) :=
    (smallConst_ok s (o := 7) 1 h.1.ready (by decide) (by decide) (by decide) (by decide)).mono
      fun t k => (h.after k.1 k.2.2.2.1 (by decide) (by decide) k.2.2.2.2.1 k.2.2.2.2.2).cons
        (by rw [k.2.1]; exact large t (h.after k.1 k.2.2.2.1 (by decide) (by decide) k.2.2.2.2.1 k.2.2.2.2.2))
  have w2 (s : State) {bs : Fin 7 → List Byte} (h : FoldBound g bs v [7] s) :
      WP isa (clearOperandBuffer 104) s (FoldBound g bs v [5, 7]) := by
    refine (clearArrayWide_ok s h.1.ready (o := 5) (by decide) (by decide)).mono ?_
    rintro t ⟨ready, cleared, keeps, frame, rest⟩
    have ht := h.after ready keeps (by decide) (by decide) frame rest
    exact ht.cons (by rw [numAt_of_cleared cleared]; have := large t ht; omega)
  have w3 (s : State) {bs : Fin 7 → List Byte} (h : FoldBound g bs v [5, 7] s) :
      WP isa (clearOperandBuffer 72) s (FoldBound g bs v [5, 7]) :=
    (clearArrayWide_ok s h.1.ready (o := 1) (by decide) (by decide)).mono
      fun _ k => h.after k.1 k.2.2.1 (by decide) (by decide) k.2.2.2.1 k.2.2.2.2
  have w4 (s : State) {bs : Fin 7 → List Byte} (h : FoldBound g bs v [5, 7] s) :
      WP isa (copyHigh 224 4 1) s (FoldBound g bs v [5, 7]) :=
    (crt_copyHigh_ok s h.1 (j := 4) (d := 1) (by decide) (by decide) (by decide) half).mono
      fun _ k => h.after k.1 k.2.2.1 (by decide) (by decide) k.2.2.2.1 k.2.2.2.2
  have w5 (s : State) {bs : Fin 7 → List Byte} (h : FoldBound g bs v [5, 7] s) :
      WP isa (copyLow 224 4 6) s (FoldBound g bs v [5, 7]) :=
    (crt_copyLow_ok s h.1 (j := 4) (d := 6) (by decide) (by decide) (by decide)).mono
      fun _ k => h.after k.1 k.2.2.1 (by decide) (by decide) k.2.2.2.1 k.2.2.2.2
  have w6 (s : State) {bs : Fin 7 → List Byte} (h : FoldBound g bs v [5, 7] s) :
      WP isa (montOp 1 1 7) s (FoldBound g bs v [1, 5, 7]) := by
    refine (montOp_ok s h.1.ready (foldOperand (by decide)) (foldOperand (by decide)) (foldOperand (by decide))
      (by decide) h.get).mono ?_
    rintro t ⟨ready, mod, bound, _, keeps, frame, rest⟩
    exact (h.after ready keeps (by decide) (by decide) frame rest).cons (by rw [mod]; exact bound)
  have w7 (s : State) {bs : Fin 7 → List Byte} (h : FoldBound g bs v [1, 5, 7] s) :
      WP isa (montOp 6 6 7) s (FoldBound g bs v [6, 1, 5, 7]) := by
    refine (montOp_ok s h.1.ready (foldOperand (by decide)) (foldOperand (by decide)) (foldOperand (by decide))
      (by decide) h.get).mono ?_
    rintro t ⟨ready, mod, bound, _, keeps, frame, rest⟩
    exact (h.after ready keeps (by decide) (by decide) frame rest).cons (by rw [mod]; exact bound)
  have w8 (s : State) {bs : Fin 7 → List Byte} (h : FoldBound g bs v [6, 1, 5, 7] s) :
      WP isa (montOp 6 6 7) s (FoldBound g bs v [6, 1, 5, 7]) := w7 s (h.sub (by decide))
  have w9 (s : State) {bs : Fin 7 → List Byte} (h : FoldBound g bs v [6, 1, 5, 7] s) :
      WP isa (subModArray 4 5 1) s (FoldBound g bs v [4, 6, 1, 5, 7]) := by
    refine (subModArray_ok s h.1.ready (o := 4) (a := 5) (b := 1) (foldOperand (by decide)) (foldOperand (by decide))
      (foldOperand (by decide)) (by decide) (by decide) (by decide) h.get h.get).mono ?_
    rintro t ⟨ready, value, keeps, frame, rest⟩
    have ht := h.after ready keeps (by decide) (by decide) frame rest
    refine ht.cons ?_
    rw [value, keeps_array_num keeps (fits s h) (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by decide)]
    exact Nat.mod_lt _ (by have := large s h; omega)
  have w10 (s : State) {bs : Fin 7 → List Byte} (h : FoldBound g bs v [4, 6, 1, 5, 7] s) :
      WP isa (subModArray 1 6 4) s (FoldBound g bs v [1, 4, 6, 5, 7]) := by
    refine (subModArray_ok s h.1.ready (o := 1) (a := 6) (b := 4) (foldOperand (by decide)) (foldOperand (by decide))
      (foldOperand (by decide)) (by decide) (by decide) (by decide) h.get h.get).mono ?_
    rintro t ⟨ready, value, keeps, frame, rest⟩
    have ht := (h.sub (os' := [4, 6, 5, 7]) (by decide)).after ready keeps (by decide) (by decide) frame rest
    refine ht.cons ?_
    rw [value, keeps_array_num keeps (fits s h) (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by decide)]
    exact Nat.mod_lt _ (by have := large s h; omega)
  have w11 (s : State) {bs : Fin 7 → List Byte} (h : FoldBound g bs v [1, 4, 6, 5, 7] s) :
      WP isa (subModArray 4 1 5) s (FoldBound g bs v [4]) := by
    refine (subModArray_ok s h.1.ready (o := 4) (a := 1) (b := 5) (foldOperand (by decide)) (foldOperand (by decide))
      (foldOperand (by decide)) (by decide) (by decide) (by decide) h.get h.get).mono ?_
    rintro t ⟨ready, value, keeps, frame, rest⟩
    have ht := (h.sub (os' := []) (by decide)).after ready keeps (by decide) (by decide) frame rest
    refine ht.cons ?_
    rw [value, keeps_array_num keeps (fits s h) (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by decide)]
    exact Nat.mod_lt _ (by have := large s h; omega)
  -- Each step in both runs.
  have size (s : State) {bs : Fin 7 → List Byte} {os : List Nat} (h : FoldBound g bs v os s) : 128 ≤ 8 * workspaceWords g.words := by
    have := fits s h
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
    omega
  have fit3 (s : State) {bs : Fin 7 → List Byte} {os : List Nat} (h : FoldBound g bs v os s) : arrAt v 3 + 32 ≤ 8 * workspaceWords g.words := by
    have := Nat.le_trans (array_end_le (w := v) (by decide : 3 < 8)) (fits s h)
    have hv : 2 ≤ v := h.1.ready.width ▸ h.1.ready.layout.1
    omega
  intro s₁ s₂ tr1 tr2 u₁ u₂ hh e1 e2
  have sz := size s₁ hh.1
  have f3 := fit3 s₁ hh.1
  let Rel := fun (os : List Nat) (s t : State) => FoldBound g bs1 v os s ∧ FoldBound g bs2 v os t ∧ s.sp = t.sp
  have ready (os : List Nat) : ∀ s t, Rel os s t →
      ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v s ∧ ArithmeticReady (crtN g.base g.words) (workspaceWords g.words) v t ∧ s.sp = t.sp :=
    fun _ _ h => ⟨h.1.1.ready, h.2.1.1.ready, h.2.2⟩
  have mont (os : List Nat) (b : Nat) (hb : b ∈ os) (o a : Nat) (ho : Operand o) (ha : Operand a) (hbo : Operand b) :
      RelCT isa (Rel os) (montOp o a b) (fun _ _ => True) :=
    (montOp_ct ho ha hbo f3).mono (fun _ _ h => ⟨⟨h.1.1.ready, h.1.get hb⟩, ⟨h.2.1.1.ready, h.2.1.get hb⟩, h.2.2⟩)
      (fun _ _ _ => trivial)
  have subm (os : List Nat) (o a b : Nat) (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho0 : o ≠ 0) :
      RelCT isa (Rel os) (subModArray o a b) (fun _ _ => True) :=
    (subModArray_ct ho ha hb ho0 sz).mono (ready os) (fun _ _ _ => trivial)
  have c1 : RelCT isa (Rel []) (smallConst 7 1) (fun _ _ => True) :=
    (smallConst_ct (o := 7) 1 (by decide) (by decide) (by decide)).mono (ready []) (fun _ _ _ => trivial)
  have c2 : RelCT isa (Rel [7]) (clearOperandBuffer (64 + 8 * 5)) (fun _ _ => True) :=
    (clearArrayWide_ct (by decide) sz).mono (ready [7]) (fun _ _ _ => trivial)
  have c3 : RelCT isa (Rel [5, 7]) (clearOperandBuffer (64 + 8 * 1)) (fun _ _ => True) :=
    (clearArrayWide_ct (by decide) sz).mono (ready [5, 7]) (fun _ _ _ => trivial)
  have c4 : RelCT isa (Rel [5, 7]) (copyHigh 224 4 1) (fun _ _ => True) :=
    (crt_copyHigh_ct (by decide) (by decide)).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  have c5 : RelCT isa (Rel [5, 7]) (copyLow 224 4 6) (fun _ _ => True) :=
    (crt_copyLow_ct (by decide) (by decide)).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  have all := crt_seq_ct c1 (fun s h => w1 s h) (fun s h => w1 s h)
    (crt_seq_ct c2 (fun s h => w2 s h) (fun s h => w2 s h)
      (crt_seq_ct c3 (fun s h => w3 s h) (fun s h => w3 s h)
        (crt_seq_ct c4 (fun s h => w4 s h) (fun s h => w4 s h)
          (crt_seq_ct c5 (fun s h => w5 s h) (fun s h => w5 s h)
            (crt_seq_ct (mont [5, 7] 7 (by decide) 1 1 (foldOperand (by decide)) (foldOperand (by decide))
                (foldOperand (by decide))) (fun s h => w6 s h) (fun s h => w6 s h)
              (crt_seq_ct (mont [1, 5, 7] 7 (by decide) 6 6 (foldOperand (by decide)) (foldOperand (by decide))
                  (foldOperand (by decide))) (fun s h => w7 s h) (fun s h => w7 s h)
                (crt_seq_ct (mont [6, 1, 5, 7] 7 (by decide) 6 6 (foldOperand (by decide))
                    (foldOperand (by decide)) (foldOperand (by decide))) (fun s h => w8 s h) (fun s h => w8 s h)
                  (crt_seq_ct (subm [6, 1, 5, 7] 4 5 1 (by decide) (by decide) (by decide) (by decide))
                      (fun s h => w9 s h) (fun s h => w9 s h)
                    (crt_seq_ct (subm [4, 6, 1, 5, 7] 1 6 4 (by decide) (by decide) (by decide) (by decide))
                        (fun s h => w10 s h) (fun s h => w10 s h)
                      (subm [1, 4, 6, 5, 7] 4 1 5 (by decide) (by decide) (by decide) (by decide)))))))))))
  exact all s₁ s₂ tr1 tr2 u₁ u₂ hh e1 e2

theorem foldReduce_wp (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {v : Nat}
    (h : CrtCopyCtx g bs (crtP g.base g.words) 224 v s) (half : g.words ≤ 2 * v) :
    WP isa foldReduce s (FoldBound g bs v [4]) := by
  refine WP.mono (crt_foldReduce_ok s h half rfl) ?_
  rintro t ⟨ready, mod, lt, _, frame, rest⟩
  exact ⟨h.after_narrow ready frame rest, fun o ho => by
    simp only [List.mem_singleton] at ho; subst o; rw [mod]; exact lt⟩

/-! ## The counts, the doublings and the squarings -/

/-- The fold's context and a doubling count. -/
def FoldCount (g : CrtGeometry) (bs : Fin 7 → List Byte) (v c : Nat) (s : State) : Prop :=
  CrtCopyCtx g bs (crtP g.base g.words) 224 v s ∧
    DoubleLoopReady (crtN g.base g.words) (workspaceWords g.words) v c s

theorem FoldCount.of_regs {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {v c : Nat} {rs : List Reg}
    (h : FoldCount g bs v c s) (mem : t.mem = s.mem) (rest : Rest rs s t) (r0 : Reg.r0 ∉ rs) :
    FoldCount g bs v c t :=
  ⟨h.1.of_regs mem rest ((rest.gpr .r0 r0).trans h.1.ready.ptr), h.2.of_regs mem rest r0⟩

theorem FoldCount.after {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {v c c' : Nat} {rs : List Reg}
    (h : FoldCount g bs v c s) (d : DoubleLoopReady (crtN g.base g.words) (workspaceWords g.words) v c' t)
    (frame : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem)
    (rest : Rest rs s t)
    (mod : numAt t.mem (State.addr (crtN g.base g.words)) v 0 = numAt s.mem (State.addr (crtN g.base g.words)) v 0) :
    FoldCount g bs v c' t :=
  ⟨h.1.after_narrow (d.toReady (by rw [mod]; exact h.1.ready.modulus)) frame rest, d⟩

theorem smallTwo_wp (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {v : Nat}
    (h : FoldBound g bs v [4] s) :
    WP isa (smallConst 7 2) s fun t => ∃ c, FoldCount g bs v c t := by
  have fits : arrAt v 8 ≤ 8 * workspaceWords g.words := h.1.ready.width ▸ h.1.ready.layout.2.2.1
  refine (smallConst_ok s (o := 7) 2 h.1.ready (by decide) (by decide) (by decide) (by decide)).mono ?_
  rintro t ⟨ready, _, two, keeps, frame, rest⟩
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have mod := keeps_array_num keeps fits op0 (by decide)
  have a4 := keeps_array_num keeps fits (foldOperand (o := 4) (by decide)) (by decide)
  exact ⟨(t.mem.readW (off (State.addr (crtN g.base g.words)) 208) 32).toNat, h.1.after_narrow ready frame rest,
    ready.workspace, ready.layout, ready.width, ready.ptr, ready.inverse,
    by rw [a4, mod]; exact h.get, two, by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq],
    ready.stackRead, ready.stackSep, ready.saved⟩

theorem foldCounts_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {v : Nat} (half : g.words ≤ 2 * v) :
    RelCT isa (fun s t => (∃ c, FoldCount g bs1 v c s) ∧ (∃ c, FoldCount g bs2 v c t) ∧ s.sp = t.sp) foldCounts
      (fun _ _ => True) := by
  let A := fun (bs : Fin 7 → List Byte) (s : State) =>
    (∃ c, FoldCount g bs v c s) ∧ s.z = decide (2 * (g.words - v) ≤ v)
  have argsWP (s : State) {bs : Fin 7 → List Byte} (h : ∃ c, FoldCount g bs v c s) :
      WP isa (.block foldCountArgs) s (A bs) := by
    obtain ⟨c, h⟩ := h
    refine (foldCountArgs_ok s h.1 half).mono ?_
    rintro t ⟨_, _, z, mem, rest⟩
    exact ⟨⟨c, h.of_regs mem rest (by decide)⟩, z⟩
  have args : RelCT isa (fun s t => (∃ c, FoldCount g bs1 v c s) ∧ (∃ c, FoldCount g bs2 v c t) ∧ s.sp = t.sp)
      (.block foldCountArgs) (fun _ _ => True) :=
    (ctxBlock_ct (by taint_decide)).mono (fun _ _ h => by
      obtain ⟨⟨_, h1⟩, ⟨_, h2⟩, sp⟩ := h
      exact ⟨h1.1, h2.1, sp⟩) (fun _ _ _ => trivial)
  have r0 : ∀ s t, A bs1 s ∧ A bs2 t ∧ s.sp = t.sp → s.gpr .r0 = t.gpr .r0 := fun _ _ h => by
    obtain ⟨⟨⟨_, h1⟩, _⟩, ⟨⟨_, h2⟩, _⟩, _⟩ := h
    exact h1.1.ready.ptr.trans h2.1.ready.ptr.symm
  have low : RelCT isa (fun s t => A bs1 s ∧ A bs2 t ∧ s.sp = t.sp) (.block foldCountLow) (fun _ _ => True) :=
    r0Block_ct r0 (by taint_decide)
  have high : RelCT isa (fun s t => A bs1 s ∧ A bs2 t ∧ s.sp = t.sp) (.block foldCountHigh) (fun _ _ => True) :=
    r0Block_ct r0 (by taint_decide)
  rw [foldCounts]
  exact crt_seq_ct args (fun s h => argsWP s h) (fun s h => argsWP s h)
    (crt_ite_ct (cond := decide (2 * (g.words - v) ≤ v)) (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2])
      (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2]) (fun _ => low) (fun _ => high))

theorem foldCounts_wp (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {v : Nat} (half : g.words ≤ 2 * v)
    (h : ∃ c, FoldCount g bs v c s) : WP isa foldCounts s (FoldCount g bs v (foldC g.words v)) := by
  obtain ⟨c, h⟩ := h
  refine (foldCounts_ok s h.1 half h.2).mono ?_
  rintro t ⟨d, frame, _, mod, rest⟩
  exact h.after d frame rest mod

theorem foldDoubles_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {v c : Nat} (hc : c < 2 ^ 32) :
    RelCT isa (fun s t => FoldCount g bs1 v c s ∧ FoldCount g bs2 v c t ∧ s.sp = t.sp) foldDoubles
      (fun _ _ => True) := by
  let A := fun (bs : Fin 7 → List Byte) (s : State) => FoldCount g bs v c s ∧ s.z = decide (c = 0)
  have testWP (s : State) {bs : Fin 7 → List Byte} (h : FoldCount g bs v c s) :
      WP isa (.block [.ldr .r1 .r0 208, .cmp .r1 (.imm 0)]) s (A bs) := by
    refine (doublesTest_ok s h.2 hc).mono ?_
    rintro t ⟨_, z, mem, rest⟩
    exact ⟨h.of_regs mem rest (by decide), z⟩
  have test : RelCT isa (fun s t => FoldCount g bs1 v c s ∧ FoldCount g bs2 v c t ∧ s.sp = t.sp)
      (.block [.ldr .r1 .r0 208, .cmp .r1 (.imm 0)]) (fun _ _ => True) :=
    r0Block_ct (fun _ _ h => h.1.2.ptr.trans h.2.1.2.ptr.symm) (by taint_decide)
  rw [foldDoubles]
  exact crt_seq_ct test (fun s h => testWP s h) (fun s h => testWP s h)
    (crt_ite_ct (cond := decide (c = 0)) (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2])
      (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2])
      (fun _ => RelCT.block_nil (fun _ _ _ => trivial))
      (fun hc0 => (doubleLoop_ct (c := c) (by simp only [decide_eq_false_iff_not] at hc0; omega) hc).mono
        (fun _ _ h => ⟨h.1.1.2, h.2.1.1.2, h.2.2⟩) (fun _ _ _ => trivial)))

theorem foldDoubles_wp (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {v c : Nat} (hc : c < 2 ^ 32)
    (h : FoldCount g bs v c s) : WP isa foldDoubles s (FoldCount g bs v 0) := by
  refine (foldDoubles_ok s h.2 hc).mono ?_
  rintro t ⟨d, _, mod, frame, rest⟩
  exact h.after d frame rest mod

/-- The squarings' states, for some modulus; their values do not matter here. -/
def FoldSqRel (base : BitVec 32) (len w k : Nat) (s t : State) : Prop :=
  (∃ m, FoldSq base len w m False k s) ∧ (∃ m, FoldSq base len w m False k t) ∧ s.sp = t.sp

theorem foldSquare_ct {base : BitVec 32} {len w k : Nat} :
    RelCT isa (FoldSqRel base len w k) (squareOp 4 4) (FoldSqRel base len w (2 * k)) := by
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have ct := relCT_keep_sp ((squareOp_ct (base := base) (len := len) (w := w) op4 op4).mono
    (P' := FoldSqRel base len w k)
    (fun _ _ h => by
      obtain ⟨⟨m1, h1⟩, ⟨m2, h2⟩, sp⟩ := h
      exact ⟨⟨h1.ready, by rw [h1.modulus]; exact h1.operand⟩,
        ⟨h2.ready, by rw [h2.modulus]; exact h2.operand⟩, sp⟩)
    (fun _ _ _ => trivial)) (fun _ _ h => h.2.2)
  have post (s : State) (h : ∃ m, FoldSq base len w m False k s) :
      WP isa (squareOp 4 4) s fun t => ∃ m, FoldSq base len w m False (2 * k) t := by
    obtain ⟨m, hm⟩ := h
    exact WP.mono (foldSquare_ok s hm) fun t ht => ⟨m, ht.1⟩
  exact (ct.wp (fun s t h => ⟨post s h.1, post t h.2.1⟩)).mono (fun _ _ h => h)
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)

theorem foldSquares6_ct {base : BitVec 32} {len w k : Nat} :
    RelCT isa (FoldSqRel base len w k) r2Squares (fun _ _ => True) := by
  unfold r2Squares
  exact foldSquare_ct.seq (foldSquare_ct.seq (foldSquare_ct.seq (foldSquare_ct.seq (foldSquare_ct.seq
    (foldSquare_ct.mono (fun _ _ h => h) (fun _ _ _ => trivial))))))

theorem FoldCount.foldSq {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {v : Nat} (k : Nat)
    (h : FoldCount g bs v 0 s) :
    ∃ m, FoldSq (crtN g.base g.words) (workspaceWords g.words) v m False k s :=
  ⟨_, h.2.toReady h.1.ready.modulus, rfl, h.2.operand, False.elim, h.2.two, h.2.counter⟩

theorem foldSquares_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {v : Nat} (half : g.words ≤ 2 * v) :
    RelCT isa (fun s t => FoldCount g bs1 v 0 s ∧ FoldCount g bs2 v 0 t ∧ s.sp = t.sp) foldSquares
      (fun _ _ => True) := by
  let A := fun (bs : Fin 7 → List Byte) (s : State) => FoldCount g bs v 0 s ∧ s.z = decide (2 * (g.words - v) ≤ v)
  have argsWP (s : State) {bs : Fin 7 → List Byte} (h : FoldCount g bs v 0 s) :
      WP isa (.block foldCountArgs) s (A bs) := by
    refine (foldCountArgs_ok s h.1 half).mono ?_
    rintro t ⟨_, _, z, mem, rest⟩
    exact ⟨h.of_regs mem rest (by decide), z⟩
  have args : RelCT isa (fun s t => FoldCount g bs1 v 0 s ∧ FoldCount g bs2 v 0 t ∧ s.sp = t.sp)
      (.block foldCountArgs) (fun _ _ => True) :=
    (ctxBlock_ct (by taint_decide)).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  rw [foldSquares]
  exact crt_seq_ct args (fun s h => argsWP s h) (fun s h => argsWP s h)
    (crt_ite_ct (cond := decide (2 * (g.words - v) ≤ v)) (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2])
      (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2])
      (fun _ => (foldSquares6_ct (k := v)).mono (fun _ _ h => ⟨h.1.1.foldSq v, h.2.1.1.foldSq v, h.2.2⟩)
        (fun _ _ _ => trivial))
      (fun _ => RelCT.block_nil (fun _ _ _ => trivial)))

/-! ## The fold, and its choice -/

theorem r2Fold_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {v : Nat} (half : g.words ≤ 2 * v) :
    RelCT isa (fun s t => FoldBound g bs1 v [] s ∧ FoldBound g bs2 v [] t ∧ s.sp = t.sp) r2Fold
      (fun _ _ => True) := by
  refine relCT_of_pre fun s0 _ h0 => ?_
  have words : foldC g.words v < 2 ^ 32 := by
    have : g.words ≤ 128 := (crt_width_valid h0.1.1.shared.buffers.lengthValid).2.1
    have := h0.1.1.le
    unfold foldC
    split <;> omega
  have two : RelCT isa (fun s t => FoldBound g bs1 v [4] s ∧ FoldBound g bs2 v [4] t ∧ s.sp = t.sp)
      (smallConst 7 2) (fun _ _ => True) :=
    (smallConst_ct (o := 7) 2 (by decide) (by decide) (by decide)).mono
      (fun _ _ h => ⟨h.1.1.ready, h.2.1.1.ready, h.2.2⟩) (fun _ _ _ => trivial)
  rw [r2Fold]
  refine crt_seq_ct (foldReduce_ct half) (fun s h => foldReduce_wp s h.1 half) (fun s h => foldReduce_wp s h.1 half)
    (crt_seq_ct two (fun s h => smallTwo_wp s h) (fun s h => smallTwo_wp s h)
      (crt_seq_ct (foldCounts_ct half) (fun s h => foldCounts_wp s half h) (fun s h => foldCounts_wp s half h)
        (crt_seq_ct (foldDoubles_ct words) (fun s h => foldDoubles_wp s words h)
          (fun s h => foldDoubles_wp s words h) (foldSquares_ct half))))

theorem r2FromN_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {v : Nat} :
    RelCT isa (CrtCopyPair g bs1 bs2 (crtP g.base g.words) 224 v) r2FromN (fun _ _ => True) := by
  let A := fun (bs : Fin 7 → List Byte) (s : State) =>
    CrtCopyCtx g bs (crtP g.base g.words) 224 v s ∧ s.z = decide (g.words ≤ 2 * v)
  have testWP (s : State) {bs : Fin 7 → List Byte} (h : CrtCopyCtx g bs (crtP g.base g.words) 224 v s) :
      WP isa (.block foldTest) s (A bs) := by
    refine (foldTest_ok s h).mono ?_
    rintro t ⟨z, mem, rest⟩
    exact ⟨h.of_regs mem rest ((rest.gpr .r0 (by decide)).trans h.ready.ptr), z⟩
  have test : RelCT isa (CrtCopyPair g bs1 bs2 (crtP g.base g.words) 224 v) (.block foldTest)
      (fun _ _ => True) := ctxBlock_ct (by taint_decide)
  rw [r2FromN]
  exact crt_seq_ct test (fun s h => testWP s h) (fun s h => testWP s h)
    (crt_ite_ct (cond := decide (g.words ≤ 2 * v)) (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2])
      (fun s h => by rw [VG.Proof.X25519.Arm.eval_eq, h.2])
      (fun hc => (r2Fold_ct (of_decide_eq_true hc)).mono
        (fun _ _ h => ⟨⟨h.1.1, by simp⟩, ⟨h.2.1.1, by simp⟩, h.2.2⟩) (fun _ _ _ => trivial))
      (fun _ => relCT_of_pre fun s t h => (r2_ct (by
          have : g.words ≤ 128 := (crt_width_valid h.1.1.shared.buffers.lengthValid).2.1
          have := h.1.1.le
          omega)).mono (fun _ _ h => ⟨h.1.1.ready, h.2.1.1.ready, h.2.2⟩) (fun _ _ _ => trivial)))

/-! ## The factor's preparation -/

/-- `PrepareAcceptedPrimeCT`'s private `sanitizeModulus_ready`. -/
theorem sanitizeModulus_precompute (s : State) {base : BitVec 32} {len w : Nat}
    (h : PrimeInput base len w s) : WP isa sanitizeModulus s (PrecomputeModulus base len w) := by
  refine WP.mono (sanitizeModulus_ok s h.workspace h.layout h.width h.ptr h.bit h.stackRead h.stackSep h.saved) ?_
  rintro t ⟨layout, width, value, _, frame, rest, ptr⟩
  have valid := safePrime_valid h.valid
  change numAt t.mem (State.addr base) w 0 = safePrime _ _ at value
  refine ⟨⟨h.workspace.congr rest.wr, layout, width, ptr, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
  · rw [rest.sp]; exact h.stackSep
  · exact saved_base_kept frame h.stackSep h.saved rest.sp
  · rw [value]; exact valid.1
  · rw [value]; exact valid.2

theorem crt_narrowPrimeInv_ct {base pp : BitVec 32} {len v k ps : Nat} {pb1 pb2 : List Byte} :
    RelCT isa (fun s t => NarrowPrimeInput base pp len v k ps pb1 s ∧ NarrowPrimeInput base pp len v k ps pb2 t ∧
      s.sp = t.sp) (narrowPrimeInv ps) (fun _ _ => True) := by
  have load : RelCT isa (fun s t => NarrowPrimeInput base pp len v k ps pb1 s ∧
      NarrowPrimeInput base pp len v k ps pb2 t ∧ s.sp = t.sp) (savedOperand 0 ps (ps + 4)) (fun _ _ => True) :=
    (savedOperandLayout_ct (by decide : 0 < 8)).mono
      (fun _ _ h => ⟨⟨h.1.toLayoutFrameReady, h.1.source⟩, ⟨h.2.1.toLayoutFrameReady, h.2.1.source⟩, h.2.2⟩)
      (fun _ _ _ => trivial)
  have loadWP (s : State) {pb : List Byte} (h : NarrowPrimeInput base pp len v k ps pb s) :
      WP isa (savedOperand 0 ps (ps + 4)) s (AcceptedPrimeInput base len v) :=
    (crt_narrowImport_ok s h).mono fun _ j => j.1
  have install : RelCT isa (fun s t => AcceptedPrimeInput base len v s ∧ AcceptedPrimeInput base len v t ∧ s.sp = t.sp)
      (.block installAcceptance) (fun _ _ => True) :=
    crt_installAcceptance_ct.mono (fun _ _ h => ⟨h.1.ptr.trans h.2.1.ptr.symm, h.2.2⟩) (fun _ _ _ => trivial)
  have installWP (s : State) (h : AcceptedPrimeInput base len v s) :
      WP isa (.block installAcceptance) s (PrimeInput base len v) :=
    (crt_primeAcceptance_ready s h.toLayoutFrameReady h.stackFit h.flagRead h.bit h.valid).mono (fun _ j => j.1)
  have sanitize : RelCT isa (fun s t => PrimeInput base len v s ∧ PrimeInput base len v t ∧ s.sp = t.sp)
      sanitizeModulus (fun _ _ => True) :=
    sanitizeModulus_ct.mono (fun _ _ h => ⟨h.1.toLayoutFrameReady, h.2.1.toLayoutFrameReady, h.2.2⟩)
      (fun _ _ _ => trivial)
  have inverse : RelCT isa (fun s t => PrecomputeModulus base len v s ∧ PrecomputeModulus base len v t ∧ s.sp = t.sp)
      precomputeInverse (fun _ _ => True) :=
    precomputeInverse_ct.mono (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ _ => trivial)
  rw [narrowPrimeInv]
  exact crt_seq_ct load (fun s h => loadWP s h) (fun s h => loadWP s h)
    (crt_seq_ct install (fun s h => installWP s h) (fun s h => installWP s h)
      (crt_seq_ct sanitize (fun s h => sanitizeModulus_precompute s h)
        (fun s h => sanitizeModulus_precompute s h) inverse))

theorem crt_narrowPrimeFrom_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {pp : BitVec 32} {v k ps : Nat}
    {pb1 pb2 : List Byte} (le : v ≤ g.words) :
    RelCT isa (fun s t =>
      (CrtShared g bs1 s ∧ NarrowPrimeInput (crtN g.base g.words) pp (workspaceWords g.words) v k ps pb1 s) ∧
      (CrtShared g bs2 t ∧ NarrowPrimeInput (crtN g.base g.words) pp (workspaceWords g.words) v k ps pb2 t) ∧
      s.sp = t.sp) (narrowPrimeFrom ps) (fun _ _ => True) := by
  have invWP (s : State) {bs : Fin 7 → List Byte} {pb : List Byte}
      (h : CrtShared g bs s ∧ NarrowPrimeInput (crtN g.base g.words) pp (workspaceWords g.words) v k ps pb s) :
      WP isa (narrowPrimeInv ps) s (CrtCopyCtx g bs (crtP g.base g.words) 224 v) := by
    refine (crt_narrowPrimeInv_ok s h.2).mono ?_
    rintro u ⟨readyU, _, _, _, frameU, restU⟩
    exact (h.1.after_narrow (frameU.mono (by simp)) restU).copyCtx (Or.inl ⟨rfl, rfl⟩) readyU le
  rw [narrowPrimeFrom]
  exact crt_seq_ct (crt_narrowPrimeInv_ct.mono (fun _ _ h => ⟨h.1.2, h.2.1.2, h.2.2⟩) (fun _ _ _ => trivial))
    (fun s h => invWP s h) (fun s h => invWP s h) (r2FromN_ct.mono (fun _ _ h => h) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
