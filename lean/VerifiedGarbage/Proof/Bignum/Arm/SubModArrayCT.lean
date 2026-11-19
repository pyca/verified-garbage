module

public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Bignum.Arm.SubModArray
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
meta import VerifiedGarbage.Impl.Bignum.Arm.SubModArray
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Bignum.Arm.SubModArrayArgs
import VerifiedGarbage.Proof.Bignum.Arm.ClearArrayWide
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
public import VerifiedGarbage.Proof.Bignum.Arm.PrepareAcceptedPrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeAcceptance
import VerifiedGarbage.Proof.Bignum.Arm.PreparePrime
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeCT
import VerifiedGarbage.Proof.Bignum.Arm.R2CT
import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulus
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
public import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
import VerifiedGarbage.Proof.Bignum.Arm.CopyBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
meta import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
meta import VerifiedGarbage.Proof.Bignum.Arm.SubModArrayArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CopyBytesCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
meta import VerifiedGarbage.Proof.Bignum.Arm.StageCT
meta import VerifiedGarbage.Proof.Bignum.Arm.Stack
meta import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
public import VerifiedGarbage.Impl.Bignum.Arm.CrtAcceptance
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtAcceptance
meta import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
public import VerifiedGarbage.Impl.Bignum.Arm.ClearOperandBuffer
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.ZeroCT
import VerifiedGarbage.Proof.Bignum.Arm.ClearOperandBufferArgs
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Bignum.Arm.SubModBuffers
import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Bignum.Arm.SubModBuffers
meta import VerifiedGarbage.Proof.Framework.Mem

/-! ### `Bignum.Arm.SubModBuffersCT`, which only this module used -/

section

/-! # Modular subtraction reveals only pointers and length -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem subModBuffers_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r10 = t.gpr .r10 ∧ s.gpr .r12 = t.gpr .r12 ∧ s.gpr .r9 = t.gpr .r9 ∧ s.gpr .lr = t.gpr .lr) subModBuffers := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r10, .r12, .r9, .lr]) ?_ (by taint_decide)
  intro s t _ _ h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.ClearArrayWideCT`, which this module and modules that import it used -/

section

/-! # Clearing an extended result array leaks only its public layout -/

/-! ## Clearing an extended operand buffer reveals only its public pointer and width -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

structure ClearOperandBufferInput (base dst : BitVec 32) (size slot w : Nat) (s : State) : Prop where
  workspace : Workspace s base size
  ptr : s.gpr .r0 = base
  count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w
  link : s.mem.readW (off (State.addr base) slot) 32 = dst

theorem clearOperandBuffer_ct {base dst : BitVec 32} {size slot w : Nat}
    (fit : 52 ≤ size) (slotFit : slot + 4 ≤ size) (hs : slot < 4096) :
    RelCT isa (fun s t => ClearOperandBufferInput base dst size slot w s ∧ ClearOperandBufferInput base dst size slot w t ∧ s.sp = t.sp)
      (clearOperandBuffer slot) (fun _ _ => True) := by
  let P := ClearOperandBufferInput base dst size slot w
  let Q := fun s : State => s.gpr .r0 = dst ∧ s.gpr .lr = BitVec.ofNat 32 (2 * w + 2)
  have args : RelCT isa (fun s t => P s ∧ P t) (.block (clearOperandBufferArgs slot)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : P s) : WP isa (.block (clearOperandBufferArgs slot)) s Q :=
    WP.mono (clearOperandBufferArgs_ok s h.workspace fit slotFit hs h.ptr h.count h.link) (fun _ j => ⟨j.1, j.2.1⟩)
  have clear : RelCT isa (fun s t => Q s ∧ Q t) zero (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨zero_ct s t tr1 tr2 u v trivial trivial ⟨h.1.1.trans h.2.1.symm, h.1.2.trans h.2.2.symm⟩ e1 e2, trivial⟩
  have body := relCT_keep_sp (((pair_posts args wp).seq clear).mono
    (P' := fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ _ => trivial)) (fun _ _ h => h.2.2)
  exact ((body.seq (loadStack_ct .r0 0)).assoc).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

theorem clearArrayWide_ct {base : BitVec 32} {len w o : Nat} (ho : o < 8) (fit : 128 ≤ 8 * len) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (clearOperandBuffer (64 + 8 * o)) (fun _ _ => True) := by
  have input (s : State) (h : ArithmeticReady base len w s) :
      ClearOperandBufferInput base (base + BitVec.ofNat 32 (arrAt w o)) (8 * len) (64 + 8 * o) w s := by
    have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
    rw [h.width] at header
    exact ⟨h.workspace, h.ptr, header.count, header.array o ho⟩
  exact (clearOperandBuffer_ct (base := base) (dst := base + BitVec.ofNat 32 (arrAt w o))
    (size := 8 * len) (slot := 64 + 8 * o) (w := w) (by omega_using [fit]) (by omega_using [ho, fit]) (by omega_using [ho])).mono
    (fun s t h => ⟨input s h.1, input t h.2.1, h.2.2⟩) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.PrepareAcceptedPrimeCT`, which the modules that import this one used -/

section

/-! ### `Bignum.Arm.CrtAcceptanceCT`, which this module and modules that import it used -/

section

/-! # Installing a secret acceptance bit has public memory addresses -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_installAcceptance_ct : RelCT isa
    (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.sp = t.sp) (.block installAcceptance) (fun _ _ => True) := by
  have addr : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.sp = t.sp)
      (.block [.addSp .r12 48])
      (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r12 = t.gpr .r12) := by
    apply single_ct (fun _ _ _ => rfl)
    intro s t u v h e1 e2
    simp only [exec, Nat.reduceLT, ite_true, Option.some.injEq] at e1 e2
    subst u; subst v
    simp only [State.setReg, ite_true, h.1, h.2]
    exact ⟨trivial, trivial⟩
  have store : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r12 = t.gpr .r12)
      (.block [.ldr .r11 .r12 0, .str .r11 .r0 212]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r12]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2
  exact RelCT.block_append (M := isa) (l₁ := [.addSp .r12 48])
    (l₂ := [.ldr .r11 .r12 0, .str .r11 .r0 212]) (addr.seq store)

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.CrtNarrowCopyCT`, which the modules that import this one used -/

section

/-! # The copies between the narrow and a full-width workspace are constant-time

Their addresses are the workspaces' and their public widths', which the
pointers loaded from the headers pin down in both runs.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (wp_ldr Rest)

/-- Both runs' copy contexts, for any secrets. -/
def CrtCopyPair (g : CrtGeometry) (bs1 bs2 : Fin 7 → List Byte) (child : BitVec 32) (slot v : Nat)
    (s t : State) : Prop :=
  CrtCopyCtx g bs1 child slot v s ∧ CrtCopyCtx g bs2 child slot v t ∧ s.sp = t.sp

theorem CrtCopyCtx.of_regs {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v : Nat} {rs : List Reg} (h : CrtCopyCtx g bs child slot v s) (mem : t.mem = s.mem) (rest : Rest rs s t)
    (ptr : t.gpr .r0 = crtN g.base g.words) : CrtCopyCtx g bs child slot v t :=
  ⟨h.shared.of_mem mem rest, h.ready.of_mem mem rest ptr, h.childWs.congr rest.wr, h.member,
    by rw [mem]; exact h.layout, h.sep, h.slotFit, h.slotSmall, by rw [mem]; exact h.link, h.le⟩

theorem crt_fullSource_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {child : BitVec 32} {slot v j : Nat} :
    RelCT isa (CrtCopyPair g bs1 bs2 child slot v) (.block (fullSource slot j)) (fun _ _ => True) := by
  have load : RelCT isa (CrtCopyPair g bs1 bs2 child slot v) (.block [.ldrSp .r1 8]) (fun _ _ => True) :=
    (loadStack_ct .r1 8).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  let Main := fun (bs : Fin 7 → List Byte) (s : State) => CrtCopyCtx g bs child slot v s ∧ s.gpr .r1 = g.base
  have wp (s : State) {bs : Fin 7 → List Byte} (h : CrtCopyCtx g bs child slot v s) :
      WP isa (.block [.ldrSp .r1 8]) s (Main bs) := by
    refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide)
      (addr_add (by have := h.shared.stack.nowrap; omega_using [this])) (h.shared.stack.read (by decide)) fun t a => WP.block_nil ?_
    exact ⟨h.of_regs a.mem (a.rest (ws := [.r1]) (by simp)) ((a.other .r0 (by decide)).trans h.ready.ptr),
      a.gpr.trans h.shared.savedMain⟩
  have first := load.wp (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  have link : RelCT isa (fun s t => Main bs1 s ∧ Main bs2 t) (.block [.ldr .r1 .r1 slot]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r1]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r1])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.2.trans h.2.2.symm
  have linkWP (s : State) {bs : Fin 7 → List Byte} (h : Main bs s) :
      WP isa (.block [.ldr .r1 .r1 slot]) s (fun t => t.gpr .r1 = child) := by
    have main := h.1.shared.buffers.context.main
    have slotFit := h.1.slotFit
    refine wp_ldr (a := off (State.addr g.base) slot) h.1.slotSmall
      (by rw [h.2]; exact addr_add (by have := main.nowrap; omega_using [slotFit, this])) (main.read h.1.slotFit) fun t a => WP.block_nil ?_
    exact a.gpr.trans h.1.link
  have array : RelCT isa (fun s t => s.gpr .r1 = child ∧ t.gpr .r1 = child) (.block [.ldr .r1 .r1 (64 + 8 * j)])
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r1]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r1])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.trans h.2.symm
  have tail := RelCT.block_append (M := isa) (l₁ := [.ldr .r1 .r1 slot]) (l₂ := [.ldr .r1 .r1 (64 + 8 * j)])
    ((link.wp (fun s t h => ⟨linkWP s h.1, linkWP t h.2⟩)).seq
      (array.mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) (fun _ _ h => h)))
  exact RelCT.block_append (M := isa) (l₁ := [.ldrSp .r1 8]) (l₂ := [.ldr .r1 .r1 slot, .ldr .r1 .r1 (64 + 8 * j)])
    (first.seq (tail.mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) (fun _ _ _ => trivial)))

/-- The copy's three registers agree between the runs. -/
theorem crt_copy_ct {x y n : BitVec 32} :
    RelCT isa (fun s t => (s.gpr .r0 = x ∧ s.gpr .r1 = y ∧ s.gpr .lr = n) ∧ (t.gpr .r0 = x ∧ t.gpr .r1 = y ∧ t.gpr .lr = n))
      copyBytes (fun _ _ => True) := by
  intro s t tr1 tr2 u w h e1 e2
  exact ⟨copyBytes_ct s t tr1 tr2 u w trivial trivial
    ⟨h.1.1.trans h.2.1.symm, h.1.2.1.trans h.2.2.1.symm, h.1.2.2.trans h.2.2.2.symm⟩ e1 e2, trivial⟩

theorem crt_restoreBase_ct : RelCT isa (fun _ _ => True) (.block [.mov .r0 (.reg .r5)]) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
  intro s t _
  exact Taint.agree_ofRegs (by simp)

/-- After the source: the narrow workspace ready and the full array's address in r1. -/
def CrtSourced (g : CrtGeometry) (bs : Fin 7 → List Byte) (child : BitVec 32) (slot v j : Nat) (s : State) : Prop :=
  CrtCopyCtx g bs child slot v s ∧ s.gpr .r1 = child + BitVec.ofNat 32 (arrAt g.words j)

theorem crt_fullSource_sourced (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32}
    {slot v j : Nat} (h : CrtCopyCtx g bs child slot v s) (hj : j < 8) :
    WP isa (.block (fullSource slot j)) s (CrtSourced g bs child slot v j) := by
  refine WP.mono (crt_fullSource_ok s h.shared h.childWs h.layout h.slotFit h.slotSmall h.link hj) ?_
  rintro t ⟨src, mem, rest⟩
  exact ⟨h.of_regs mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr), src⟩

theorem crt_sourced_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {child : BitVec 32} {slot v j : Nat}
    (hj : j < 8) :
    RelCT isa (CrtCopyPair g bs1 bs2 child slot v) (.block (fullSource slot j))
      (fun s t => s.sp = t.sp ∧ CrtSourced g bs1 child slot v j s ∧ CrtSourced g bs2 child slot v j t) :=
  (relCT_keep_sp crt_fullSource_ct (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨crt_fullSource_sourced s h.1 hj, crt_fullSource_sourced t h.2.1 hj⟩)

theorem crt_copyLow_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {child : BitVec 32} {slot v j d : Nat}
    (hj : j < 8) (hd : d < 8) :
    RelCT isa (CrtCopyPair g bs1 bs2 child slot v) (copyLow slot j d) (fun _ _ => True) := by
  let Copying := fun s : State => s.gpr .r0 = crtN g.base g.words + BitVec.ofNat 32 (arrAt v d) ∧
    s.gpr .r1 = child + BitVec.ofNat 32 (arrAt g.words j) ∧ s.gpr .lr = BitVec.ofNat 32 (8 * v)
  have args : RelCT isa (fun s t => CrtSourced g bs1 child slot v j s ∧ CrtSourced g bs2 child slot v j t)
      (.block (lowArgs d)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.1.ready.ptr.trans h.2.1.ready.ptr.symm
  have argsWP (s : State) {bs : Fin 7 → List Byte} (h : CrtSourced g bs child slot v j s) :
      WP isa (.block (lowArgs d)) s Copying := by
    refine WP.mono (crt_lowArgs_ok s h.1.ready hd) ?_
    rintro t ⟨dst, _, count, src, _, _⟩
    exact ⟨dst, src.trans h.2, count⟩
  rw [copyLow]
  exact ((crt_sourced_ct hj).mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq
    ((args.wp (fun s t h => ⟨argsWP s h.1, argsWP t h.2⟩)).seq
      ((crt_copy_ct.mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) (fun _ _ h => h)).seq crt_restoreBase_ct))

theorem crt_copyOut_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {child : BitVec 32} {slot v j a : Nat}
    (hj : j < 8) (ha : a < 8) :
    RelCT isa (CrtCopyPair g bs1 bs2 child slot v) (copyOut slot j a) (fun _ _ => True) := by
  let Copying := fun s : State => s.gpr .r0 = child + BitVec.ofNat 32 (arrAt g.words j) ∧
    s.gpr .r1 = crtN g.base g.words + BitVec.ofNat 32 (arrAt v a) ∧ s.gpr .lr = BitVec.ofNat 32 (8 * v)
  have args : RelCT isa (fun s t => CrtSourced g bs1 child slot v j s ∧ CrtSourced g bs2 child slot v j t)
      (.block (outArgs a)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.1.ready.ptr.trans h.2.1.ready.ptr.symm
  have argsWP (s : State) {bs : Fin 7 → List Byte} (h : CrtSourced g bs child slot v j s) :
      WP isa (.block (outArgs a)) s Copying := by
    refine WP.mono (crt_outArgs_ok s h.1.ready ha) ?_
    rintro t ⟨dst, src, _, count, _, _⟩
    exact ⟨dst.trans h.2, src, count⟩
  rw [copyOut]
  exact ((crt_sourced_ct hj).mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq
    ((args.wp (fun s t h => ⟨argsWP s h.1, argsWP t h.2⟩)).seq
      ((crt_copy_ct.mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) (fun _ _ h => h)).seq crt_restoreBase_ct))

theorem crt_copyHigh_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {child : BitVec 32} {slot v j d : Nat}
    (hj : j < 8) (hd : d < 8) :
    RelCT isa (CrtCopyPair g bs1 bs2 child slot v) (copyHigh slot j d) (fun _ _ => True) := by
  let Main := fun (bs : Fin 7 → List Byte) (s : State) => CrtSourced g bs child slot v j s ∧ s.gpr .r2 = g.base
  have load : RelCT isa (fun s t => s.sp = t.sp ∧ CrtSourced g bs1 child slot v j s ∧ CrtSourced g bs2 child slot v j t)
      (.block [.ldrSp .r2 8]) (fun _ _ => True) :=
    (loadStack_ct .r2 8).mono (fun _ _ h => h.1) (fun _ _ _ => trivial)
  have loadWP (s : State) {bs : Fin 7 → List Byte} (h : CrtSourced g bs child slot v j s) :
      WP isa (.block [.ldrSp .r2 8]) s (Main bs) := by
    refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide)
      (addr_add (by have := h.1.shared.stack.nowrap; omega_using [this])) (h.1.shared.stack.read (by decide)) fun t a => WP.block_nil ?_
    exact ⟨⟨h.1.of_regs a.mem (a.rest (ws := [.r2]) (by simp)) ((a.other .r0 (by decide)).trans h.1.ready.ptr),
      (a.other .r1 (by decide)).trans h.2⟩, a.gpr.trans h.1.shared.savedMain⟩
  let Copying := fun s : State => (s.gpr .r0 = crtN g.base g.words + BitVec.ofNat 32 (arrAt v d) ∧
    s.gpr .r1 = child + BitVec.ofNat 32 (arrAt g.words j + 8 * v) ∧
    s.gpr .lr = BitVec.ofNat 32 (8 * (g.words - v))) ∧ s.z = decide (g.words = v)
  have args : RelCT isa (fun s t => Main bs1 s ∧ Main bs2 t) (.block (highArgs d)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r2]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0, .r2])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.1.ready.ptr.trans h.2.1.1.ready.ptr.symm
    · exact h.1.2.trans h.2.2.symm
  have argsWP (s : State) {bs : Fin 7 → List Byte} (h : Main bs s) : WP isa (.block (highArgs d)) s Copying := by
    have main := h.1.1.shared.buffers.context.main
    have size := h.1.1.shared.buffers.context.size
    have words : g.words ≤ 128 := (crt_width_valid h.1.1.shared.buffers.lengthValid).2.1
    refine WP.mono (crt_highArgs_ok s h.1.1.ready hd h.2 (addr_add (by have := main.nowrap; omega_using [size, this]))
      (main.read (by omega_using [size])) (h.1.1.shared.main.toCrtLayoutState.nativeCount main) h.1.1.le (by omega_using [words])) ?_
    rintro t ⟨dst, _, src, count, z, _, _⟩
    exact ⟨⟨dst, by rw [src, h.1.2, Offset.add_add], count⟩, z⟩
  have branch : RelCT isa (fun s t => Copying s ∧ Copying t) (.ite .eq (.block []) copyBytes) (fun _ _ => True) := by
    refine RelCT.ite (fun s t h => ?_) (RelCT.block_nil (fun _ _ _ => trivial))
      (crt_copy_ct.mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h))
    change some s.z = some t.z
    rw [h.1.2, h.2.2]
  rw [copyHigh]
  exact ((crt_sourced_ct hj).mono (fun _ _ h => h) (fun _ _ h => h)).seq
    ((load.wp (fun s t h => ⟨loadWP s h.2.1, loadWP t h.2.2⟩)).seq
      ((args.mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) (fun _ _ h => h)).wp (fun s t h => ⟨argsWP s h.2.1, argsWP t h.2.2⟩)
        |>.seq ((branch.mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) (fun _ _ h => h)).seq crt_restoreBase_ct)))

end VG.Proof.Bignum.Arm

end

end

/-! # Neither factor validation nor acceptance changes the preparation trace -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/PreparePrimeCT.lean`, which only this module imported.
section

/-! # Secret-factor preparation has only public workspace-dependent traces -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)

theorem sanitizeModulus_ready (s : State) {base : BitVec 32} {len w : Nat}
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

theorem preparePrime_ct {base : BitVec 32} {len w : Nat} (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t => PrimeInput base len w s ∧ PrimeInput base len w t ∧ s.sp = t.sp)
      preparePrime (fun _ _ => True) := by
  have sanitize := (sanitizeModulus_ct (base := base) (len := len) (w := w)).mono
    (P' := fun (s t : State) => PrimeInput base len w s ∧ PrimeInput base len w t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.toLayoutFrameReady, h.2.1.toLayoutFrameReady, h.2.2⟩) (fun _ _ _ => trivial)
  have first := (relCT_keep_sp sanitize (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨sanitizeModulus_ready s h.1, sanitizeModulus_ready t h.2.1⟩)
  have inverse := relCT_keep_sp ((precomputeInverse_ct (base := base) (len := len) (w := w)).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ PrecomputeModulus base len w s ∧ PrecomputeModulus base len w t)
    (fun _ _ h => h.2) (fun _ _ h => h)) (fun _ _ h => h.1)
  have ready := inverse.wp (fun s t h => ⟨precomputeInverse_ready s h.2.1, precomputeInverse_ready t h.2.2⟩)
  exact first.seq ((ready.mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)).seq (r2_ct countFits))

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

theorem prepareAcceptedPrime_ct {base : BitVec 32} {len w : Nat} (countFits : 128 * w < 2 ^ 32) :
    RelCT isa (fun s t => AcceptedPrimeInput base len w s ∧ AcceptedPrimeInput base len w t ∧ s.sp = t.sp)
      prepareAcceptedPrime (fun _ _ => True) := by
  let P := AcceptedPrimeInput base len w
  have install : RelCT isa (fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
      (.block installAcceptance) (fun _ _ => True) :=
    crt_installAcceptance_ct.mono (fun _ _ h => ⟨h.1.ptr.trans h.2.1.ptr.symm, h.2.2⟩) (fun _ _ _ => trivial)
  have ready := (relCT_keep_sp install (fun _ _ h => h.2.2)).wp (fun s t h =>
    ⟨(crt_primeAcceptance_ready s h.1.toLayoutFrameReady h.1.stackFit h.1.flagRead h.1.bit h.1.valid).mono
      (fun _ j => j.1),
      (crt_primeAcceptance_ready t h.2.1.toLayoutFrameReady h.2.1.stackFit h.2.1.flagRead h.2.1.bit h.2.1.valid).mono
      (fun _ j => j.1)⟩)
  exact ready.seq ((preparePrime_ct countFits).mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm

end

end

/-! # Complete array subtraction has no secret-dependent addresses or branches -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

theorem subModArray_ct {base : BitVec 32} {len w o a b : Nat}
    (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho0 : o ≠ 0) (fit : 128 ≤ 8 * len) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (subModArray o a b) (fun _ _ => True) := by
  let P := ArithmeticReady base len w
  let Q := fun s : State => s.gpr .r0 = base + BitVec.ofNat 32 (arrAt w o) ∧
    s.gpr .r10 = base + BitVec.ofNat 32 (arrAt w a) ∧ s.gpr .r12 = base + BitVec.ofNat 32 (arrAt w b) ∧
    s.gpr .r9 = base + BitVec.ofNat 32 (arrAt w 0) ∧ s.gpr .lr = BitVec.ofNat 32 (2 * w)
  have clear := (relCT_keep_sp (clearArrayWide_ct (base := base) (w := w) ho fit) (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨(clearArrayWide_ok s h.1 ho ho0).mono (fun _ j => j.1),
      (clearArrayWide_ok t h.2.1 ho ho0).mono (fun _ j => j.1)⟩)
  have args : RelCT isa (fun (s t : State) => s.sp = t.sp ∧ P s ∧ P t)
      (subModArrayArgs o a b) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _
      (hc := .seq (Taint.ofRegs [.r0]) (.block []) (.block [])) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1.ptr.trans h.2.2.ptr.symm
  have argsWP (s : State) (h : P s) : WP isa (subModArrayArgs o a b) s Q := by
    have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
    rw [h.width] at header
    exact (subModArrayArgs_ok s ho ha hb h.workspace fit header h.ptr).mono
      (fun _ j => ⟨j.1, j.2.1, j.2.2.1, j.2.2.2.1, j.2.2.2.2.1⟩)
  have prepared := (relCT_keep_sp args (fun _ _ h => h.1)).wp
    (fun s t h => ⟨argsWP s h.2.1, argsWP t h.2.2⟩)
  have subtract : RelCT isa (fun (s t : State) => s.sp = t.sp ∧ Q s ∧ Q t)
      subModBuffers (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨subModBuffers_ct s t tr1 tr2 u v trivial trivial
      ⟨h.2.1.1.trans h.2.2.1.symm, h.2.1.2.1.trans h.2.2.2.1.symm,
        h.2.1.2.2.1.trans h.2.2.2.2.1.symm, h.2.1.2.2.2.1.trans h.2.2.2.2.2.1.symm,
        h.2.1.2.2.2.2.trans h.2.2.2.2.2.2.symm⟩ e1 e2, trivial⟩
  have final := (relCT_keep_sp subtract (fun _ _ h => h.1)).seq (loadStack_ct .r0 0)
  exact clear.seq (prepared.seq (final.mono (fun _ _ h => h) (fun _ _ _ => trivial)))

end VG.Proof.Bignum.Arm
