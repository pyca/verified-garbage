module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepareState
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayoutCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtInitialize
import VerifiedGarbage.Proof.Bignum.Arm.PcHead
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepareState
meta import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayoutCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtInitialize
meta import VerifiedGarbage.Proof.Bignum.Arm.PcHead
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Bignum.Arm.CrtWorkspaceCall
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspaceCT
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtWorkspaceCall
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspaceCT
meta import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StageCT
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceState
import VerifiedGarbage.Proof.Bignum.Arm.SetupFrame
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Arm.CrtStrides
meta import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.Arm.Workspace
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtStrides
meta import VerifiedGarbage.Proof.Rsa.MontContract
meta import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceState
meta import VerifiedGarbage.Proof.Bignum.Arm.SetupFrame
meta import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupContext
import VerifiedGarbage.Proof.Bignum.Arm.CrtLeavePrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupPrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupMain
import VerifiedGarbage.Impl.Bignum.Arm.Zero
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupContext
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtLeavePrime
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupPrime
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupMain
meta import VerifiedGarbage.Impl.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Bignum.Arm.CrtEnterPrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtEnterPrime

/-! ### `Bignum.Arm.CrtSetupAllCT`, which only this module used -/

section

/-! ### `Bignum.Arm.CrtSetupPrimeCT`, which only this module used -/

section

/-! ### `Bignum.Arm.CrtEnterPrimeCT`, which only this module used -/

section

/-! # Moving between CRT workspaces depends only on their public pointers -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont

structure CrtEnterInput (base child : BitVec 32) (size slot w : Nat) (s : State) : Prop where
  workspace : Workspace s base size
  ptr : s.gpr .r0 = base
  count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w
  link : s.mem.readW (off (State.addr base) slot) 32 = child

theorem crt_enterPrime_ct {base child : BitVec 32} {size slot w : Nat}
    (fit : 52 ≤ size) (slotFit : slot + 4 ≤ size) (hs : slot < 4096) :
    RelCT isa (fun s t => CrtEnterInput base child size slot w s ∧ CrtEnterInput base child size slot w t)
      (enterPrime slot) (fun _ _ => True) := by
  let P := CrtEnterInput base child size slot w
  have head : RelCT isa (fun s t => P s ∧ P t) (.block (primeArgs slot)) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : P s) : WP isa (.block (primeArgs slot)) s (fun t => t.gpr .r2 = child) :=
    WP.mono (crt_primeArgs_ok s h.workspace fit slotFit hs h.ptr h.count h.link) (fun _ j => j.2.1)
  refine (pair_posts head wp).seq ?_
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r2]) _ (by taint_decide)
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h.1.trans h.2.symm

end VG.Proof.Bignum.Arm

end

end

/-! # Factor workspace initialization has no secret-dependent accesses -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

structure CrtSetupPrimeInput (base child : BitVec 32) (len slot w : Nat) (s : State) : Prop
    extends CrtEnterInput base child (8 * len) slot w s where
  childWorkspace : Workspace s child (8 * len)

theorem crt_setupPrime_ct {base child : BitVec 32} {len slot w : Nat}
    (fit : 220 ≤ 8 * len) (slotFit : slot + 4 ≤ 8 * len) (hs : slot < 4096) :
    RelCT isa (fun s t => CrtSetupPrimeInput base child len slot w s ∧ CrtSetupPrimeInput base child len slot w t)
      (setupPrime slot) (fun _ _ => True) := by
  let P := CrtSetupPrimeInput base child len slot w
  have enter := (crt_enterPrime_ct (base := base) (child := child) (size := 8 * len) (w := w)
    (by omega_using [fit]) slotFit hs).mono (P' := fun s t => P s ∧ P t)
    (fun _ _ h => ⟨h.1.toCrtEnterInput, h.2.toCrtEnterInput⟩) (fun _ _ _ => trivial)
  have wp (s : State) (h : P s) : WP isa (enterPrime slot) s (fun t => t.gpr .r0 = child) :=
    WP.mono (crt_enterPrime_ok s h.workspace h.childWorkspace (by omega_using [fit]) slotFit hs fit h.ptr h.count h.link)
      (fun _ j => j.1)
  refine (pair_posts enter wp).seq ?_
  intro s t tr1 tr2 u v h e1 e2
  exact ⟨setup_ct s t tr1 tr2 u v trivial trivial (h.1.trans h.2.symm) e1 e2, trivial⟩

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.CrtSetupStages`, which only this module used -/

section

/-! # Per-execution invariants for the complete setup timing proof -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.Rsa.Mont (arrAt)

structure CrtSetupInput (base : BitVec 32) (len w : Nat) (s : State) : Prop where
  context : CrtSetupContext base len w s
  ptr : s.gpr .r0 = base
  count : s.gpr .r7 = BitVec.ofNat 32 w
  zero : s.gpr .r3 = 0

structure CrtAtMain (base : BitVec 32) (len w : Nat) (s : State) : Prop where
  context : CrtSetupContext base len w s
  main : CrtMainState base len w s.mem
  ptr : s.gpr .r0 = base

structure CrtAtPrime (base child : BitVec 32) (len w : Nat) (s : State) : Prop where
  context : CrtSetupContext base len w s
  main : CrtMainState base len w s.mem
  childWorkspace : Workspace s child (8 * len)
  ptr : s.gpr .r0 = child
  link : s.mem.readW (VG.Proof.Mont.off (State.addr child) 216) 32 = base

theorem crt_setupMain_ready (s : State) {base : BitVec 32} {len w : Nat} (h : CrtSetupInput base len w s) :
    WP isa setupMain s (CrtAtMain base len w) := by
  refine WP.mono (crt_setupMain_ok s h.context.main h.context.width h.context.widthFit h.context.arraysFit h.ptr h.count h.zero) ?_
  rintro t ⟨main, ptr, _, rest⟩
  exact ⟨h.context.congr rest.wr, main, ptr⟩

theorem crt_setupPrime_ready (s : State) {base child : BitVec 32} {len slot w : Nat}
    (h : CrtAtMain base len w s) (ws : Workspace s child (8 * len))
    (slotFit : slot + 4 ≤ 8 * len) (hs : slot < 4096)
    (sep : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr child, 8 * len⟩)
    (link : s.mem.readW (VG.Proof.Mont.off (State.addr base) slot) 32 = child) :
    WP isa (setupPrime slot) s (CrtAtPrime base child len w) := by
  have size := h.context.size
  refine WP.mono (crt_setupPrime_ok s h.context.main ws (by omega_using [size]) slotFit hs
    h.context.width h.context.widthFit h.context.arraysFit h.ptr
    (h.main.toCrtLayoutState.nativeCount h.context.main) link) ?_
  rintro t ⟨_, _, ptr, linkT, frame, rest⟩
  exact ⟨h.context.congr rest.wr, h.main.congr (h.context.main.eq_of_frame sep frame), ws.congr rest.wr, ptr, linkT⟩

theorem crt_leavePrime_ready (s : State) {base child : BitVec 32} {len w : Nat}
    (h : CrtAtPrime base child len w s) : WP isa (.block leavePrime) s (CrtAtMain base len w) := by
  have size := h.context.size
  refine WP.mono (crt_leavePrime_ok s h.childWorkspace (by omega_using [size]) h.ptr h.link) ?_
  rintro t ⟨ptr, mem, rest⟩
  exact ⟨h.context.congr rest.wr, mem ▸ h.main, ptr⟩

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.CrtSetupMainCT`, which only this module used -/

section

/-! ### `Bignum.Arm.CrtLinksCT`, which only this module used -/

section

/-! # CRT link setup uses only public buffer geometry -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont

structure CrtLinksInput (base : BitVec 32) (size w : Nat) (s : State) : Prop where
  workspace : Workspace s base size
  ptr : s.gpr .r0 = base
  count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w

theorem crt_links_ct {base : BitVec 32} {size w : Nat} (fit : 52 ≤ size) :
    RelCT isa (fun s t => CrtLinksInput base size w s ∧ CrtLinksInput base size w t) links (fun _ _ => True) := by
  let P := CrtLinksInput base size w
  let Q := fun s : State => s.gpr .r0 = base ∧ s.gpr .r7 = BitVec.ofNat 32 w ∧
    s.gpr .r1 = BitVec.ofNat 32 (stride w) ∧ s.gpr .r2 = base
  have head : RelCT isa (fun s t => P s ∧ P t) (.block linkStride) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have wp (s : State) (h : P s) : WP isa (.block linkStride) s Q := by
    refine WP.mono (crt_linkStride_ok s h.workspace fit h.ptr h.count) ?_
    rintro t ⟨width, step, current, _, rest⟩
    exact ⟨(rest.gpr .r0 (by simp)).trans h.ptr, width, step, current⟩
  have tail : RelCT isa (fun s t => Q s ∧ Q t) linksTail (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r7, .r1, .r2]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.1.1.trans h.2.1.symm
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.trans h.2.2.2.2.symm
  exact (pair_posts head wp).seq tail

end VG.Proof.Bignum.Arm

end

end

/-! # Public geometry determines the main CRT initialization trace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.Rsa.Mont (arrAt)

structure CrtMainInput (base : BitVec 32) (len w : Nat) (s : State) : Prop where
  workspace : Workspace s base (8 * len)
  ptr : s.gpr .r0 = base
  count : s.gpr .r7 = BitVec.ofNat 32 w
  zero : s.gpr .r3 = 0

theorem crt_setupMain_ct {base : BitVec 32} {len w : Nat} (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (fits : arrAt w 8 ≤ 8 * len) :
    RelCT isa (fun s t => CrtMainInput base len w s ∧ CrtMainInput base len w t) setupMain (fun _ _ => True) := by
  let P := CrtMainInput base len w
  have first : RelCT isa (fun s t => P s ∧ P t) setup (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨setup_ct s t tr1 tr2 u v trivial trivial (h.1.ptr.trans h.2.ptr.symm) e1 e2, trivial⟩
  have wp (s : State) (h : P s) : WP isa setup s (CrtLinksInput base (8 * len) w) := by
    refine WP.mono (setup_frame_ok s h.workspace hw hw' fits h.ptr h.count h.zero) ?_
    rintro t ⟨layout, width, ptr, _, rest⟩
    have shape : CrtLayoutState base len w t.mem := ⟨layout, width⟩
    exact ⟨h.workspace.congr rest.wr, ptr, shape.nativeCount (h.workspace.congr rest.wr)⟩
  have size : 52 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  exact (pair_posts first wp).seq (crt_links_ct size)

end VG.Proof.Bignum.Arm

end

end

/-! # Complete three-workspace CRT setup is constant time -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.Rsa.Mont (arrAt)

theorem crt_setupP_ct {base : BitVec 32} {len w : Nat} (fit : 256 ≤ 8 * len) :
    RelCT isa (fun s t => CrtAtMain base len w s ∧ CrtAtMain base len w t) (setupPrime 224)
      (fun s t => CrtAtPrime base (crtP base w) len w s ∧ CrtAtPrime base (crtP base w) len w t) := by
  let P := CrtAtMain base len w
  have input (s : State) (h : P s) : CrtSetupPrimeInput base (crtP base w) len 224 w s :=
    ⟨⟨h.context.main, h.ptr, h.main.toCrtLayoutState.nativeCount h.context.main, h.main.p⟩, h.context.p⟩
  have ct := (crt_setupPrime_ct (base := base) (child := crtP base w) (len := len) (slot := 224) (w := w)
    (by omega_using [fit]) (by omega_using [fit]) (by decide)).mono (P' := fun s t => P s ∧ P t)
    (fun s t h => ⟨input s h.1, input t h.2⟩) (fun _ _ _ => trivial)
  exact pair_posts ct (fun s h => crt_setupPrime_ready s h h.context.p (by omega_using [fit]) (by decide) h.context.sepMP h.main.p)

theorem crt_setupQ_ct {base : BitVec 32} {len w : Nat} (fit : 256 ≤ 8 * len) :
    RelCT isa (fun s t => CrtAtMain base len w s ∧ CrtAtMain base len w t) (setupPrime 228)
      (fun s t => CrtAtPrime base (crtQ base w) len w s ∧ CrtAtPrime base (crtQ base w) len w t) := by
  let P := CrtAtMain base len w
  have input (s : State) (h : P s) : CrtSetupPrimeInput base (crtQ base w) len 228 w s :=
    ⟨⟨h.context.main, h.ptr, h.main.toCrtLayoutState.nativeCount h.context.main, h.main.q⟩, h.context.q⟩
  have ct := (crt_setupPrime_ct (base := base) (child := crtQ base w) (len := len) (slot := 228) (w := w)
    (by omega_using [fit]) (by omega_using [fit]) (by decide)).mono (P' := fun s t => P s ∧ P t)
    (fun s t h => ⟨input s h.1, input t h.2⟩) (fun _ _ _ => trivial)
  exact pair_posts ct (fun s h => crt_setupPrime_ready s h h.context.q (by omega_using [fit]) (by decide) h.context.sepMQ h.main.q)

theorem crt_leavePrime_ct {base child : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => CrtAtPrime base child len w s ∧ CrtAtPrime base child len w t) (.block leavePrime)
      (fun s t => CrtAtMain base len w s ∧ CrtAtMain base len w t) := by
  have ct : RelCT isa (fun s t => CrtAtPrime base child len w s ∧ CrtAtPrime base child len w t)
      (.block leavePrime) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  exact pair_posts ct (fun s h => crt_leavePrime_ready s h)

theorem crt_setupAll_ct {base : BitVec 32} {len w : Nat} (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (fits : arrAt w 8 ≤ 8 * len) :
    RelCT isa (fun s t => CrtSetupInput base len w s ∧ CrtSetupInput base len w t) setupAll (fun _ _ => True) := by
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  have first := (crt_setupMain_ct (base := base) hw hw' fits).mono
    (P' := fun s t => CrtSetupInput base len w s ∧ CrtSetupInput base len w t)
    (fun _ _ h => ⟨⟨h.1.context.main, h.1.ptr, h.1.count, h.1.zero⟩,
      ⟨h.2.context.main, h.2.ptr, h.2.count, h.2.zero⟩⟩) (fun _ _ _ => trivial)
  exact ((pair_posts first (fun s h => crt_setupMain_ready s h)).seq ((crt_setupP_ct size).seq
    (crt_leavePrime_ct.seq ((crt_setupQ_ct size).seq crt_leavePrime_ct)))).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm

end

end

/-! ### `Bignum.Arm.CrtWorkspaceCallCT`, which this module and modules that import it used -/

section

/-! # Switching the active workspace leaks only the public stack address -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_saveMain_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block saveMain) (fun _ _ => True) := by
  have addr : RelCT isa (fun s t => s.sp = t.sp) (.block [.addSp .r12 8])
      (fun s t => s.gpr .r12 = t.gpr .r12) := by
    apply single_ct (fun _ _ _ => rfl)
    intro s t u v h e1 e2
    simp only [exec, Nat.reduceLT, ite_true, Option.some.injEq] at e1 e2
    subst u; subst v
    simp only [State.setReg, ite_true, h]
  have store : RelCT isa (fun s t => s.gpr .r12 = t.gpr .r12)
      (.block [.str .r0 .r12 0]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r12]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h
  exact RelCT.block_append (M := isa) (l₁ := [.addSp .r12 8]) (l₂ := [.str .r0 .r12 0]) (addr.seq store)

theorem crt_selectChild_ct (slot : Nat) :
    RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.sp = t.sp)
      (selectChild slot) (fun _ _ => True) := by
  have load : RelCT isa (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.sp = t.sp)
      (.block [.ldr .r0 .r0 slot]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (hc := .block []) (by
      rw [← Taint.check_eraseOff _ _ (Taint.noBase_ofRegs [.r0])]
      rfl)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1
  exact (relCT_keep_sp load (fun _ _ h => h.2)).seq activateWorkspace_ct

theorem crt_selectMain_ct : RelCT isa (fun s t => s.sp = t.sp) selectMain (fun _ _ => True) :=
  (loadStack_ct .r0 8).seq activateWorkspace_ct

end VG.Proof.Bignum.Arm

end

end

/-! # CRT workspace preparation reveals only public geometry -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_initialize_ct {base np : BitVec 32} {size w k : Nat} {nb1 nb2 : List Byte} :
    RelCT isa (fun s t => CrtPrepareInput base np size w k nb1 s ∧ CrtPrepareInput base np size w k nb2 t)
      (.seq (.block PcFn.head) setupAll) (fun _ _ => True) := by
  let P := fun s t => CrtPrepareInput base np size w k nb1 s ∧ CrtPrepareInput base np size w k nb2 t
  have head : RelCT isa P (.block PcFn.head) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro _ _ _
    exact Taint.agree_ofRegs (by simp)
  have wp (s : State) {nb : List Byte} (h : CrtPrepareInput base np size w k nb s) :
      WP isa (.block PcFn.head) s (CrtSetupInput base (workspaceWords w) w) := by
    refine WP.mono (pcHead_ok s h.lengthValid.2 h.count) ?_
    rintro t ⟨count, zero, _, rest⟩
    rw [h.width] at count
    exact ⟨h.context.congr rest.wr, (rest.gpr .r0 (by simp)).trans h.ptr, count, zero⟩
  have args := head.wp (fun s t h => ⟨wp s h.1, wp t h.2⟩)
  have setup : RelCT isa (fun s t => True ∧ CrtSetupInput base (workspaceWords w) w s ∧
      CrtSetupInput base (workspaceWords w) w t) setupAll (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact crt_setupAll_ct h.2.1.context.width h.2.1.context.widthFit h.2.1.context.arraysFit
      s t tr1 tr2 u v ⟨h.2.1, h.2.2⟩ e1 e2
  exact args.seq setup

theorem crt_prepare_ct {base np : BitVec 32} {size w k : Nat} {nb1 nb2 : List Byte} :
    RelCT isa (fun s t => CrtPrepareInput base np size w k nb1 s ∧
      CrtPrepareInput base np size w k nb2 t ∧ s.sp = t.sp) CrtFn.prepare (fun _ _ => True) := by
  let P := fun s t => CrtPrepareInput base np size w k nb1 s ∧
    CrtPrepareInput base np size w k nb2 t ∧ s.sp = t.sp
  have initCT : RelCT isa P (.seq (.block PcFn.head) setupAll) (fun _ _ => True) :=
    crt_initialize_ct.mono (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ _ => trivial)
  have first := (relCT_keep_sp initCT (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨WP.mono (crt_initialize_ok s h.1) (fun _ j => j.1),
      WP.mono (crt_initialize_ok t h.2.1) (fun _ j => j.1)⟩)
  have load : RelCT isa (fun s t => s.sp = t.sp ∧ CrtInitialized base np size w k nb1 s ∧
      CrtInitialized base np size w k nb2 t) (savedOperand 0 8 12) (fun _ _ => True) :=
    (savedOperandLayout_ct (by decide : 0 < 8)).mono
      (fun _ _ h => ⟨⟨h.2.1.ready, h.2.1.source⟩, ⟨h.2.2.ready, h.2.2.source⟩, h.1⟩) (fun _ _ _ => trivial)
  exact (first.seq ((relCT_keep_sp load (fun _ _ h => h.1)).seq crt_saveMain_ct)).assoc

end VG.Proof.Bignum.Arm
