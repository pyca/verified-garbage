module

public import VerifiedGarbage.Proof.Bignum.Arm.PrivPreModulus
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepareState
public import VerifiedGarbage.Proof.Bignum.Arm.PrivPreBlocksCT
public import VerifiedGarbage.Proof.Bignum.Arm.PrivPrePhase
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.PrepareAcceptedPrime
import VerifiedGarbage.Proof.Bignum.Arm.PrepareAcceptedPrimeCT
import VerifiedGarbage.Proof.Bignum.Arm.PrepareModulus
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOut
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutCT
import VerifiedGarbage.Proof.Bignum.Arm.MaskOutputCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceCallCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepareCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptedFactors
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandState
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtHeaderCopiesCT
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPrime
import VerifiedGarbage.Proof.Bignum.Arm.PrimeR2FromCT
import VerifiedGarbage.Proof.Bignum.Arm.TransferArray
import VerifiedGarbage.Proof.Bignum.Arm.TransferArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Bignum.Arm.PrimeR2From
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPowerCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtSavedSources
import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT

/-! # The modulus' values and the mask are computed in constant time -/

@[expose] public section


namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Impl.Bignum.Arm.PrivPreFn VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

/-- A factor's phase: the shared state, and the acceptance bit, which accepts
only a valid factor. -/
def PpFactorIn (g : CrtGeometry) (bs : Fin 7 → List Byte) (j : Fin 6) (s : State) : Prop :=
  CrtShared g bs s ∧ ppFlag s ≤ 1 ∧
    (ppFlag s ≠ 0 → 1 < Spec.Rsa.os2ip (bs j.succ) ∧ Spec.Rsa.os2ip (bs j.succ) % 2 = 1)

theorem pp_phase_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (j : Fin 6) (prime : j = 1 ∨ j = 2)
    {dest : List Instr} {d : BitVec 32}
    (destOk : ∀ (bs : Fin 7 → List Byte) (u : State), CrtShared g bs u → WP isa (.block dest) u fun t =>
      t.gpr .r4 = d ∧ t.gpr .r2 = BitVec.ofNat 32 4 ∧ t.mem = u.mem ∧ Rest [.r1, .r2, .r3, .r4, .r7] u t)
    (destCt : ∀ {P1 P2 : State → Prop}, (∀ s, P1 s → MainSaved g s ∧ InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 4) 4) →
      (∀ s, P2 s → MainSaved g s ∧ InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 4) 4) →
      RelCT isa (fun s t => P1 s ∧ P2 t ∧ s.sp = t.sp) (.block dest) (fun _ _ => True)) :
    RelCT isa (fun s t => PpFactorIn g bs1 j s ∧ PpFactorIn g bs2 j t ∧ s.sp = t.sp)
      (phase (56 + 8 * j.val) dest) (fun _ _ => True) := by
  let v := ppWords (g.sourceLength j.succ)
  let N := crtN g.base g.words
  -- The narrow workspace entered.
  let Entered := fun (bs : Fin 7 → List Byte) (s : State) =>
    CrtShared g bs s ∧ NarrowPrimeInput N (g.source j.succ) (workspaceWords g.words) v
      (g.sourceLength j.succ) (56 + 8 * j.val) (bs j.succ) s
  have enterWP (s : State) {bs : Fin 7 → List Byte} (h : PpFactorIn g bs j s) :
      WP isa (enterFactor (56 + 8 * j.val + 4)) s (Entered bs) := by
    obtain ⟨_, _, kfit, kpos, _, _⟩ := h.1.pp_fits j prime
    have hj := j.isLt
    refine WP.mono (pp_enterFactor_ok s h.1 j prime) ?_
    rintro z ⟨sharedZ, selectedZ, flagZ, _, _⟩
    have flag : ppFlag z = ppFlag s := by unfold ppFlag; rw [flagZ]
    refine ⟨sharedZ, selectedZ, ?_, kpos, kfit, by have := sharedZ.stack.nowrap; omega, sharedZ.stack.read (by decide),
      by rw [← ppFlag, flag]; exact h.2.1, by rw [← ppFlag, flag]; exact h.2.2⟩
    simpa only [show 56 + 8 * j.val + 4 = 60 + 8 * j.val by omega] using sharedZ.savedOperand j sharedZ.narrow_member
  have enterCT : RelCT isa (fun s t => PpFactorIn g bs1 j s ∧ PpFactorIn g bs2 j t ∧ s.sp = t.sp)
      (enterFactor (56 + 8 * j.val + 4)) (fun _ _ => True) :=
    (pp_enterFactor_ct j prime).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  -- The factor prepared.
  let Prepared := fun (bs : Fin 7 → List Byte) (s : State) =>
    CrtShared g bs s ∧ ArithmeticReady N (workspaceWords g.words) v s
  have le {bs : Fin 7 → List Byte} {s : State} (h : CrtShared g bs s) : v ≤ g.words := by
    obtain ⟨_, le, _⟩ := h.pp_fits j prime
    exact le
  have prepWP (s : State) {bs : Fin 7 → List Byte} (h : Entered bs s) :
      WP isa (narrowPrimeFrom (56 + 8 * j.val)) s (Prepared bs) := by
    refine WP.mono (crt_narrowPrimeFrom_ok s h.1 h.2 (le h.1)) ?_
    rintro y ⟨readyY, _, _, _, _, frameY, restY⟩
    exact ⟨h.1.after_narrow (frameY.mono (by simp)) restY, readyY⟩
  have prepCT : RelCT isa (fun s t => Entered bs1 s ∧ Entered bs2 t ∧ s.sp = t.sp)
      (narrowPrimeFrom (56 + 8 * j.val)) (fun _ _ => True) := by
    intro s t tr1 tr2 u w h e1 e2
    exact crt_narrowPrimeFrom_ct (le h.1.1) s t tr1 tr2 u w h e1 e2
  -- The destination.
  let Ready := fun (s : State) => SmallFnReady N (workspaceWords g.words) v 4 s ∧ s.gpr .r4 = d
  have destWP (s : State) {bs : Fin 7 → List Byte} (h : Prepared bs s) : WP isa (.block dest) s Ready := by
    refine WP.mono (destOk bs s h.1) ?_
    rintro t ⟨r4, r2, mem, rest⟩
    exact ⟨⟨h.2.workspace.congr rest.wr, by rw [mem]; exact h.2.layout, by rw [mem]; exact h.2.width,
      (rest.gpr .r0 (by decide)).trans h.2.ptr, r2⟩, r4⟩
  have destRel : RelCT isa (fun s t => Prepared bs1 s ∧ Prepared bs2 t ∧ s.sp = t.sp) (.block dest) (fun _ _ => True) :=
    destCt (fun s h => ⟨h.1.mainSaved, h.1.stack.read (by decide)⟩) (fun s h => ⟨h.1.mainSaved, h.1.stack.read (by decide)⟩)
  have exportCT : RelCT isa (fun s t => Ready s ∧ Ready t ∧ s.sp = t.sp) exportArray (fun _ _ => True) :=
    (exportArray_ct (dst := d) (by decide : 4 < 8)).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.1.2, h.2.1.2⟩)
      (fun _ _ _ => trivial)
  rw [phase]
  exact crt_seq_ct enterCT (fun s h => enterWP s h) (fun s h => enterWP s h)
    (crt_seq_ct prepCT (fun s h => prepWP s h) (fun s h => prepWP s h)
      (crt_seq_ct destRel (fun s h => destWP s h) (fun s h => destWP s h) exportCT))

end VG.Proof.Bignum.Arm


namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Impl.Bignum.Arm.PrivPreFn VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Layout wOf)
open VG.Proof.X25519.Arm (Rest)

/-- What the steps after the main workspace's selection keep: the frame, the
main workspace in its slot, and `pre`. -/
def PpKept (g : CrtGeometry) (s : State) : Prop :=
  CrtCallStack g s ∧ s.mem.readW (off (State.addr s.sp) 8) 32 = g.base ∧ PpPre g s ∧ Spec.Rsa.lenValid g.length ∧
    Region.Disjoint ⟨State.addr g.base, 8 * workspaceWords g.words⟩ ⟨State.addr g.output, 8 * ppPreWords g⟩ ∧
    (0 < g.pLength ∧ g.pLength < g.length ∧ 0 < g.qLength ∧ g.qLength < g.length)

theorem PpKept.after {g : CrtGeometry} {s t : State} {rs : List Reg} {regions : List Region}
    (h : PpKept g s) (frame : Frame regions s.mem t.mem) (rest : Rest rs s t)
    (stack : ∀ r ∈ regions, (⟨State.addr s.sp, 112⟩ : Region).Disjoint r) : PpKept g t := by
  refine ⟨h.1.after_outside frame rest stack, ?_, h.2.2.1.after rest, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  rw [rest.sp]
  exact (frame.readW (r := ⟨off (State.addr s.sp) 8, 4⟩) (Region.contains_self _ _)
    (fun r hr => (stack r hr).sub_left (Offset.sub_base _ (by decide))) (by decide)).trans h.2.1

theorem pp_selectP_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => CrtShared g bs1 s ∧ CrtShared g bs2 t ∧ s.sp = t.sp) selectP (fun _ _ => True) := by
  have mainWP (s : State) {bs : Fin 7 → List Byte} (h : CrtShared g bs s) :
      WP isa selectMain s (CrtSelected g bs g.base) :=
    (crt_selectMain_ready s h).mono fun _ j => ⟨j.1, j.2.1⟩
  rw [selectP]
  exact crt_seq_ct (crt_selectMain_ct.mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial))
    (fun s h => mainWP s h) (fun s h => mainWP s h)
    ((crt_selectChild_ct 224).mono (fun _ _ h => ⟨h.1.2.ptr.trans h.2.1.2.ptr.symm, h.2.2⟩) (fun _ _ _ => trivial))

theorem pp_modulusR2_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte}
    (hn : Spec.Rsa.os2ip (bs1 0) = Spec.Rsa.os2ip (bs2 0)) :
    RelCT isa (fun s t => CrtShared g bs1 s ∧ CrtShared g bs2 t ∧ s.sp = t.sp) modulusR2 (fun _ _ => True) := by
  let L := workspaceWords g.words
  let P := crtP g.base g.words
  -- p's workspace selected.
  have selectWP (s : State) {bs : Fin 7 → List Byte} (h : CrtShared g bs s) :
      WP isa selectP s (CrtSelected g bs P) :=
    (pp_selectP_ok s h).mono fun _ j => ⟨j.1, j.2.1⟩
  -- The main workspace's pointer in r1.
  let T := fun (bs : Fin 7 → List Byte) (s : State) =>
    TransferArrayInput P g.base L L g.words s ∧ numAt s.mem (State.addr g.base) g.words 0 = Spec.Rsa.os2ip (bs 0) ∧
      Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs 0)) g.length = true ∧ Spec.Rsa.lenValid g.length
  have loadWP (s : State) {bs : Fin 7 → List Byte} (h : CrtSelected g bs P s) :
      WP isa (.block [.ldrSp .r1 8]) s (T bs) := by
    refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide)
      (addr_add (by have := h.1.stack.nowrap; omega)) (h.1.stack.read (by decide)) fun x a => WP.block_nil ?_
    have ra : Rest [.r1] s x := a.rest (by decide)
    exact ⟨⟨h.2.of_mem a.mem ra ((a.other .r0 (by decide)).trans h.2.ptr),
      h.1.buffers.context.main.congr ra.wr, by rw [a.mem]; exact h.1.main.toCrtLayoutState,
      a.gpr.trans h.1.savedMain, h.1.buffers.context.sepMP⟩, by rw [a.mem]; exact h.1.modulus, h.1.valid,
      h.1.buffers.lengthValid⟩
  have loadCT : RelCT isa (fun s t => CrtSelected g bs1 P s ∧ CrtSelected g bs2 P t ∧ s.sp = t.sp)
      (.block [.ldrSp .r1 8]) (fun _ _ => True) :=
    (loadStack_ct .r1 8).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  -- `n` copied into p's workspace.
  let M := fun (bs : Fin 7 → List Byte) (s : State) =>
    PrecomputeModulus P L g.words s ∧ numAt s.mem (State.addr P) g.words 0 = Spec.Rsa.os2ip (bs 0) ∧
      Spec.Rsa.lenValid g.length
  have copyWP (s : State) {bs : Fin 7 → List Byte} (h : T bs s) : WP isa (transferArray 0 0) s (M bs) := by
    refine (transferArray_ok s h.1 (by decide) (by decide)).mono ?_
    rintro y ⟨readyY, numY, _, _, _⟩
    rw [h.2.1] at numY
    obtain ⟨odd, gt, _⟩ := valid_facts h.2.2.1 h.2.2.2.1
    exact ⟨⟨⟨readyY.workspace, readyY.layout, readyY.width, readyY.ptr, readyY.stackRead, readyY.stackSep,
      readyY.saved⟩, by rw [numY]; exact gt, by rw [numY]; exact odd⟩, numY, h.2.2.2⟩
  have copyCT : RelCT isa (fun s t => T bs1 s ∧ T bs2 t ∧ s.sp = t.sp) (transferArray 0 0) (fun _ _ => True) :=
    (transferArray_ct (by decide) (by decide)).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  have prepCT : RelCT isa (fun s t => M bs1 s ∧ M bs2 t ∧ s.sp = t.sp) prepareModulus (fun _ _ => True) := by
    intro s t tr1 tr2 u w h e1 e2
    have words : g.words ≤ 128 := (crt_width_valid h.1.2.2).2.1
    exact prepareModulus_ct (M := Spec.Rsa.os2ip (bs1 0)) (by omega) s t tr1 tr2 u w
      ⟨⟨h.1.1, h.1.2.1⟩, ⟨h.2.1.1, h.2.1.2.1.trans hn.symm⟩, h.2.2⟩ e1 e2
  rw [modulusR2]
  exact crt_seq_ct pp_selectP_ct (fun s h => selectWP s h) (fun s h => selectWP s h)
    (crt_seq_ct loadCT (fun s h => loadWP s h) (fun s h => loadWP s h)
      (crt_seq_ct copyCT (fun s h => copyWP s h) (fun s h => copyWP s h) prepCT))

theorem pp_modulusPart_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => (CrtShared g bs1 s ∧ PpPre g s ∧ ppFlag s ≤ 1) ∧
      (CrtShared g bs2 t ∧ PpPre g t ∧ ppFlag t ≤ 1) ∧ s.sp = t.sp) modulusPart (fun _ _ => True) := by
  let len := workspaceWords g.words
  let P := crtP g.base g.words
  have mainSize : 256 ≤ 8 * len := by simp only [len, workspaceWords]; omega
  have mainSub {bs : Fin 7 → List Byte} {s : State} (h : CrtShared g bs s) :
      (⟨State.addr g.base, 8 * len⟩ : Region).Sub ⟨State.addr g.base, g.size⟩ :=
    crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits (by simp [crtRegions, len])
  have pSub {bs : Fin 7 → List Byte} {s : State} (h : CrtShared g bs s) :
      (⟨State.addr P, 8 * len⟩ : Region).Sub ⟨State.addr g.base, g.size⟩ :=
    crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits (by simp [crtRegions, len, P])
  -- The main workspace, which the mask's arguments read.
  let Main := fun (s : State) => Workspace s g.base (8 * len) ∧ Layout s.mem (State.addr g.base) len ∧
    wOf s.mem (State.addr g.base) = g.words
  -- p's workspace selected.
  let S1 := fun (s : State) => LayoutFrameReady P len g.words s ∧ PpKept g s ∧
    (⟨State.addr s.sp, 112⟩ : Region).Disjoint ⟨State.addr P, 8 * len⟩ ∧
    Region.Disjoint ⟨State.addr P, 8 * len⟩ ⟨State.addr g.output, 8 * ppPreWords g⟩ ∧ Main s
  have selectWP (s : State) {bs : Fin 7 → List Byte} (h : CrtShared g bs s ∧ PpPre g s ∧ ppFlag s ≤ 1) :
      WP isa selectP s S1 := by
    refine WP.mono (pp_selectP_ok s h.1) ?_
    rintro u ⟨sharedU, readyU, _, restU⟩
    have preU := h.2.1.after restU
    exact ⟨readyU, ⟨sharedU.stack, sharedU.savedMain, preU, sharedU.buffers.lengthValid,
        preU.workspace.sub_left (mainSub sharedU), sharedU.buffers.pPositive, sharedU.buffers.pShort,
        sharedU.buffers.qPositive, sharedU.buffers.qShort⟩,
      sharedU.stack.separate.sub_right (pSub sharedU), preU.workspace.sub_left (pSub sharedU),
      sharedU.buffers.context.main, sharedU.main.layout, sharedU.main.width⟩
  have selectCT : RelCT isa (fun s t => (CrtShared g bs1 s ∧ PpPre g s ∧ ppFlag s ≤ 1) ∧
      (CrtShared g bs2 t ∧ PpPre g t ∧ ppFlag t ≤ 1) ∧ s.sp = t.sp) selectP (fun _ _ => True) :=
    pp_selectP_ct.mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  -- `pre` in r4.
  let S3 := fun (s : State) => ExportState P g.output len g.words (16 * g.words) s ∧ PpKept g s ∧ Main s
  have loadWP (s : State) (h : S1 s) : WP isa (.block [.ldrSp .r4 4]) s S3 := by
    obtain ⟨dl, kept, sep, sepOut, ws, layout, width⟩ := h
    have pre := kept.2.2.1
    have preFit := pre.fit
    have six : 16 * g.words ≤ 8 * ppPreWords g := by simp only [ppPreWords]; omega
    refine wp_loadStack (a := off (State.addr s.sp) 4) (by decide) (addr_add (by have := kept.1.nowrap; omega))
      (kept.1.read (by decide)) fun t a => WP.block_nil ?_
    have rest : Rest [.r4] s t := a.rest (by decide)
    refine ⟨⟨dl.workspace.congr a.wr, by rw [a.mem]; exact dl.layout, by rw [a.mem]; exact dl.width,
      (a.other .r0 (by decide)).trans dl.ptr, a.gpr.trans kept.1.output, by omega, by omega, ?_, ?_⟩,
      kept.after (regions := []) (by rw [a.mem]; exact Frame.refl _ _) rest (by simp),
      ws.congr a.wr, by rw [a.mem]; exact layout, by rw [a.mem]; exact width⟩
    · rw [a.wr]
      have := CallLay.inRegions_sub (off := 0) (l := 16 * g.words) pre.write (by omega) (by omega)
      simpa only [BitVec.add_zero] using this
    · exact sepOut.sub_right (Region.sub_prefix six)
  have loadCT : RelCT isa (fun s t => S1 s ∧ S1 t ∧ s.sp = t.sp) (.block [.ldrSp .r4 4]) (fun _ _ => True) :=
    (loadStack_ct .r4 4).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  -- `n` and `R² mod n` exported.
  let S4 := fun (s : State) => PpKept g s ∧ Main s
  have exportWP (s : State) (h : S3 s) : WP isa precomputeOut s S4 := by
    obtain ⟨ex, kept, ws, layout, width⟩ := h
    refine WP.mono (precomputeOut_ok s ex.workspace ex.layout ex.width ex.fits ex.write ex.separate ex.ptr ex.output) ?_
    rintro t ⟨_, _, frame, rest⟩
    have pre := kept.2.2.1
    have sub : Region.Sub ⟨State.addr g.output, 16 * g.words⟩ ⟨State.addr g.output, 8 * ppPreWords g⟩ :=
      Region.sub_prefix (by simp only [ppPreWords]; omega)
    have eq : WorkspaceEq (State.addr g.base) (8 * len) s.mem t.mem :=
      WorkspaceEq.of_frame (by have := ws.nowrap; omega) frame
        (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact kept.2.2.2.2.1.sub_right sub)
    exact ⟨kept.after frame rest (fun r hr => by
        simp only [List.mem_singleton] at hr; subst r; exact pre.stack.sub_right sub),
      ws.congr rest.wr, eq.layout layout, (eq.width (by have := mainSize; omega)).trans width⟩
  have exportCT : RelCT isa (fun s t => S3 s ∧ S3 t ∧ s.sp = t.sp) precomputeOut (fun _ _ => True) :=
    precomputeOut_ct.mono (fun _ _ h => ⟨h.1.1, h.2.1.1⟩) (fun _ _ _ => trivial)
  -- The mask's arguments, and the mask.
  let S5 := MaskOutputInput g.output (8 * ppPreWords g)
  have argsWP (s : State) (h : S4 s) : WP isa (.block maskArgs) s S5 := by
    obtain ⟨kept, ws, layout, width⟩ := h
    have header := nativeHeader_of_layout s.mem g.base ws.nowrap (Nat.le_refl _) layout
    rw [width] at header
    obtain ⟨p1, p2, q1, q2⟩ := kept.2.2.2.2.2
    refine WP.mono (pp_maskArgs_ok s kept.1 kept.2.1 (by have := ws.nowrap; omega)
      (ws.read (by omega)) header.count kept.2.2.2.1 p1 p2 q1 q2) ?_
    rintro t ⟨r4, r6, mem, rest⟩
    exact ⟨r4, r6, by rw [rest.sp]; have := kept.1.nowrap; omega,
      by rw [rest.rd, rest.wr, rest.sp]; exact kept.1.read (by decide)⟩
  have argsCT : RelCT isa (fun s t => S4 s ∧ S4 t ∧ s.sp = t.sp) (.block maskArgs) (fun _ _ => True) :=
    pp_maskArgs_ct (fun s h => ⟨h.1.2.1, h.1.1.nowrap, h.1.1.read (by decide)⟩)
      (fun s h => ⟨h.1.2.1, h.1.1.nowrap, h.1.1.read (by decide)⟩)
  rw [modulusPart]
  exact crt_seq_ct selectCT (fun s h => selectWP s h) (fun s h => selectWP s h)
    (crt_seq_ct loadCT (fun s h => loadWP s h) (fun s h => loadWP s h)
      (crt_seq_ct exportCT (fun s h => exportWP s h) (fun s h => exportWP s h)
        (crt_seq_ct argsCT (fun s h => argsWP s h) (fun s h => argsWP s h) maskOutput_ct)))

theorem PpValidInput.prepare_input {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : PpValidInput g bs s) : CrtPrepareInput g.base g.modulus g.size g.words g.length (bs 0) s := by
  have mainSub : (⟨State.addr g.base, 8 * workspaceWords g.words⟩ : Region).Sub ⟨State.addr g.base, g.size⟩ :=
    crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits (by simp [crtRegions])
  have source : SavedOperand g.base g.modulus (workspaceWords g.words) g.length 8 12 (bs 0) s :=
    ⟨h.stack.nowrap, ⟨h.stack.read (by decide), h.stack.read (by decide)⟩, h.stack.separate.sub_right mainSub, by decide,
      by decide, h.modulusPtr, h.stack.count, h.buffers.source 0, (h.buffers.sourceSeparate 0).sub_right mainSub⟩
  exact ⟨h.buffers.workspace, h.buffers.context, h.buffers.storageFits, source, h.stack.separate, h.buffers.sourceSeparate 0,
    by simpa only [off, BitVec.add_zero] using h.stack.read (d := 0) (by decide),
    h.stack.write (by decide), h.saved, h.ptr, h.count, h.buffers.lengthValid, rfl⟩

/-- After the validation: the shared state, `pre`, and the acceptance bit. -/
def PpChecked (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop :=
  CrtShared g bs s ∧ PpPre g s ∧ s.mem.readW (off (State.addr s.sp) 48) 32 = (if crtAccepted bs then 1 else 0)

theorem PpChecked.factor {g : CrtGeometry} {bs : Fin 7 → List Byte} {s : State} (h : PpChecked g bs s)
    (j : Fin 6) (prime : j = 1 ∨ j = 2) : PpFactorIn g bs j s := by
  refine ⟨h.1, by unfold ppFlag; rw [h.2.2]; split <;> decide, fun ne => ?_⟩
  have acc : crtAccepted bs := by
    by_contra acc
    unfold ppFlag at ne; rw [h.2.2] at ne; simp [acc] at ne
  rcases prime with rfl | rfl
  · exact (h.1.accepted_factors acc).1
  · exact (h.1.accepted_factors acc).2

theorem PpChecked.accepted {g : CrtGeometry} {bs : Fin 7 → List Byte} {s : State} (h : PpChecked g bs s)
    (ne : ppFlag s ≠ 0) : crtAccepted bs := by
  by_contra acc
  unfold ppFlag at ne; rw [h.2.2] at ne; simp [acc] at ne

/-- After `R² mod n`: it, in p's workspace. -/
def PpReady (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop :=
  PpChecked g bs s ∧
    numAt s.mem (State.addr (crtP g.base g.words)) g.words 4 = 2 ^ (128 * g.words) % Spec.Rsa.os2ip (bs 0)

theorem pp_modulusR2_wp (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : PpChecked g bs s) :
    WP isa modulusR2 s (PpReady g bs) := by
  have pSub : (⟨State.addr (crtP g.base g.words), 8 * workspaceWords g.words⟩ : Region).Sub
      ⟨State.addr g.base, g.size⟩ :=
    crt_region_sub_workspace h.1.buffers.workspace h.1.buffers.storageFits (by simp [crtRegions])
  refine WP.mono (pp_modulusR2_ok s h.1) ?_
  rintro t ⟨shared, _, r2, frame, rest⟩
  refine ⟨⟨shared, h.2.1.after rest, ?_⟩, r2⟩
  rw [rest.sp, ← h.2.2]
  refine frame.readW (r := ⟨off (State.addr s.sp) 48, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (h.1.stack.separate.sub_right pSub).sub_left (Offset.sub_base _ (by decide))
  · exact Offset.disjoint_base _ (by decide) (by decide)

/-- A factor's phase keeps p's workspace. -/
theorem PpReady.after_phase {g : CrtGeometry} {bs : Fin 7 → List Byte} {s t : State} {d : BitVec 32} {n : Nat}
    (h : PpReady g bs s) (dest : PpDest g d n s) (checked : PpChecked g bs t)
    (frame : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, ⟨State.addr s.sp, 4⟩,
      ⟨State.addr d, n⟩] s.mem t.mem) : PpReady g bs t := by
  have pSub : (⟨State.addr (crtP g.base g.words), 8 * workspaceWords g.words⟩ : Region).Sub
      ⟨State.addr g.base, g.size⟩ :=
    crt_region_sub_workspace h.1.1.buffers.workspace h.1.1.buffers.storageFits (by simp [crtRegions])
  have sepP := (h.1.1.child (child := crtP g.base g.words) (slot := 224) (Or.inl ⟨rfl, rfl⟩)).2.2.2.1
  refine ⟨checked, (h.1.1.p_num (regions := [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩,
    ⟨State.addr d, n⟩]) (frame.mono (by simp)) (fun r hr => ?_) (by decide)).trans h.2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sepP
  · exact dest.workspace.sub_left pSub

theorem pp_phaseP_wp (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : PpReady g bs s) :
    WP isa (phase 64 pDest) s (PpReady g bs) := by
  have pre := h.1.2.1
  have words : g.words ≤ 128 := (crt_width_valid h.1.1.buffers.lengthValid).2.1
  have wordsLen : g.length ≤ 8 * g.words := by
    change g.length ≤ 8 * Spec.Rsa.modulusWords g.length; simp only [Spec.Rsa.modulusWords]; omega
  have twoP := pre.words_le
  have dest : PpDest g (ppDestP g) (8 * ppWords g.pLength) s :=
    pre.dest wordsLen (by have := h.1.1.buffers.pShort; omega) pre.addrP (Nat.le_refl _)
      (by simp only [ppPreWords]; omega)
  have fac := h.1.factor 1 (Or.inl rfl)
  refine WP.mono (pp_phase_ok s h.1.1 1 (Or.inl rfl) (fun u hu => pp_pDest_ok u hu) dest fac.2.1 fac.2.2
    (fun ne => ⟨Spec.Rsa.os2ip (bs 3), (h.1.accepted ne).2.2.symm⟩) h.2) ?_
  rintro t ⟨shared, flag, _, frame, rest⟩
  refine h.after_phase dest ⟨shared, pre.after rest, ?_⟩ frame
  rw [← h.1.2.2]; exact BitVec.eq_of_toNat_eq flag

theorem pp_phaseQ_wp (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : PpReady g bs s) :
    WP isa (phase 72 qDest) s (PpReady g bs) := by
  have pre := h.1.2.1
  have words : g.words ≤ 128 := (crt_width_valid h.1.1.buffers.lengthValid).2.1
  have wordsLen : g.length ≤ 8 * g.words := by
    change g.length ≤ 8 * Spec.Rsa.modulusWords g.length; simp only [Spec.Rsa.modulusWords]; omega
  have twoP := pre.words_le
  have dest : PpDest g (ppDestQ g) (8 * ppWords g.qLength) s :=
    pre.dest wordsLen (by have := h.1.1.buffers.pShort; omega) pre.addrQ (by omega)
      (by simp only [ppPreWords]; omega)
  have fac := h.1.factor 2 (Or.inr rfl)
  refine WP.mono (pp_phase_ok s h.1.1 2 (Or.inr rfl) (fun u hu => pp_qDest_ok u hu) dest fac.2.1 fac.2.2
    (fun ne => ⟨Spec.Rsa.os2ip (bs 2), by rw [Nat.mul_comm]; exact (h.1.accepted ne).2.2.symm⟩) h.2) ?_
  rintro t ⟨shared, flag, _, frame, rest⟩
  refine h.after_phase dest ⟨shared, pre.after rest, ?_⟩ frame
  rw [← h.1.2.2]; exact BitVec.eq_of_toNat_eq flag

theorem pp_valid_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte}
    (hn : Spec.Rsa.os2ip (bs1 0) = Spec.Rsa.os2ip (bs2 0)) :
    RelCT isa (fun s t => (PpValidInput g bs1 s ∧ PpPre g s) ∧ (PpValidInput g bs2 t ∧ PpPre g t) ∧ s.sp = t.sp)
      valid (fun _ _ => True) := by
  let V1 := fun (bs : Fin 7 → List Byte) (s : State) => CrtSelected g bs g.base s ∧ PpPre g s
  have prepareWP (s : State) {bs : Fin 7 → List Byte} (h : PpValidInput g bs s ∧ PpPre g s) :
      WP isa CrtFn.prepare s (V1 bs) :=
    (crt_begin_ok s h.1.buffers h.1.stack h.1.ptr h.1.count h.1.saved h.1.modulusPtr h.1.valid).mono
      fun _ j => ⟨⟨j.1, j.2.1⟩, h.2.after j.2.2.2⟩
  have prepareCT : RelCT isa (fun s t => (PpValidInput g bs1 s ∧ PpPre g s) ∧ (PpValidInput g bs2 t ∧ PpPre g t) ∧
      s.sp = t.sp) CrtFn.prepare (fun _ _ => True) :=
    crt_prepare_ct.mono (fun _ _ h => ⟨h.1.1.prepare_input, h.2.1.1.prepare_input, h.2.2⟩) (fun _ _ _ => trivial)
  have validateWP (s : State) {bs : Fin 7 → List Byte} (h : V1 bs s) :
      WP isa (CrtFn.validateWith (validateProductWith lengthCount)) s (PpChecked g bs) := by
    obtain ⟨p0, pLe, q0, qLe, pFit, qFit⟩ := pp_lengthCounts h.1.1
    exact (crt_validateStageWith_ok s h.1.1 h.1.2 (fun x hx => countFrom_lengthCount hx) p0 pLe q0 qLe pFit
      qFit).mono fun _ j => ⟨j.1, h.2.after j.2.2.2.2.2.2, j.2.2.2.2.1⟩
  have validateCT : RelCT isa (fun s t => V1 bs1 s ∧ V1 bs2 t ∧ s.sp = t.sp)
      (CrtFn.validateWith (validateProductWith lengthCount)) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨p0, pLe, q0, qLe, -, -⟩ := pp_lengthCounts h.1.1.1
    exact crt_validateStageWith_ct (fun x hx => countFrom_lengthCount hx) p0 pLe q0 qLe lengthCount_ct
      s t tr1 tr2 u v ⟨h.1.1, h.2.1.1, h.2.2⟩ e1 e2
  have modR2CT : RelCT isa (fun s t => PpChecked g bs1 s ∧ PpChecked g bs2 t ∧ s.sp = t.sp) modulusR2
      (fun _ _ => True) :=
    (pp_modulusR2_ct hn).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  have phasePCT : RelCT isa (fun s t => PpReady g bs1 s ∧ PpReady g bs2 t ∧ s.sp = t.sp)
      (phase 64 pDest) (fun _ _ => True) :=
    (pp_phase_ct (g := g) (bs1 := bs1) (bs2 := bs2) 1 (Or.inl rfl) (dest := pDest) (d := ppDestP g)
      (fun _ u hu => pp_pDest_ok u hu) (fun h1 h2 => pp_pDest_ct h1 h2)).mono
      (fun _ _ h => ⟨h.1.1.factor 1 (Or.inl rfl), h.2.1.1.factor 1 (Or.inl rfl), h.2.2⟩) (fun _ _ _ => trivial)
  have phaseQCT : RelCT isa (fun s t => PpReady g bs1 s ∧ PpReady g bs2 t ∧ s.sp = t.sp)
      (phase 72 qDest) (fun _ _ => True) :=
    (pp_phase_ct (g := g) (bs1 := bs1) (bs2 := bs2) 2 (Or.inr rfl) (dest := qDest) (d := ppDestQ g)
      (fun _ u hu => pp_qDest_ok u hu) (fun h1 h2 => pp_qDest_ct h1 h2)).mono
      (fun _ _ h => ⟨h.1.1.factor 2 (Or.inr rfl), h.2.1.1.factor 2 (Or.inr rfl), h.2.2⟩) (fun _ _ _ => trivial)
  have modCT : RelCT isa (fun s t => PpReady g bs1 s ∧ PpReady g bs2 t ∧ s.sp = t.sp) modulusPart
      (fun _ _ => True) :=
    pp_modulusPart_ct.mono (fun _ _ h => ⟨⟨h.1.1.1, h.1.1.2.1, (h.1.1.factor 1 (Or.inl rfl)).2.1⟩,
      ⟨h.2.1.1.1, h.2.1.1.2.1, (h.2.1.1.factor 1 (Or.inl rfl)).2.1⟩, h.2.2⟩) (fun _ _ _ => trivial)
  rw [valid]
  exact crt_seq_ct prepareCT (fun s h => prepareWP s h) (fun s h => prepareWP s h)
    (crt_seq_ct validateCT (fun s h => validateWP s h) (fun s h => validateWP s h)
      (crt_seq_ct modR2CT (fun s h => pp_modulusR2_wp s h) (fun s h => pp_modulusR2_wp s h)
        (crt_seq_ct phasePCT (fun s h => pp_phaseP_wp s h) (fun s h => pp_phaseP_wp s h)
          (crt_seq_ct phaseQCT (fun s h => pp_phaseQ_wp s h) (fun s h => pp_phaseQ_wp s h) modCT))))

end VG.Proof.Bignum.Arm
