module

public import VerifiedGarbage.Proof.Bignum.Arm.PrivPreModulus
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepareState
public import VerifiedGarbage.Proof.Bignum.Arm.PrivPreBlocksCT
public import VerifiedGarbage.Proof.Bignum.Arm.PrivPrePhase
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.PrepareAcceptedPrime
import VerifiedGarbage.Proof.Bignum.Arm.PrepareAcceptedPrimeCT
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
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPrime
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
  have countFits {bs : Fin 7 → List Byte} {s : State} (h : CrtShared g bs s) : 128 * v < 2 ^ 32 := by
    have words : g.words ≤ 128 := (crt_width_valid h.buffers.lengthValid).2.1
    obtain ⟨_, le, _⟩ := h.pp_fits j prime
    change v ≤ g.words at le
    omega
  have prepWP (s : State) {bs : Fin 7 → List Byte} (h : Entered bs s) : WP isa (narrowPrime (56 + 8 * j.val)) s (Prepared bs) := by
    refine WP.mono (crt_narrowPrime_ok s h.2 (countFits h.1)) ?_
    rintro y ⟨readyY, _, _, _, _, frameY, restY⟩
    exact ⟨h.1.after_narrow (frameY.mono (by simp [N])) restY, readyY⟩
  have prepCT : RelCT isa (fun s t => Entered bs1 s ∧ Entered bs2 t ∧ s.sp = t.sp)
      (narrowPrime (56 + 8 * j.val)) (fun _ _ => True) := by
    intro s t tr1 tr2 u w h e1 e2
    exact crt_narrowPrime_ct (countFits h.1.1) s t tr1 tr2 u w ⟨h.1.2, h.2.1.2, h.2.2⟩ e1 e2
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

theorem pp_modulusPart_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
    RelCT isa (fun s t => (CrtShared g bs1 s ∧ PpPre g s ∧ ppFlag s ≤ 1) ∧
      (CrtShared g bs2 t ∧ PpPre g t ∧ ppFlag t ≤ 1) ∧ s.sp = t.sp) modulusPart (fun _ _ => True) := by
  let len := workspaceWords g.words
  have mainSize : 256 ≤ 8 * len := by simp only [len, workspaceWords]; omega
  have mainSub {bs : Fin 7 → List Byte} {s : State} (h : CrtShared g bs s) :
      (⟨State.addr g.base, 8 * len⟩ : Region).Sub ⟨State.addr g.base, g.size⟩ :=
    crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits (by simp [crtRegions, len])
  -- The main workspace selected.
  let S1 := fun (s : State) => AcceptedPrimeInput g.base len g.words s ∧ PpKept g s ∧
    (⟨State.addr s.sp, 112⟩ : Region).Disjoint ⟨State.addr g.base, 8 * len⟩
  have selectWP (s : State) {bs : Fin 7 → List Byte} (h : CrtShared g bs s ∧ PpPre g s ∧ ppFlag s ≤ 1) :
      WP isa selectMain s S1 := by
    refine WP.mono (crt_selectMain_ready s h.1) ?_
    rintro u ⟨sharedU, readyU, frameU, restU⟩
    have flagU := acceptance_after_base_save frameU restU
    refine ⟨⟨readyU, by have := sharedU.stack.nowrap; omega, sharedU.stack.read (by decide),
      by rw [flagU]; exact h.2.2, fun _ => ?_⟩, ⟨sharedU.stack, sharedU.savedMain, h.2.1.after restU, sharedU.buffers.lengthValid,
        h.2.1.workspace.sub_left (mainSub sharedU), sharedU.buffers.pPositive, sharedU.buffers.pShort,
        sharedU.buffers.qPositive, sharedU.buffers.qShort⟩,
      sharedU.stack.separate.sub_right (mainSub sharedU)⟩
    obtain ⟨odd, gt, _⟩ := valid_facts sharedU.valid sharedU.buffers.lengthValid.1
    rw [sharedU.modulus]; exact ⟨gt, odd⟩
  have selectCT : RelCT isa (fun s t => (CrtShared g bs1 s ∧ PpPre g s ∧ ppFlag s ≤ 1) ∧
      (CrtShared g bs2 t ∧ PpPre g t ∧ ppFlag t ≤ 1) ∧ s.sp = t.sp) selectMain (fun _ _ => True) :=
    crt_selectMain_ct.mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  -- `R² mod n`.
  let S2 := fun (s : State) => DoubleLoopReady g.base len g.words 0 s ∧ PpKept g s ∧
    (⟨State.addr s.sp, 112⟩ : Region).Disjoint ⟨State.addr g.base, 8 * len⟩
  have countFits {s : State} (h : PpKept g s) : 128 * g.words < 2 ^ 32 := by
    have := (crt_width_valid h.2.2.2.1).2.1
    change g.words ≤ 128 at this
    omega
  have prepWP (s : State) (h : S1 s) : WP isa prepareAcceptedPrime s S2 := by
    refine WP.mono (prepareAcceptedPrime_ok s h.1 (countFits h.2.1)) ?_
    rintro t ⟨dl, _, _, frame, rest⟩
    refine ⟨dl, h.2.1.after frame rest (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact h.2.2),
      by rw [rest.sp]; exact h.2.2⟩
  have prepCT : RelCT isa (fun s t => S1 s ∧ S1 t ∧ s.sp = t.sp) prepareAcceptedPrime (fun _ _ => True) := by
    intro s t tr1 tr2 u w h e1 e2
    exact prepareAcceptedPrime_ct (countFits h.1.2.1) s t tr1 tr2 u w ⟨h.1.1, h.2.1.1, h.2.2⟩ e1 e2
  -- `pre` in r4.
  let S3 := fun (s : State) => ExportState g.base g.output len g.words (16 * g.words) s ∧ PpKept g s ∧
    (⟨State.addr s.sp, 112⟩ : Region).Disjoint ⟨State.addr g.base, 8 * len⟩
  have loadWP (s : State) (h : S2 s) : WP isa (.block [.ldrSp .r4 4]) s S3 := by
    obtain ⟨dl, kept, sep⟩ := h
    have pre := kept.2.2.1
    have preFit := pre.fit
    have six : 16 * g.words ≤ 8 * ppPreWords g := by simp only [ppPreWords]; omega
    refine wp_loadStack (a := off (State.addr s.sp) 4) (by decide) (addr_add (by have := kept.1.nowrap; omega))
      (kept.1.read (by decide)) fun t a => WP.block_nil ?_
    have rest : Rest [.r4] s t := a.rest (by decide)
    refine ⟨⟨dl.workspace.congr a.wr, by rw [a.mem]; exact dl.layout, by rw [a.mem]; exact dl.width,
      (a.other .r0 (by decide)).trans dl.ptr, a.gpr.trans kept.1.output, by omega, by omega, ?_, ?_⟩,
      kept.after (regions := []) (by rw [a.mem]; exact Frame.refl _ _) rest (by simp), by rw [a.sp]; exact sep⟩
    · rw [a.wr]
      have := CallLay.inRegions_sub (off := 0) (l := 16 * g.words) pre.write (by omega) (by omega)
      simpa only [BitVec.add_zero] using this
    · exact kept.2.2.2.2.1.sub_right (Region.sub_prefix six)
  have loadCT : RelCT isa (fun s t => S2 s ∧ S2 t ∧ s.sp = t.sp) (.block [.ldrSp .r4 4]) (fun _ _ => True) :=
    (loadStack_ct .r4 4).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  -- `n` and `R² mod n` exported.
  let S4 := fun (s : State) => PpKept g s ∧ Workspace s g.base (8 * len) ∧ Layout s.mem (State.addr g.base) len ∧
    wOf s.mem (State.addr g.base) = g.words
  have exportWP (s : State) (h : S3 s) : WP isa precomputeOut s S4 := by
    obtain ⟨ex, kept, sep⟩ := h
    refine WP.mono (precomputeOut_ok s ex.workspace ex.layout ex.width ex.fits ex.write ex.separate ex.ptr ex.output) ?_
    rintro t ⟨_, _, frame, rest⟩
    have pre := kept.2.2.1
    have sub : Region.Sub ⟨State.addr g.output, 16 * g.words⟩ ⟨State.addr g.output, 8 * ppPreWords g⟩ :=
      Region.sub_prefix (by simp only [ppPreWords]; omega)
    have eq : WorkspaceEq (State.addr g.base) (8 * len) s.mem t.mem :=
      WorkspaceEq.of_frame (by have := ex.workspace.nowrap; omega) frame
        (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact ex.separate)
    exact ⟨kept.after frame rest (fun r hr => by
        simp only [List.mem_singleton] at hr; subst r; exact pre.stack.sub_right sub),
      ex.workspace.congr rest.wr, eq.layout ex.layout, (eq.width (by have := mainSize; omega)).trans ex.width⟩
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
    (crt_seq_ct prepCT (fun s h => prepWP s h) (fun s h => prepWP s h)
      (crt_seq_ct loadCT (fun s h => loadWP s h) (fun s h => loadWP s h)
        (crt_seq_ct exportCT (fun s h => exportWP s h) (fun s h => exportWP s h)
          (crt_seq_ct argsCT (fun s h => argsWP s h) (fun s h => argsWP s h) maskOutput_ct))))

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

theorem pp_phaseP_wp (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : PpChecked g bs s) :
    WP isa (phase 64 pDest) s (PpChecked g bs) := by
  have pre := h.2.1
  have words : g.words ≤ 128 := (crt_width_valid h.1.buffers.lengthValid).2.1
  have wordsLen : g.length ≤ 8 * g.words := by
    change g.length ≤ 8 * Spec.Rsa.modulusWords g.length; simp only [Spec.Rsa.modulusWords]; omega
  have twoP := pre.words_le
  have dest : PpDest g (ppDestP g) (8 * ppWords g.pLength) s :=
    pre.dest wordsLen (by have := h.1.buffers.pShort; omega) pre.addrP (Nat.le_refl _)
      (by simp only [ppPreWords]; omega)
  have fac := h.factor 1 (Or.inl rfl)
  refine WP.mono (pp_phase_ok s h.1 1 (Or.inl rfl) (fun u hu => pp_pDest_ok u hu) dest fac.2.1 fac.2.2) ?_
  rintro t ⟨shared, flag, _, _, rest⟩
  refine ⟨shared, pre.after rest, ?_⟩
  rw [← h.2.2]; exact BitVec.eq_of_toNat_eq flag

theorem pp_phaseQ_wp (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : PpChecked g bs s) :
    WP isa (phase 72 qDest) s (PpChecked g bs) := by
  have pre := h.2.1
  have words : g.words ≤ 128 := (crt_width_valid h.1.buffers.lengthValid).2.1
  have wordsLen : g.length ≤ 8 * g.words := by
    change g.length ≤ 8 * Spec.Rsa.modulusWords g.length; simp only [Spec.Rsa.modulusWords]; omega
  have twoP := pre.words_le
  have dest : PpDest g (ppDestQ g) (8 * ppWords g.qLength) s :=
    pre.dest wordsLen (by have := h.1.buffers.pShort; omega) pre.addrQ (by omega)
      (by simp only [ppPreWords]; omega)
  have fac := h.factor 2 (Or.inr rfl)
  refine WP.mono (pp_phase_ok s h.1 2 (Or.inr rfl) (fun u hu => pp_qDest_ok u hu) dest fac.2.1 fac.2.2) ?_
  rintro t ⟨shared, flag, _, _, rest⟩
  refine ⟨shared, pre.after rest, ?_⟩
  rw [← h.2.2]; exact BitVec.eq_of_toNat_eq flag

theorem pp_valid_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} :
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
  have validateWP (s : State) {bs : Fin 7 → List Byte} (h : V1 bs s) : WP isa CrtFn.validate s (PpChecked g bs) :=
    (crt_validateStage_ok s h.1.1 h.1.2).mono fun _ j => ⟨j.1, h.2.after j.2.2.2.2.2.2, j.2.2.2.2.1⟩
  have validateCT : RelCT isa (fun s t => V1 bs1 s ∧ V1 bs2 t ∧ s.sp = t.sp) CrtFn.validate (fun _ _ => True) :=
    crt_validateStage_ct.mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ _ => trivial)
  have phasePCT : RelCT isa (fun s t => PpChecked g bs1 s ∧ PpChecked g bs2 t ∧ s.sp = t.sp)
      (phase 64 pDest) (fun _ _ => True) :=
    (pp_phase_ct (g := g) (bs1 := bs1) (bs2 := bs2) 1 (Or.inl rfl) (dest := pDest) (d := ppDestP g)
      (fun _ u hu => pp_pDest_ok u hu) (fun h1 h2 => pp_pDest_ct h1 h2)).mono
      (fun _ _ h => ⟨h.1.factor 1 (Or.inl rfl), h.2.1.factor 1 (Or.inl rfl), h.2.2⟩) (fun _ _ _ => trivial)
  have phaseQCT : RelCT isa (fun s t => PpChecked g bs1 s ∧ PpChecked g bs2 t ∧ s.sp = t.sp)
      (phase 72 qDest) (fun _ _ => True) :=
    (pp_phase_ct (g := g) (bs1 := bs1) (bs2 := bs2) 2 (Or.inr rfl) (dest := qDest) (d := ppDestQ g)
      (fun _ u hu => pp_qDest_ok u hu) (fun h1 h2 => pp_qDest_ct h1 h2)).mono
      (fun _ _ h => ⟨h.1.factor 2 (Or.inr rfl), h.2.1.factor 2 (Or.inr rfl), h.2.2⟩) (fun _ _ _ => trivial)
  have modCT : RelCT isa (fun s t => PpChecked g bs1 s ∧ PpChecked g bs2 t ∧ s.sp = t.sp) modulusPart
      (fun _ _ => True) :=
    pp_modulusPart_ct.mono (fun _ _ h => ⟨⟨h.1.1, h.1.2.1, (h.1.factor 1 (Or.inl rfl)).2.1⟩,
      ⟨h.2.1.1, h.2.1.2.1, (h.2.1.factor 1 (Or.inl rfl)).2.1⟩, h.2.2⟩) (fun _ _ _ => trivial)
  rw [valid]
  exact crt_seq_ct prepareCT (fun s h => prepareWP s h) (fun s h => prepareWP s h)
    (crt_seq_ct validateCT (fun s h => validateWP s h) (fun s h => validateWP s h)
      (crt_seq_ct phasePCT (fun s h => pp_phaseP_wp s h) (fun s h => pp_phaseP_wp s h)
        (crt_seq_ct phaseQCT (fun s h => pp_phaseQ_wp s h) (fun s h => pp_phaseQ_wp s h) modCT)))

end VG.Proof.Bignum.Arm
