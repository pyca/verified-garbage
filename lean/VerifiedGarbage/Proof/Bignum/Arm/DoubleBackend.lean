module

public import VerifiedGarbage.Impl.Bignum.Arm.DoubleCall
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpDoubling
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallEntry
public import VerifiedGarbage.Proof.Bignum.Arm.CallStack
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnBody
import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnRestore
import VerifiedGarbage.Proof.Bignum.Arm.MontCallCT
import VerifiedGarbage.Proof.Bignum.Arm.MontCallArgsReady
import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Bignum.Arm.DoubleCall
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved

/-! # The callable modular doubling and its calls

`DoubleCall.code` takes the callable product's arguments (`CallInput`) and
an array `a` that starts with 2, and doubles array `b` modulo the modulus
into array `o`, preserving the procedure-call ABI. Called as
`MontCall.op name callee 4 7 4` it is one doubling of R-squared's loop
(`sharedDoubling`), writing only the workspace and the 48 bytes below the
caller's stack pointer that a call of the product also uses.
-/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

/-- The callee's precondition: the product's, and the scalar 2 in array `a`. -/
abbrev DoubleCallInput (base : BitVec 32) (len w o a b : Nat) (s : State) : Prop :=
  CallInput base len w o a b s ∧ w32 s.mem (State.addr base) (arrAt w a) = 2

def DoubleResult (base : BitVec 32) (len w o b : Nat) (s t : State) : Prop :=
  numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
  numAt t.mem (State.addr base) w o =
    (2 * numAt s.mem (State.addr base) w b) % numAt s.mem (State.addr base) w 0 ∧
  Keeps (State.addr base) len w o s.mem t.mem

theorem doubleCallFn_ok (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : DoubleCallInput base len w o a b s) (ho : Operand o) (ha : Operand a) (hb : Operand b) :
    WP isa DoubleCall.code s fun t => abiPreserved s t ∧ DoubleResult base len w o b s t := by
  have input := h.1
  have nowrap := input.workspace.nowrap
  have fits : arrAt w 8 ≤ 8 * len := input.width ▸ input.layout.2.2.1
  have eq := input.pushed_eq
  have framePush := FrameStack.pushed_frameA (rs := MontCall.savedRegs) input.stackFit
  unfold DoubleCall.code
  refine WP.frame (by decide) input.stackFit (by decide) ?_
  rw [WP.seq_iff]
  refine WP.mono (call_entry_ok s input hb.1) ?_
  rintro u ⟨ready, memU, restU⟩
  rw [WP.seq_iff]
  have aEnd := Nat.le_trans (array_end_le (w := w) ha.1) fits
  have two : w32 u.mem (State.addr base) (arrAt w a) = 2 := by
    change (u.mem.readW (off (State.addr base) (arrAt w a)) 32).toNat = 2
    rw [memU, eq.word (d := arrAt w a) (bits := 32) (by omega_using [aEnd])]
    exact h.2
  have body := doubleFnBody_ok u ready.workspace ready.layout ho ha hb ready.ptr
    ready.outIndex ready.aIndex ready.bIndex
    (by rw [ready.width]; exact two) (by rw [ready.width]; exact ready.inverse)
    (by rw [ready.width]; exact ready.operand)
  simp only [ready.width] at body
  refine WP.mono body ?_
  rintro v ⟨lt, value, keeps, frameBody, restV0⟩
  have restV : Rest roundClobbers u v := restV0
  have spV : v.sp = s.sp - BitVec.ofNat 32 40 := restV.sp.trans restU.sp
  have wrV : v.wr = (callPushed s).wr := restV.wr.trans restU.wr
  rw [memU] at lt value keeps frameBody
  have saved : Spill.Saved v.mem (State.addr v.sp) s.gpr callAllSaved := by
    rw [spV]
    have savedPush : Spill.Saved (callPushed s).mem (State.addr (s.sp - BitVec.ofNat 32 40)) s.gpr callAllSaved :=
      call_push_saved s input.stackFit
    exact savedPush.frame (lo := 0) (hi := 40) (by decide) frameBody (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst r
      simpa only [FrameStack.belowA, BitVec.add_zero, Nat.sub_zero] using input.stackWorkspace)
  have stackFit : v.sp.toNat + 40 ≤ 2 ^ 32 := by
    rw [spV, FrameStack.sub_toNat' input.stackFit]
    have := s.sp.isLt
    omega_using []
  have writable : (⟨State.addr v.sp, 40⟩ : Region) ∈ v.wr := by
    rw [wrV, spV]
    exact List.mem_cons_self
  refine WP.mono (call_restore_ok v s.gpr stackFit ⟨_, List.mem_append_right _ writable, Region.contains_self _ _⟩ saved) ?_
  rintro t ⟨restored, memT, restT⟩ ml ul hfl
  have spT : t.sp = s.sp - BitVec.ofNat 32 40 := restT.sp.trans spV
  have oldM := eq.number fits (by decide : 0 < 8)
  have oldB := eq.number fits hb.1
  rw [oldM] at lt
  rw [oldM, oldB] at value
  have lostEq : WorkspaceEq (State.addr base) (8 * len) t.mem ml :=
    WorkspaceEq.of_frame (by omega_using [nowrap]) hfl (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; exact input.stackWorkspace.symm)
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro r hr
    have ne : r ≠ .r12 := by intro he; subst r; simp [preserved] at hr
    rw [popped_gpr ne]
    have member : r ∈ callCalleeSaved.map Prod.fst := by
      simpa only [callCalleeSaved, List.map_cons, List.map_nil, preserved] using hr
    obtain ⟨p, hp, eqr⟩ := List.mem_map.mp member
    rw [← eqr]
    exact restored p hp
  · rw [popped_sp, spT]
    exact BitVec.sub_add_cancel _ _
  · dsimp only; rw [lostEq.number fits ho.1, memT]; exact lt
  · dsimp only; rw [lostEq.number fits ho.1, memT]; exact value
  · intro i hi separate
    dsimp only
    rw [show ml (State.addr base + BitVec.ofNat 64 i) = t.mem (State.addr base + BitVec.ofNat 64 i)
      from lost_byte hfl (R := ⟨State.addr base, 8 * len⟩) input.stackWorkspace.symm hi, memT, keeps i hi separate]
    exact framePush.bytes (R := ⟨State.addr base, 8 * len⟩)
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact input.stackWorkspace.symm)
      (by change 8 * len ≤ 2 ^ 64; omega_using [nowrap]) hi

theorem doubleCallFn_ct {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b) :
    RelCT isa (fun s t => DoubleCallInput base len w o a b s ∧
      DoubleCallInput base len w o a b t ∧ s.sp = t.sp) DoubleCall.code (fun _ _ => True) := by
  unfold DoubleCall.code
  apply RelCT.frame (fun _ _ h => h.2.2)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨hs, ht, sp⟩, ps, pt⟩ := hp
  have ps' := push_pushed (rs := MontCall.savedRegs) (by decide) hs.1.stackFit
  have pt' := push_pushed (rs := MontCall.savedRegs) (by decide) ht.1.stackFit
  have es : callPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : callPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  cases e1 with
  | seq entry1 tail1 =>
    cases e2 with
    | seq entry2 tail2 =>
      obtain ⟨trace, sp'⟩ := loadStack_ct .r12 40 _ _ _ _ _ _ (by simp only [callPushed, pushed_sp, sp]) entry1 entry2
      obtain ⟨_, s1, run1, ready1, mem1, rest1⟩ := call_entry_ok s0 hs.1 hb.1
      obtain ⟨_, t1, run2, ready2, mem2, rest2⟩ := call_entry_ok t0 ht.1 hb.1
      obtain ⟨-, rfl⟩ := Exec.det entry1 run1
      obtain ⟨-, rfl⟩ := Exec.det entry2 run2
      have hw : 2 ≤ w := hs.1.width ▸ hs.1.layout.1
      have fit : arrAt w 8 ≤ 8 * len := hs.1.width ▸ hs.1.layout.2.2.1
      have tmpFits : arrAt w 3 + 32 ≤ 8 * len := by
        have := array_end_le (w := w) (j := 3) (k := 8) (by decide)
        omega_using [hw, fit, this]
      have aEnd := Nat.le_trans (array_end_le (w := w) ha.1) fit
      have twoAfter (x : State) (hx : DoubleCallInput base len w o a b x) (y : State)
          (mem : y.mem = (callPushed x).mem) : w32 y.mem (State.addr base) (arrAt w a) = 2 := by
        change (y.mem.readW (off (State.addr base) (arrAt w a)) 32).toNat = 2
        rw [mem, hx.1.pushed_eq.word (d := arrAt w a) (bits := 32) (by omega_using [aEnd])]
        exact hx.2
      have body := relCT_keep_sp ((doubleFnBody_ct (base := base) ho ha hb tmpFits (by omega_using [hw])).mono
        (P' := fun (x y : State) => DoubleFnReady base len w o a b x ∧ DoubleFnReady base len w o a b y ∧ x.sp = y.sp)
        (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)
      obtain ⟨tailTrace, _⟩ := body.seq montCallRestore_ct _ _ _ _ _ _
        ⟨⟨ready1, twoAfter s0 hs _ mem1⟩, ⟨ready2, twoAfter t0 ht _ mem2⟩, sp'⟩ tail1 tail2
      exact ⟨by rw [trace, tailTrace], trivial⟩

theorem doubleCallInvoke_ok (name : String) (callee : Prog isa)
    {base : BitVec 32} {len w o a b : Nat}
    (correct : ∀ s, DoubleCallInput base len w o a b s →
      WP isa callee s fun t => abiPreserved s t ∧ DoubleResult base len w o b s t)
    (stack : armStack callee ≤ 40) (s : State) (h : DoubleCallInput base len w o a b s) :
    WP isa (.call name callee) s fun t =>
      DoubleResult base len w o b s t ∧
      Frame [⟨State.addr base, 8 * len⟩, belowA s.sp 40] s.mem t.mem ∧ Rest roundClobbers s t := by
  let rd : List Region := [⟨State.addr s.sp, 4⟩]
  let wr : List Region := [⟨State.addr base, 8 * len⟩]
  let k : Contract isa := {
    pre := DoubleCallInput base len w o a b
    post := DoubleResult base len w o b
    pub := fun _ _ => True }
  have pre : k.pre (s.callEntry.withRegions rd wr) := by
    refine ⟨⟨⟨h.1.workspace.nowrap, by simp only [State.withRegions_wr, wr, List.mem_singleton]⟩,
      h.1.layout, h.1.width, ?_, ?_, ?_, h.1.bArg, h.1.inverse, h.1.operand, h.1.stackFit, ?_,
      h.1.stackWorkspace, h.1.stackArg⟩, h.2⟩
    · exact (State.callEntry_gpr s (by decide)).trans h.1.ptr
    · exact (State.callEntry_gpr s (by decide)).trans h.1.outIndex
    · exact (State.callEntry_gpr s (by decide)).trans h.1.aIndex
    · exact ⟨_, List.mem_append_left _ List.mem_cons_self, Region.contains_self _ _⟩
  have coversWr : Covers wr s.wr := Covers.one ⟨_, h.1.workspace.writable, Region.contains_self _ _⟩
  have coversRd : Covers rd (s.rd ++ s.wr) := Covers.one h.1.argRead
  refine WP.callF (k := k) correct pre
    (Covers.append_left coversRd (Covers.right coversWr)) coversWr (by have := h.1.stackFit; omega_using [stack, this]) ?_
  intro t rdEq wrEq spEq frame _ result
  refine ⟨result, FrameStack.Frame.belowA_mono frame stack h.1.stackFit, ?_⟩
  exact ⟨by intro r hr; exact False.elim (hr (by cases r <;> simp [roundClobbers])),
    rdEq, wrEq, spEq⟩

/-- The doubling loop's state supplies the product's arithmetic state. -/
theorem DoubleLoopReady.arithmetic {s : State} {base : BitVec 32} {len w c : Nat}
    (h : DoubleLoopReady base len w c s) (large : 1 < numAt s.mem (State.addr base) w 0) :
    ArithmeticReady base len w s :=
  ⟨h.workspace, h.layout, h.width, h.ptr, h.inverse, large, h.stackRead, h.stackSep, h.saved⟩

/-- A call that keeps all but array four, the workspace and the space below
the stack keeps the doubling loop's state. -/
theorem DoubleLoopReady.after_call {s t : State} {base : BitVec 32} {len w c : Nat}
    (h : DoubleLoopReady base len w c s) (cs : CallStack base len s)
    (bound : numAt t.mem (State.addr base) w 4 < numAt s.mem (State.addr base) w 0)
    (keeps : Keeps (State.addr base) len w 4 s.mem t.mem)
    (frame : Frame [⟨State.addr base, 8 * len⟩, belowA s.sp 48] s.mem t.mem)
    (rest : Rest roundClobbers s t) (ptr : t.gpr .r0 = base) :
    DoubleLoopReady base len w c t ∧ numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have kl := keeps_layout h.layout (by rw [h.width]; exact keeps)
  have oldM := keeps_array_num keeps fits op0 (by decide)
  have oldLow := keeps_array_word (d := 0) (bits := 64) keeps fits op0 (by decide) (by omega_using [])
  have oldTwo := keeps_array_word (d := 0) (bits := 32) keeps fits
    (show Operand 7 by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide) (by omega_using [])
  simp only [Nat.add_zero] at oldLow oldTwo
  refine ⟨⟨h.workspace.congr rest.wr, kl.2, kl.1.trans h.width, ptr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, oldM⟩
  · change ((t.mem.readW (off (State.addr base) (arrAt w 0)) 64).toNat *
      (t.mem.readW (off (State.addr base) 56) 64).toNat + 1) % 2 ^ 64 = 0
    rw [oldLow, keeps_header_readW keeps size (d := 56) (bits := 64) (by decide)]
    exact h.inverse
  · rw [oldM]; exact bound
  · change (t.mem.readW (off (State.addr base) (arrAt w 7)) 32).toNat = 2
    rw [oldTwo]; exact h.two
  · rw [keeps_header_readW keeps size (d := 208) (bits := 32) (by decide)]; exact h.counter
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
  · rw [rest.sp]; exact h.stackSep
  · rw [rest.sp]
    have sep : Region.Disjoint ⟨State.addr s.sp, 4⟩ (FrameStack.belowA s.sp 48) := by
      rw [FrameStack.belowA, FrameStack.addr_sub' cs.fit]
      exact (Offset.below_disjoint _ (by decide)).symm
    exact (frame.readW (r := ⟨State.addr s.sp, 4⟩) (Region.contains_self _ _)
      (by intro r hr
          rcases List.mem_cons.mp hr with hr | hr
          · subst r; exact h.stackSep
          · have er := List.mem_singleton.mp hr; subst r; exact sep) (by decide)).trans h.saved

theorem doubleCallArgs_input (s u : State) {base : BitVec 32} {len w c : Nat}
    (h : DoubleLoopReady base len w c s) (large : 1 < numAt s.mem (State.addr base) w 0)
    (cs : CallStack base len s)
    (eq : WorkspaceEq (State.addr base) (8 * len) s.mem u.mem)
    (ptrU : u.gpr .r0 = base) (outU : u.gpr .r2 = BitVec.ofNat 32 4)
    (aU : u.gpr .r3 = BitVec.ofNat 32 7)
    (memU : u.mem = s.mem.writeW (State.addr (allocated 8 s).sp) (BitVec.ofNat 32 4))
    (restU : Rest [.r1, .r2, .r3, .r12, .lr] (allocated 8 s) u) :
    DoubleCallInput base len w 4 7 4 u := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have aEnd := Nat.le_trans (array_end_le (w := w) (j := 7) (k := 8) (by decide)) fits
  refine ⟨montCallArgs_input s u (h.arithmetic large) cs
    (show Operand 4 by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) h.operand
    eq ptrU outU aU memU restU, ?_⟩
  change (u.mem.readW (off (State.addr base) (arrAt w 7)) 32).toNat = 2
  rw [eq.word (d := arrAt w 7) (bits := 32) (by omega_using [aEnd])]
  exact h.two

theorem doubleCallArgs_ready (s : State) {base : BitVec 32} {len w c : Nat}
    (h : DoubleLoopReady base len w c s) (large : 1 < numAt s.mem (State.addr base) w 0)
    (cs : CallStack base len s) :
    WP isa (.block (MontCall.opArgs 4 7 4)) (allocated 8 s) (DoubleCallInput base len w 4 7 4) := by
  let A := allocated 8 s
  have fit8 : 8 ≤ s.sp.toNat := by have := cs.fit; omega_using [this]
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  have argsWs : Workspace A base (8 * len) :=
    ⟨h.workspace.nowrap, List.mem_cons_of_mem _ h.workspace.writable⟩
  have argsWrite : InRegions A.wr (State.addr A.sp) 4 :=
    ⟨⟨State.addr A.sp, 8⟩, List.mem_cons_self,
      by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide⟩
  have argsFit : A.sp.toNat + 8 ≤ 2 ^ 32 := by
    change (s.sp - BitVec.ofNat 32 8).toNat + 8 ≤ 2 ^ 32
    rw [sub_toNat' fit8]; have := s.sp.isLt; omega_using []
  have argSub : Region.Sub ⟨State.addr A.sp, 4⟩ (belowA s.sp 48) :=
    fun x hx => belowA_sub (a := 8) (by decide) cs.fit x (Region.sub_prefix (by decide) x hx)
  have argSep := cs.separate.sub_left argSub
  refine WP.mono (montCallArgs_ok A argsWs (by omega_using [size]) h.ptr argsFit argsWrite
    (by decide) (by decide) (by decide)) ?_
  rintro u ⟨ptrU, outU, aU, memU, frameU, restU⟩
  have eq := WorkspaceEq.of_frame (by have := h.workspace.nowrap; omega_using [this] : 8 * len < 2 ^ 64)
    frameU (by intro r hr; have er := List.mem_singleton.mp hr; subst r; exact argSep.symm)
  exact doubleCallArgs_input s u h large cs eq ptrU outU aU memU restU

theorem doubleCallOp_ok (name : String) (callee : Prog isa)
    {base : BitVec 32} {len w c : Nat}
    (correct : ∀ s, DoubleCallInput base len w 4 7 4 s →
      WP isa callee s fun t => abiPreserved s t ∧ DoubleResult base len w 4 4 s t)
    (stack : armStack callee ≤ 40) (s : State)
    (h : DoubleLoopReady base len w c s) (large : 1 < numAt s.mem (State.addr base) w 0)
    (cs : CallStack base len s) :
    WP isa (MontCall.op name callee 4 7 4) s fun t =>
      DoubleLoopReady base len w c t ∧ CallStack base len t ∧
      numAt t.mem (State.addr base) w 4 =
        (2 * numAt s.mem (State.addr base) w 4) % numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩, belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  let A := allocated 8 s
  have fit8 : 8 ≤ s.sp.toNat := by have := cs.fit; omega_using [this]
  have argSub : Region.Sub ⟨State.addr A.sp, 4⟩ (belowA s.sp 48) :=
    fun x hx => belowA_sub (a := 8) (by decide) cs.fit x (Region.sub_prefix (by decide) x hx)
  have argSep : Region.Disjoint ⟨State.addr A.sp, 4⟩ ⟨State.addr base, 8 * len⟩ :=
    cs.separate.sub_left argSub
  have argsWs : Workspace A base (8 * len) :=
    ⟨h.workspace.nowrap, List.mem_cons_of_mem _ h.workspace.writable⟩
  have argsWrite : InRegions A.wr (State.addr A.sp) 4 :=
    ⟨⟨State.addr A.sp, 8⟩, List.mem_cons_self, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide⟩
  have argsFit : A.sp.toNat + 8 ≤ 2 ^ 32 := by
    change (s.sp - BitVec.ofNat 32 8).toNat + 8 ≤ 2 ^ 32
    rw [sub_toNat' fit8]; have := s.sp.isLt; omega_using []
  unfold MontCall.op
  rw [WP.seq_iff]
  apply WP.alloc (by decide) fit8
  rw [WP.seq_iff]
  refine WP.mono (montCallArgs_ok A argsWs (by omega_using [size]) h.ptr argsFit argsWrite
    (by decide) (by decide) (by decide)) ?_
  rintro u ⟨ptrU, outU, aU, memU, frameU, restU⟩
  change u.mem = s.mem.writeW (State.addr A.sp) (BitVec.ofNat 32 4) at memU
  change Frame [⟨State.addr A.sp, 4⟩] s.mem u.mem at frameU
  have eq := WorkspaceEq.of_frame (by have := h.workspace.nowrap; omega_using [this] : 8 * len < 2 ^ 64)
    frameU (by intro r hr; have er := List.mem_singleton.mp hr; subst r; exact argSep.symm)
  have input := doubleCallArgs_input s u h large cs eq ptrU outU aU memU restU
  refine WP.mono (doubleCallInvoke_ok name callee correct stack u input) ?_
  rintro v ⟨⟨bound, value, keeps⟩, frameV, restV⟩
  have restUV : Rest roundClobbers A v :=
    (restU.mono (by intro r _; cases r <;> simp [roundClobbers])).trans restV
  have frameArgs : Frame [⟨State.addr base, 8 * len⟩, belowA s.sp 48] s.mem u.mem :=
    frameU.sub fun r hr => by
      have er := List.mem_singleton.mp hr; subst r
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), argSub⟩
  have frameCall : Frame [⟨State.addr base, 8 * len⟩, belowA s.sp 48] u.mem v.mem :=
    frameV.sub fun r hr => by
      rcases List.mem_cons.mp hr with hr | hr
      · subst r; exact ⟨_, List.mem_cons_self, fun _ hx => hx⟩
      · have er := List.mem_singleton.mp hr; subst r
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
        rw [restU.sp]
        exact belowA_inner (a := 40) (k := 8) (by decide) cs.fit
  have frame := frameArgs.trans frameCall
  have keepsAll : Keeps (State.addr base) len w 4 s.mem v.mem := by
    intro i hi separate
    exact (keeps i hi separate).trans (frameU.bytes (R := ⟨State.addr base, 8 * len⟩)
      (by intro r hr; have er := List.mem_singleton.mp hr; subst r; exact argSep.symm)
      (by change 8 * len ≤ 2 ^ 64; have := h.workspace.nowrap; omega_using [this]) hi)
  rw [eq.number fits (by decide : 0 < 8)] at bound value
  rw [eq.number fits (by decide : 4 < 8)] at value
  intro ml ul hfl
  change Frame [belowA s.sp 8] v.mem ml at hfl
  have lostSub : Region.Sub (belowA s.sp 8) (belowA s.sp 48) := belowA_sub (by decide) cs.fit
  have lostWs : (belowA s.sp 8).Disjoint ⟨State.addr base, 8 * len⟩ := cs.separate.sub_left lostSub
  have lostEq := WorkspaceEq.of_frame (by have := h.workspace.nowrap; omega_using [this] : 8 * len < 2 ^ 64)
    hfl (by intro r hr; have er := List.mem_singleton.mp hr; subst r; exact lostWs.symm)
  rw [← lostEq.number fits (by decide : 4 < 8)] at bound value
  have keepsLost : Keeps (State.addr base) len w 4 s.mem ml := by
    intro i hi separate
    exact (lost_byte hfl (R := ⟨State.addr base, 8 * len⟩) lostWs.symm hi).trans (keepsAll i hi separate)
  have frame : Frame [⟨State.addr base, 8 * len⟩, belowA s.sp 48] s.mem ml :=
    frame.trans (hfl.sub fun r hr => by
      have er := List.mem_singleton.mp hr; subst r
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), lostSub⟩)
  have freeRest : Rest roundClobbers s { freed 8 v with mem := ml, unknowns := ul } := by
    refine ⟨by intro r hr; exact False.elim (hr (by cases r <;> simp [roundClobbers])), restUV.rd, ?_, ?_⟩
    · change v.wr.tail = s.wr; rw [restUV.wr]; rfl
    · change v.sp + BitVec.ofNat 32 8 = s.sp
      rw [restUV.sp]; exact BitVec.sub_add_cancel _ _
  have saved : ({ freed 8 v with mem := ml, unknowns := ul } : State).mem.readW
      (State.addr ({ freed 8 v with mem := ml, unknowns := ul } : State).sp) 32 = base := by
    rw [freeRest.sp]
    have sep : Region.Disjoint ⟨State.addr s.sp, 4⟩ (belowA s.sp 48) := by
      rw [belowA, addr_sub' cs.fit]
      exact (Offset.below_disjoint _ (by decide)).symm
    exact (frame.readW (r := ⟨State.addr s.sp, 4⟩) (Region.contains_self _ _)
      (by intro r hr
          rcases List.mem_cons.mp hr with hr | hr
          · subst r; exact h.stackSep
          · have er := List.mem_singleton.mp hr; subst r; exact sep) (by decide)).trans h.saved
  refine WP.mono (restoreBase_ok { freed 8 v with mem := ml, unknowns := ul }
    (by rw [freeRest.rd, freeRest.wr, freeRest.sp]; exact h.stackRead) saved) ?_
  rintro t ⟨ptrT, memT, restT⟩
  change t.mem = ml at memT
  have rest := freeRest.trans (restT.mono (by intro r _; cases r <;> simp [roundClobbers]))
  rw [← memT] at keepsLost frame bound value
  obtain ⟨ready, modulus⟩ := h.after_call cs bound keepsLost frame rest ptrT
  exact ⟨ready, cs.of_rest rest, value, modulus, frame, rest⟩

theorem doubleCall_rawCall_ct (name : String) (callee : Prog isa)
    {base : BitVec 32} {len w o a b : Nat}
    (ct : RelCT isa (fun s t => DoubleCallInput base len w o a b s ∧
      DoubleCallInput base len w o a b t ∧ s.sp = t.sp) callee (fun _ _ => True)) :
    RelCT isa (fun s t => DoubleCallInput base len w o a b s ∧
      DoubleCallInput base len w o a b t ∧ s.sp = t.sp) (.call name callee) (fun _ _ => True) := by
  intro s t tr1 tr2 u v hp e1 e2
  cases e1 with
  | call p1 b1 q1 =>
    cases e2 with
    | call p2 b2 q2 =>
      rw [call_callEntry, Option.some.injEq] at p1 p2
      subst p1 p2
      obtain ⟨trace, _⟩ := ct _ _ _ _ _ _
        ⟨⟨hp.1.1.callEntry, hp.1.2⟩, ⟨hp.2.1.1.callEntry, hp.2.1.2⟩, hp.2.2⟩ b1 b2
      exact ⟨by simpa only [isa, List.map_nil, List.nil_append, List.append_nil] using trace, trivial⟩

theorem doubleCallOp_ct (name : String) (callee : Prog isa)
    {base : BitVec 32} {len w c : Nat}
    (ct : RelCT isa (fun s t => DoubleCallInput base len w 4 7 4 s ∧
      DoubleCallInput base len w 4 7 4 t ∧ s.sp = t.sp) callee (fun _ _ => True)) :
    RelCT isa (fun s t => (DoubleLoopReady base len w c s ∧ 1 < numAt s.mem (State.addr base) w 0) ∧
      (DoubleLoopReady base len w c t ∧ 1 < numAt t.mem (State.addr base) w 0) ∧
      CallStack base len s ∧ CallStack base len t ∧ s.sp = t.sp)
      (MontCall.op name callee 4 7 4) (fun s t => s.sp = t.sp) := by
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨hs, ht, cs, ctStack, sp⟩ := hp
  have fitS : 8 ≤ s.sp.toNat := by have := cs.fit; omega_using [this]
  have fitT : 8 ≤ t.sp.toNat := by have := ctStack.fit; omega_using [this]
  have fits : VG.Proof.Rsa.Mont.arrAt w 8 ≤ 8 * len := hs.1.width ▸ hs.1.layout.2.2.1
  have size : 52 ≤ 8 * len := by simp only [VG.Proof.Rsa.Mont.arrAt, VG.Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  unfold MontCall.op at e1 e2
  cases e1 with
  | seq f1 restore1 =>
    cases e2 with
    | seq f2 restore2 =>
      have frameSp := (Exec.sp f1).trans (sp.trans (Exec.sp f2).symm)
      obtain ⟨restoreTrace, finalSp⟩ := loadStack_ct .r0 0 _ _ _ _ _ _ frameSp restore1 restore2
      cases f1 with
      | frame p1 b1 q1 =>
        cases f2 with
        | frame p2 b2 q2 =>
          have allocS : isa.push (.alloc 8) s = some (allocated 8 s) := by
            simp only [isa, push, fitS]
            rfl
          have allocT : isa.push (.alloc 8) t = some (allocated 8 t) := by
            simp only [isa, push, fitT]
            rfl
          have eqS := Option.some.inj (allocS.symm.trans p1)
          have eqT := Option.some.inj (allocT.symm.trans p2)
          subst eqS eqT
          cases b1 with
          | seq args1 call1 =>
            cases b2 with
            | seq args2 call2 =>
              obtain ⟨_, s1, runS, inputS⟩ := doubleCallArgs_ready s hs.1 hs.2 cs
              obtain ⟨_, t1, runT, inputT⟩ := doubleCallArgs_ready t ht.1 ht.2 ctStack
              rw [(Exec.det runS args1).2] at inputS
              rw [(Exec.det runT args2).2] at inputT
              have argsSp : _ := (Exec.sp args1).trans
                ((show (allocated 8 s).sp = (allocated 8 t).sp by simp only [allocated, sp]).trans (Exec.sp args2).symm)
              obtain ⟨callTrace, _⟩ := doubleCall_rawCall_ct name callee ct _ _ _ _ _ _
                ⟨inputS, inputT, argsSp⟩ call1 call2
              have writeS : InRegions (allocated 8 s).wr (State.addr (allocated 8 s).sp) 4 :=
                ⟨⟨State.addr (allocated 8 s).sp, 8⟩, List.mem_cons_self, by
                  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide⟩
              have writeT : InRegions (allocated 8 t).wr (State.addr (allocated 8 t).sp) 4 :=
                ⟨⟨State.addr (allocated 8 t).sp, 8⟩, List.mem_cons_self, by
                  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide⟩
              have traceS := montCallArgs_trace (allocated 8 s)
                ⟨hs.1.workspace.nowrap, List.mem_cons_of_mem _ hs.1.workspace.writable⟩ size hs.1.ptr writeS
                (by decide) (by decide) (by decide) args1
              have traceT := montCallArgs_trace (allocated 8 t)
                ⟨ht.1.workspace.nowrap, List.mem_cons_of_mem _ ht.1.workspace.writable⟩ size ht.1.ptr writeT
                (by decide) (by decide) (by decide) args2
              exact ⟨by simp only [addrs, List.map_nil, List.nil_append, List.append_nil]
                        rw [traceS, traceT, callTrace, restoreTrace]
                        simp only [allocated, sp], finalSp⟩

end VG.Proof.Bignum.Arm

namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Arm.FrameStack VG.Impl.Bignum.Arm

/-- One doubling as a call of `callee`, for a caller whose 48 bytes below
the stack pointer are free. -/
def sharedDoubling (base sp : BitVec 32) (len w : Nat) (name : String) (callee : Prog isa)
    (correct : ∀ s, DoubleCallInput base len w 4 7 4 s →
      WP isa callee s fun t => abiPreserved s t ∧ DoubleResult base len w 4 4 s t)
    (stack : armStack callee ≤ 40) :
    Doubling base len w (CallReady base sp len) [⟨State.addr base, 8 * len⟩, belowA sp 48] where
  dbl := MontCall.op name callee 4 7 4
  workspace := by simp
  stable := by
    intro s t _ rest h
    exact ⟨h.1.of_rest rest, rest.sp.trans h.2⟩
  dbl_ok := by
    intro s c h large hp
    refine WP.mono (doubleCallOp_ok name callee correct stack s h large hp.1) ?_
    rintro t ⟨ready, cs, value, modulus, frame, rest⟩
    rw [hp.2] at frame
    exact ⟨ready, value, modulus, ⟨cs, rest.sp.trans hp.2⟩, frame, rest⟩

theorem sharedDoublingTiming (base sp : BitVec 32) (len w : Nat) (name : String) (callee : Prog isa)
    (correct : ∀ s, DoubleCallInput base len w 4 7 4 s →
      WP isa callee s fun t => abiPreserved s t ∧ DoubleResult base len w 4 4 s t)
    (stack : armStack callee ≤ 40)
    (ct : RelCT isa (fun s t => DoubleCallInput base len w 4 7 4 s ∧
      DoubleCallInput base len w 4 7 4 t ∧ s.sp = t.sp) callee (fun _ _ => True)) :
    DoublingTiming (sharedDoubling base sp len w name callee correct stack) := by
  constructor
  intro c
  exact (doubleCallOp_ct name callee (c := c) ct).mono
    (fun _ _ h => ⟨⟨h.1.1, h.1.2.1⟩, ⟨h.2.1.1, h.2.1.2.1⟩, h.1.2.2.1, h.2.1.2.2.1, h.2.2⟩)
    (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm.TwoExp

/-! ## Each Montgomery implementation's callable doubling

The doubling of an implementation (`MontBackend.dblCallee`) is
`DoubleCall.code` as the implementation rewrites its callers
(`MontBackend.caller`), so that its rows are the implementation's;
`vg_rsa_mont_double` with the implementation's suffix.
-/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (Operand)

def MontBackend.dblName (b : MontBackend) : String := "vg_rsa_mont_double" ++ b.suffix

def MontBackend.dblCallee (b : MontBackend) : Prog isa := b.caller.code DoubleCall.code

/-- One doubling of R-squared's loop: array four doubled, by a call. -/
def MontBackend.dbl (b : MontBackend) : Prog isa := MontCall.op b.dblName b.dblCallee 4 7 4

theorem doubleCall_codeOk : VG.Arm.Scrub.CodeOk DoubleCall.code 40 := by lit_decide

theorem doubleCall_stack : armStack DoubleCall.code ≤ 40 := doubleCall_codeOk.1

theorem MontBackend.dbl_stack (b : MontBackend) : armStack b.dblCallee ≤ 40 :=
  Nat.le_trans (b.caller.stack_le _) doubleCall_stack

theorem MontBackend.dblOk (b : MontBackend) : VG.Arm.Scrub.CodeOk b.dblCallee 40 :=
  b.callerOk _ _ doubleCall_codeOk

theorem MontBackend.dbl_correct (b : MontBackend) {base : BitVec 32} {len w : Nat} (s : State)
    (h : DoubleCallInput base len w 4 7 4 s) :
    WP isa b.dblCallee s fun t => abiPreserved s t ∧ DoubleResult base len w 4 4 s t := by
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  obtain ⟨tr, t, run, post⟩ := doubleCallFn_ok s h op4 op7 op4
  exact ⟨tr, t, b.caller.sim _ run, post⟩

theorem MontBackend.dbl_ct (b : MontBackend) {base : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => DoubleCallInput base len w 4 7 4 s ∧
      DoubleCallInput base len w 4 7 4 t ∧ s.sp = t.sp) b.dblCallee (fun _ _ => True) := by
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  intro s t tr1 tr2 u v h e1 e2
  obtain ⟨_, _, run1, _⟩ := doubleCallFn_ok s h.1 op4 op7 op4
  obtain ⟨_, _, run2, _⟩ := doubleCallFn_ok t h.2.1 op4 op7 op4
  obtain ⟨trace1, rfl⟩ := Exec.det (b.caller.sim _ run1) e1
  obtain ⟨trace2, rfl⟩ := Exec.det (b.caller.sim _ run2) e2
  obtain ⟨trace, _⟩ := doubleCallFn_ct op4 op7 op4 s t _ _ _ _ h run1 run2
  exact ⟨by rw [← trace1, ← trace2, trace], trivial⟩

/-- The implementation's doubling, called from a frame whose 48 bytes below
the stack pointer are free. -/
def MontBackend.doubling (b : MontBackend) (base sp : BitVec 32) (len w : Nat) :
    TwoExp.Doubling base len w (TwoExp.CallReady base sp len) [⟨State.addr base, 8 * len⟩, belowA sp 48] :=
  TwoExp.sharedDoubling base sp len w b.dblName b.dblCallee (b.dbl_correct) b.dbl_stack

theorem MontBackend.doublingTiming (b : MontBackend) (base sp : BitVec 32) (len w : Nat) :
    TwoExp.DoublingTiming (b.doubling base sp len w) :=
  TwoExp.sharedDoublingTiming base sp len w b.dblName b.dblCallee (b.dbl_correct) b.dbl_stack b.dbl_ct

theorem MontBackend.doubling_dbl (b : MontBackend) (base sp : BitVec 32) (len w : Nat) :
    (b.doubling base sp len w).dbl = b.dbl := rfl

/-- A doubling for every workspace whose caller leaves it the 48 bytes below
the stack, as `CallOp` is a product: one code `dbl`, with its proofs. -/
structure CallDbl where
  dbl : Prog isa
  doubling : ∀ (base sp : BitVec 32) (len w : Nat),
    TwoExp.Doubling base len w (TwoExp.CallReady base sp len) [⟨State.addr base, 8 * len⟩, belowA sp 48]
  doubling_dbl : ∀ base sp len w, (doubling base sp len w).dbl = dbl
  timing : ∀ (base sp : BitVec 32) (len w : Nat), TwoExp.DoublingTiming (doubling base sp len w)

/-- A call to `b`'s doubling. -/
def MontBackend.callDbl (b : MontBackend) : CallDbl :=
  ⟨b.dbl, b.doubling, b.doubling_dbl, b.doublingTiming⟩

end VG.Proof.Bignum.Arm
