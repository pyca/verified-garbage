module

public import VerifiedGarbage.Proof.Bignum.Arm.PrivPreEnter
public import VerifiedGarbage.Proof.Bignum.Arm.PreparePrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtSavedSources
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.ExportArray
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! # One factor's `R² mod p` at its own width, exported to `pre`

Writes outside the CRT storage, the frame and the sources keep the CRT's
shared state, so the export to `pre` may come between the CRT's stages.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Impl.Bignum.Arm.PrivPreFn VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest)

/-- `w` words read as one number. -/
theorem wordsAt_one_read {m : Mem} {p : Addr} {w x : Nat} (first : (m.read p (8 * w)).toNat = x) :
    Spec.Rsa.wordsAt m p w = Spec.Rsa.toWords x w := by
  have hx : VG.Proof.Bignum.wv m p 0 w = x := by
    rw [← VG.Proof.Bignum.read_eq_wv]; simpa only [off, BitVec.add_zero] using first
  rw [Spec.Rsa.wordsAt, Spec.Rsa.toWords]
  refine List.map_congr_left fun i hi => ?_
  have h := VG.Proof.Bignum.word_eq_ofNat m p 0 w (List.mem_range.mp hi)
  simpa only [Nat.zero_add, hx] using h

theorem CrtCallStack.after_outside {g : CrtGeometry} {s t : State} {rs : List Reg} {regions : List Region}
    (h : CrtCallStack g s) (frame : Frame regions s.mem t.mem) (rest : Rest rs s t)
    (stack : ∀ r ∈ regions, (⟨State.addr s.sp, 112⟩ : Region).Disjoint r) :
    CrtCallStack g t := by
  have kept {d : Nat} (fit : d + 4 ≤ 112) :
      t.mem.readW (off (State.addr s.sp) d) 32 = s.mem.readW (off (State.addr s.sp) d) 32 :=
    frame.readW (r := ⟨off (State.addr s.sp) d, 4⟩) (Region.contains_self _ _)
      (fun r hr => (stack r hr).sub_left (Offset.sub_base _ fit)) (by decide)
  refine ⟨by rw [rest.sp]; exact h.nowrap, by rw [rest.rd, rest.wr, rest.sp]; exact h.readable,
    by rw [rest.wr, rest.sp]; exact h.writable, by rw [rest.sp]; exact h.separate, ?_, ?_, ?_, ?_⟩
  · rw [rest.sp, kept (d := 4) (by decide)]; exact h.output
  · rw [rest.sp, kept (d := 12) (by decide)]; exact h.count
  · intro i
    rw [rest.sp, kept (d := 56 + 8 * i.val) (by have := i.isLt; omega)]
    exact h.pointer i
  · intro i
    rw [rest.sp, kept (d := 60 + 8 * i.val) (by have := i.isLt; omega)]
    exact h.length i

/-- Writes outside the CRT storage, the frame and the sources keep the shared state. -/
theorem CrtShared.after_outside {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    {rs : List Reg} {regions : List Region} (h : CrtShared g bs s)
    (frame : Frame regions s.mem t.mem) (rest : Rest rs s t)
    (ws : ∀ r ∈ regions, (⟨State.addr g.base, g.size⟩ : Region).Disjoint r)
    (stack : ∀ r ∈ regions, (⟨State.addr s.sp, 112⟩ : Region).Disjoint r)
    (sources : ∀ i, ∀ r ∈ regions, (⟨State.addr (g.source i), g.sourceLength i⟩ : Region).Disjoint r) :
    CrtShared g bs t := by
  have eq (base : BitVec 32) (wsB : Workspace s base (8 * workspaceWords g.words))
      (member : (⟨State.addr base, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words) :
      WorkspaceEq (State.addr base) (8 * workspaceWords g.words) s.mem t.mem :=
    WorkspaceEq.of_frame (by have := wsB.nowrap; omega) frame
      (fun r hr => (ws r hr).sub_left (crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits member))
  have mainEq := eq g.base h.buffers.context.main (by simp [crtRegions])
  refine ⟨h.buffers.after_frame frame rest sources, h.stack.after_outside frame rest stack,
    h.main.congr mainEq, h.p.congr (eq _ h.buffers.context.p (by simp [crtRegions])),
    h.q.congr (eq _ h.buffers.context.q (by simp [crtRegions])),
    (mainEq.number h.buffers.context.arraysFit (by decide)).trans h.modulus, h.valid, ?_⟩
  rw [rest.sp]
  have word : t.mem.readW (off (State.addr s.sp) 8) 32 = s.mem.readW (off (State.addr s.sp) 8) 32 :=
    frame.readW (r := ⟨off (State.addr s.sp) 8, 4⟩) (Region.contains_self _ _)
      (fun r hr => (stack r hr).sub_left (Offset.sub_base _ (by decide))) (by decide)
  exact word.trans h.savedMain

/-- Where a factor's values go in `pre`: writable, and apart from the CRT's
storage, frame and sources. -/
structure PpDest (g : CrtGeometry) (d : BitVec 32) (n : Nat) (s : State) : Prop where
  fit : d.toNat + n ≤ 2 ^ 32
  write : InRegions s.wr (State.addr d) n
  workspace : Region.Disjoint ⟨State.addr g.base, g.size⟩ ⟨State.addr d, n⟩
  stack : Region.Disjoint ⟨State.addr s.sp, 112⟩ ⟨State.addr d, n⟩
  sources : ∀ i, Region.Disjoint ⟨State.addr (g.source i), g.sourceLength i⟩ ⟨State.addr d, n⟩

theorem PpDest.after {g : CrtGeometry} {d : BitVec 32} {n : Nat} {s t : State} {rs : List Reg}
    (h : PpDest g d n s) (rest : Rest rs s t) : PpDest g d n t :=
  ⟨h.fit, by rw [rest.wr]; exact h.write, h.workspace, by rw [rest.sp]; exact h.stack, h.sources⟩

/-- The flag at slot 48, as the factor's preparation takes it. -/
def ppFlag (s : State) : Nat := (s.mem.readW (off (State.addr s.sp) 48) 32).toNat

theorem pp_phase_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtShared g bs s)
    (j : Fin 6) (prime : j = 1 ∨ j = 2) {dest : List Instr} {d : BitVec 32}
    (destOk : ∀ u : State, CrtShared g bs u → WP isa (.block dest) u fun t =>
      t.gpr .r4 = d ∧ t.gpr .r2 = BitVec.ofNat 32 4 ∧ t.mem = u.mem ∧ Rest [.r1, .r2, .r3, .r4, .r7] u t)
    (region : PpDest g d (8 * ppWords (g.sourceLength j.succ)) s)
    (bit : ppFlag s ≤ 1)
    (valid : ppFlag s ≠ 0 → 1 < Spec.Rsa.os2ip (bs j.succ) ∧ Spec.Rsa.os2ip (bs j.succ) % 2 = 1) :
    WP isa (phase (56 + 8 * j.val) dest) s fun t =>
      CrtShared g bs t ∧ ppFlag t = ppFlag s ∧
      Spec.Rsa.wordsAt t.mem (State.addr d) (ppWords (g.sourceLength j.succ)) =
        Spec.Rsa.toWords (2 ^ (128 * ppWords (g.sourceLength j.succ)) %
          safePrime (ppFlag s) (Spec.Rsa.os2ip (bs j.succ))) (ppWords (g.sourceLength j.succ)) ∧
      Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, ⟨State.addr s.sp, 4⟩,
        ⟨State.addr d, 8 * ppWords (g.sourceLength j.succ)⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  obtain ⟨two, le, kfit, kpos, _, arrays⟩ := h.pp_fits j prime
  have words : g.words ≤ 128 := (crt_width_valid h.buffers.lengthValid).2.1
  have hj := j.isLt
  let v := ppWords (g.sourceLength j.succ)
  rw [phase, WP.seq_iff]
  refine WP.mono (pp_enterFactor_ok s h j prime) ?_
  rintro z ⟨sharedZ, selectedZ, flagZ, frameZ, restZ⟩
  have primeIn : NarrowPrimeInput (crtN g.base g.words) (g.source j.succ) (workspaceWords g.words) v
      (g.sourceLength j.succ) (56 + 8 * j.val) (bs j.succ) z := by
    refine ⟨selectedZ, ?_, kpos, kfit, by have := sharedZ.stack.nowrap; omega, sharedZ.stack.read (by decide),
      by rw [flagZ]; exact bit, by rw [flagZ]; exact valid⟩
    simpa only [show 56 + 8 * j.val + 4 = 60 + 8 * j.val by omega] using sharedZ.savedOperand j sharedZ.narrow_member
  rw [WP.seq_iff]
  refine WP.mono (crt_narrowPrime_ok z primeIn (by omega)) ?_
  rintro y ⟨readyY, _, _, r2Y, flagY, frameY, restY⟩
  have sharedY := sharedZ.after_narrow (frameY.mono (by simp)) restY
  rw [WP.seq_iff]
  refine WP.mono (destOk y sharedY) ?_
  rintro x ⟨dstX, indexX, memX, restX⟩
  have restZX : Rest roundClobbers s x := restZ.trans (restY.trans (restX.mono (by decide)))
  have regionX := region.after restZX
  have narrowSub := crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits sharedY.narrow_member
  refine WP.mono (exportArray_ok x (readyY.workspace.congr restX.wr) (by rw [memX]; exact readyY.layout)
    (by rw [memX]; exact readyY.width) (o := 4) (by decide) regionX.fit regionX.write
    (regionX.workspace.sub_left narrowSub) ((restX.gpr .r0 (by decide)).trans readyY.ptr) indexX dstX) ?_
  rintro t ⟨value, frameT, _, _, restT⟩
  have restAll : Rest roundClobbers s t := restZX.trans restT
  have dests : ∀ r ∈ [(⟨State.addr d, 8 * v⟩ : Region)], _ := fun r hr => by
    simp only [List.mem_singleton] at hr; subst r; exact regionX.workspace
  have stacks : ∀ r ∈ [(⟨State.addr d, 8 * v⟩ : Region)], (⟨State.addr x.sp, 112⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact regionX.stack
  have sharedT := (sharedY.of_mem memX restX).after_outside frameT restT dests stacks
    (fun i r hr => by simp only [List.mem_singleton] at hr; subst r; exact region.sources i)
  have flagT : ppFlag t = ppFlag x := by
    unfold ppFlag
    rw [restT.sp]
    exact congrArg BitVec.toNat (frameT.readW (r := ⟨off (State.addr x.sp) 48, 4⟩) (Region.contains_self _ _)
      (fun r hr => (stacks r hr).sub_left (Offset.sub_base _ (by decide))) (by decide))
  have flagX : ppFlag x = ppFlag s := by
    unfold ppFlag
    rw [restX.sp, memX, flagY, flagZ]
  refine ⟨sharedT, flagT.trans flagX, ?_, ?_, restAll⟩
  · apply wordsAt_one_read
    rw [value, memX]
    have r2 := r2Y
    rw [flagZ] at r2
    exact r2
  · have fz : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, ⟨State.addr s.sp, 4⟩,
        ⟨State.addr d, 8 * v⟩] s.mem z.mem := frameZ.mono (by simp)
    have fy : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, ⟨State.addr s.sp, 4⟩,
        ⟨State.addr d, 8 * v⟩] z.mem y.mem := frameY.mono (by simp)
    have ft : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, ⟨State.addr s.sp, 4⟩,
        ⟨State.addr d, 8 * v⟩] x.mem t.mem := frameT.mono (by simp [v])
    rw [memX] at ft
    exact fz.trans (fy.trans ft)

end VG.Proof.Bignum.Arm
