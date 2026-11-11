module

public import VerifiedGarbage.Impl.Bignum.Arm.PrivPreFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowEnter
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowEnterCT
import VerifiedGarbage.Proof.Bignum.Arm.SetupFrame
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspaceCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Bignum.Arm.PrivPreFn
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
meta import VerifiedGarbage.Proof.Bignum.Arm.RoundState
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowEnter
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowEnterCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SetupFrame
meta import VerifiedGarbage.Proof.Bignum.Arm.Stack
meta import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspace
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspaceCT
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # A factor's own Montgomery width in the narrow workspace

The private precomputation prepares each factor in the CRT's narrow
workspace at `max(2, ⌈len/8⌉)` limbs, the width of the factor's values in
`pre` (`Spec.Rsa.primeWords`).
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Impl.Bignum.Arm.PrivPreFn VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (Rest Upd wp_ldr wp_mov wp_dp op2_reg op2_imm op2_lsl op2_lsr dpVal)

/-- The limbs of a factor of `k` bytes: `max(2, ⌈k/8⌉)`. -/
def ppWords (k : Nat) : Nat := max 2 ((k + 7) / 8)

theorem ppWords_eq (k : Nat) : ppWords k = Spec.Rsa.primeWords k := rfl

theorem ppWords_bounds {k n w : Nat} (short : k < n) (hn : 64 ≤ n)
    (hw : w = Spec.Rsa.modulusWords n) :
    2 ≤ ppWords k ∧ ppWords k ≤ w ∧ k ≤ 8 * ppWords k := by
  subst hw
  simp only [ppWords, Spec.Rsa.modulusWords] at *
  omega

/-- The factor's limbs fit the narrow workspace, which the full width sizes. -/
theorem CrtShared.pp_fits {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtShared g bs s)
    (j : Fin 6) (prime : j = 1 ∨ j = 2) :
    2 ≤ ppWords (g.sourceLength j.succ) ∧ ppWords (g.sourceLength j.succ) ≤ g.words ∧
      g.sourceLength j.succ ≤ 8 * ppWords (g.sourceLength j.succ) ∧ 0 < g.sourceLength j.succ ∧
      g.sourceLength j.succ ≤ 1024 ∧
      arrAt (ppWords (g.sourceLength j.succ)) 8 ≤ 8 * workspaceWords g.words := by
  have bounds : 0 < g.sourceLength j.succ ∧ g.sourceLength j.succ < g.length := by
    rcases prime with rfl | rfl
    · exact ⟨h.buffers.pPositive, h.buffers.pShort⟩
    · exact ⟨h.buffers.qPositive, h.buffers.qShort⟩
  obtain ⟨two, le, fit⟩ := ppWords_bounds (w := g.words) bounds.2 h.buffers.lengthValid.1 rfl
  refine ⟨two, le, fit, bounds.1, by have := h.buffers.lengthValid.2; omega, ?_⟩
  have arrays := h.buffers.context.arraysFit
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at arrays ⊢
  change _ ≤ g.words at le
  have := Nat.mul_le_mul_left 8 (Nat.add_le_add_right le 2)
  omega

/-- The width: `⌈k/8⌉`, and one more when that is one. -/
theorem primeWidth_value {k : Nat} (positive : 0 < k) (small : k < 2 ^ 28) :
    (BitVec.ofNat 32 k + 7) >>> 3 + ((BitVec.ofNat 32 k + 7) >>> 3 - 2) >>> 31 =
      BitVec.ofNat 32 (ppWords k) := by
  have ha : (BitVec.ofNat 32 k + 7) >>> 3 = BitVec.ofNat 32 ((k + 7) / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    omega_arith
  rw [ha]
  have := positive
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow, ppWords]
  omega_arith

theorem primeWidth_ok (s : State) {slot k : Nat} (hs : slot < 4096) (fit : s.sp.toNat + slot + 4 ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) slot) 4)
    (count : s.mem.readW (off (State.addr s.sp) slot) 32 = BitVec.ofNat 32 k)
    (positive : 0 < k) (small : k < 2 ^ 28) :
    WP isa (.block (primeWidth slot)) s fun t =>
      t.gpr .r7 = BitVec.ofNat 32 (ppWords k) ∧ t.gpr .r3 = 0 ∧ t.mem = s.mem ∧
      Rest [.r1, .r3, .r7] s t := by
  unfold primeWidth
  refine wp_loadStack (a := off (State.addr s.sp) slot) hs (addr_add (by omega_arith)) read fun u a => ?_
  refine wp_dp (op2_imm (by decide)) fun v b => ?_
  refine wp_mov (op2_lsr ⟨by decide, by decide⟩) fun z c => ?_
  refine wp_dp (op2_imm (by decide)) fun y d => ?_
  refine wp_mov (op2_lsr ⟨by decide, by decide⟩) fun x e => ?_
  refine wp_dp (op2_reg _ _) fun r f => ?_
  refine wp_mov (op2_imm (by decide)) fun t g => WP.block_nil ?_
  have r7z : z.gpr .r7 = (BitVec.ofNat 32 k + 7) >>> 3 := by
    rw [c.gpr, b.gpr, dpVal, a.gpr, count]
  refine ⟨?_, ?_, g.mem.trans (f.mem.trans (e.mem.trans (d.mem.trans (c.mem.trans (b.mem.trans a.mem))))),
    (a.rest (by decide)).trans ((b.rest (by decide)).trans ((c.rest (by decide)).trans ((d.rest (by decide)).trans
      ((e.rest (by decide)).trans ((f.rest (by decide)).trans (g.rest (by decide)))))))⟩
  · rw [g.other .r7 (by decide), f.gpr, dpVal, e.other .r7 (by decide), d.other .r7 (by decide), e.gpr, d.gpr,
      dpVal, r7z]
    exact primeWidth_value positive small
  · rw [g.gpr]

theorem pp_enterFactor_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtShared g bs s)
    (j : Fin 6) (prime : j = 1 ∨ j = 2) :
    WP isa (enterFactor (56 + 8 * j.val + 4)) s fun t =>
      CrtShared g bs t ∧
      LayoutFrameReady (crtN g.base g.words) (workspaceWords g.words) (ppWords (g.sourceLength j.succ)) t ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, ⟨State.addr s.sp, 4⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  obtain ⟨two, le, _, pos, small, arrays⟩ := h.pp_fits j prime
  have words := (crt_width_valid h.buffers.lengthValid).2.1
  change _ ≤ Spec.Rsa.modulusWords g.length at le
  have hj := j.isLt
  rw [enterFactor, WP.seq_iff]
  refine WP.mono (crt_narrowAddress_ok s h) ?_
  rintro u ⟨ptrU, _, memU, restU⟩
  have sharedU := h.of_mem memU restU
  rw [WP.seq_iff]
  refine WP.mono (primeWidth_ok u (slot := 56 + 8 * j.val + 4) (by omega_arith)
    (by have := sharedU.stack.nowrap; omega_arith) (sharedU.stack.read (by omega_arith))
    (by simpa only [show 56 + 8 * j.val + 4 = 60 + 8 * j.val by omega_arith] using sharedU.stack.length j)
    pos (by omega_arith)) ?_
  rintro v ⟨widthV, zeroV, memV, restV⟩
  have sharedV := sharedU.of_mem memV restV
  have ptrV : v.gpr .r0 = crtN g.base g.words := (restV.gpr .r0 (by decide)).trans ptrU
  rw [WP.seq_iff]
  refine WP.mono (setup_frame_ok v sharedV.buffers.context.narrow two (by omega_arith) arrays ptrV widthV zeroV) ?_
  rintro z ⟨layoutZ, widthZ, ptrZ, frameZ, restZ⟩
  have sharedZ := sharedV.after_narrow (frameZ.mono (by simp)) restZ
  have flagZ := sharedV.acceptance_after_workspace sharedV.narrow_member frameZ restZ
  refine WP.mono (activateWorkspace_ok z (by simpa only [off, BitVec.add_zero] using sharedZ.stack.write (d := 0) (by decide))) ?_
  rintro t ⟨memT, frameT, restT⟩
  rw [ptrZ] at memT
  obtain ⟨sharedT, readyT⟩ := crt_selectedWidth_ready sharedZ sharedZ.buffers.context.narrow ⟨layoutZ, widthZ⟩
    sharedZ.narrow_member ((restT.gpr .r0 (by decide)).trans ptrZ) memT frameT restT
  have restUV : Rest roundClobbers s v := (restU.mono (by decide)).trans (restV.mono (by decide))
  have restUZ := restUV.trans restZ
  rw [memV, memU] at frameZ
  have flagT := acceptance_after_base_save frameT restT
  rw [restUZ.sp] at frameT
  exact ⟨sharedT, readyT, flagT.trans (flagZ.trans (by rw [restUV.sp, memV, memU])),
    (frameZ.mono (by simp)).trans (frameT.mono (by simp)), restUZ.trans (restT.mono (by simp [roundClobbers]))⟩

theorem primeWidth_ct (slot : Nat) :
    RelCT isa (fun s t => s.sp = t.sp) (.block (primeWidth slot)) (fun s t => s.sp = t.sp) := by
  have rest : RelCT isa (fun s t => s.sp = t.sp)
      (.block [.dp .add .r7 .r7 (.imm 7), .mov .r7 (.shifted .r7 .lsr 3),
        .dp .sub .r1 .r7 (.imm 2), .mov .r1 (.shifted .r1 .lsr 31), .dp .add .r7 .r7 (.reg .r1),
        .mov .r3 (.imm 0)]) (fun s t => s.sp = t.sp) := by
    apply relCT_keep_sp (sp := fun _ _ h => h)
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append (M := isa) (l₁ := [.ldrSp .r7 slot])
    ((loadStack_ct .r7 slot).seq rest)

theorem pp_enterFactor_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (j : Fin 6) (prime : j = 1 ∨ j = 2) :
    RelCT isa (fun s t => CrtShared g bs1 s ∧ CrtShared g bs2 t ∧ s.sp = t.sp)
      (enterFactor (56 + 8 * j.val + 4)) (fun _ _ => True) := by
  have hj := j.isLt
  let Addressed := fun (bs : Fin 7 → List Byte) (s : State) => CrtShared g bs s ∧ s.gpr .r0 = crtN g.base g.words
  have addressWP (s : State) {bs : Fin 7 → List Byte} (h : CrtShared g bs s) :
      WP isa (.block narrowAddress) s (Addressed bs) :=
    (crt_narrowAddress_ok s h).mono fun _ j => ⟨h.of_mem j.2.2.1 j.2.2.2, j.1⟩
  let Sized := fun (bs : Fin 7 → List Byte) (s : State) => CrtShared g bs s ∧ s.gpr .r0 = crtN g.base g.words ∧
    s.gpr .r7 = BitVec.ofNat 32 (ppWords (g.sourceLength j.succ)) ∧ s.gpr .r3 = 0
  have widthWP (s : State) {bs : Fin 7 → List Byte} (h : Addressed bs s) :
      WP isa (.block (primeWidth (56 + 8 * j.val + 4))) s (Sized bs) := by
    obtain ⟨_, _, _, pos, small, _⟩ := h.1.pp_fits j prime
    refine WP.mono (primeWidth_ok s (slot := 56 + 8 * j.val + 4) (by omega)
      (by have := h.1.stack.nowrap; omega) (h.1.stack.read (by omega))
      (by simpa only [show 56 + 8 * j.val + 4 = 60 + 8 * j.val by omega] using h.1.stack.length j)
      pos (by omega)) ?_
    rintro t ⟨width, zero, mem, rest⟩
    exact ⟨h.1.of_mem mem rest, (rest.gpr .r0 (by simp)).trans h.2, width, zero⟩
  have widthCT : RelCT isa (fun s t => Addressed bs1 s ∧ Addressed bs2 t ∧ s.sp = t.sp)
      (.block (primeWidth (56 + 8 * j.val + 4))) (fun _ _ => True) :=
    (primeWidth_ct _).mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  have setupCT : RelCT isa (fun s t => Sized bs1 s ∧ Sized bs2 t ∧ s.sp = t.sp) setup (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨setup_ct s t tr1 tr2 u v trivial trivial (h.1.2.1.trans h.2.1.2.1.symm) e1 e2, trivial⟩
  have setupWP (s : State) {bs : Fin 7 → List Byte} (h : Sized bs s) : WP isa setup s (fun _ => True) := by
    obtain ⟨two, le, _, _, _, arrays⟩ := h.1.pp_fits j prime
    have words := (crt_width_valid h.1.buffers.lengthValid).2.1
    change _ ≤ Spec.Rsa.modulusWords g.length at le
    exact (setup_frame_ok s h.1.buffers.context.narrow two (by omega) arrays h.2.1 h.2.2.1 h.2.2.2).mono
      fun _ _ => trivial
  have activate : RelCT isa (fun s t => True ∧ True ∧ s.sp = t.sp) (.block activateWorkspace) (fun _ _ => True) :=
    activateWorkspace_ct.mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial)
  exact crt_seq_ct crt_narrowAddress_ct (fun s h => addressWP s h) (fun s h => addressWP s h)
    (crt_seq_ct widthCT (fun s h => widthWP s h) (fun s h => widthWP s h)
      (crt_seq_ct setupCT (fun s h => setupWP s h) (fun s h => setupWP s h) activate))

end VG.Proof.Bignum.Arm
