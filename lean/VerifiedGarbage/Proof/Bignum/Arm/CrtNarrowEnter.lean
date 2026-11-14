module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.SetupFrame
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.ActivateWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Set up and select the narrow workspace at a factor's own width -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (Rest Upd wp_ldr wp_mov wp_dp op2_reg op2_imm op2_lsl op2_lsr dpVal)

theorem crt_narrow_link (base : BitVec 32) (w : Nat) :
    base + BitVec.ofNat 32 (modulusOffset w) + (BitVec.ofNat 32 w <<< 4 + BitVec.ofNat 32 8) = crtN base w := by
  have shift : BitVec.ofNat 32 w <<< 4 = BitVec.ofNat 32 (w * 16) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 32 w * BitVec.ofNat 32 16 = _
    rw [← BitVec.ofNat_mul]
  rw [shift, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add, crtN]
  refine congrArg (base + BitVec.ofNat 32 ·) ?_
  simp only [narrowOffset, productBytes, productWords]
  omega_arith

/-- The narrow width: `⌈k/8⌉`, `⌈w/2⌉ = (16 w + 16) / 32`, and the larger, by a mask. -/
theorem narrowWidth_value {k w : Nat} (small : k < 2 ^ 28) (hw : w < 2 ^ 24) :
    (BitVec.ofNat 32 k + 7) >>> 3 +
      (((BitVec.ofNat 32 w <<< 4 + 8 + 8) >>> 5 - (BitVec.ofNat 32 k + 7) >>> 3) &&&
        ((0 : BitVec 32) - ((BitVec.ofNat 32 k + 7) >>> 3 - (BitVec.ofNat 32 w <<< 4 + 8 + 8) >>> 5) >>> 31)) =
      BitVec.ofNat 32 (narrowWords k w) := by
  have ha : (BitVec.ofNat 32 k + 7) >>> 3 = BitVec.ofNat 32 ((k + 7) / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    omega_arith
  have hb : (BitVec.ofNat 32 w <<< 4 + 8 + 8) >>> 5 = BitVec.ofNat 32 ((w + 1) / 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    omega_arith
  rw [ha, hb]
  by_cases lt : (k + 7) / 8 < (w + 1) / 2
  · have sign : (BitVec.ofNat 32 ((k + 7) / 8) - BitVec.ofNat 32 ((w + 1) / 2)) >>> 31 = BitVec.ofNat 32 1 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
        Nat.reducePow]
      omega_arith
    rw [sign, show (0 : BitVec 32) - BitVec.ofNat 32 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes,
      BitVec.add_comm, BitVec.sub_add_cancel, narrowWords, Nat.max_eq_right (by omega_arith)]
  · have sign : (BitVec.ofNat 32 ((k + 7) / 8) - BitVec.ofNat 32 ((w + 1) / 2)) >>> 31 = BitVec.ofNat 32 0 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
        Nat.reducePow]
      omega_arith
    rw [sign, show (0 : BitVec 32) - BitVec.ofNat 32 0 = 0#32 by decide, BitVec.and_zero, BitVec.add_zero, narrowWords,
      Nat.max_eq_left (by omega_arith)]

theorem crt_narrowAddress_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtShared g bs s) :
    WP isa (.block narrowAddress) s fun t =>
      t.gpr .r0 = crtN g.base g.words ∧ t.gpr .r2 = BitVec.ofNat 32 g.words <<< 4 + 8 ∧
      t.mem = s.mem ∧ Rest [.r0, .r1, .r2] s t := by
  have main := h.buffers.context.main
  have size := h.main.toCrtLayoutState.size
  unfold narrowAddress
  refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide)
    (addr_add (by have := h.stack.nowrap; omega_arith)) (h.stack.read (by decide)) fun u a => ?_
  have base : u.gpr .r1 = g.base := a.gpr.trans h.savedMain
  refine wp_ldr (a := off (State.addr g.base) 240) (by decide)
    (by rw [base]; exact addr_add (by have := main.nowrap; omega_arith))
    (by rw [a.rd, a.wr]; exact main.read (by omega_arith)) fun v b => ?_
  refine wp_ldr (a := off (State.addr g.base) 48) (by decide)
    (by rw [b.other .r1 (by decide), base]; exact addr_add (by have := main.nowrap; omega_arith))
    (by rw [b.rd, b.wr, a.rd, a.wr]; exact main.read (by omega_arith)) fun z c => ?_
  refine wp_mov (op2_lsl ⟨by decide, by decide⟩) fun y d => ?_
  refine wp_dp (op2_imm (by decide)) fun x e => ?_
  refine wp_dp (op2_reg _ _) fun t f => WP.block_nil ?_
  have mem : t.mem = s.mem := f.mem.trans (e.mem.trans (d.mem.trans (c.mem.trans (b.mem.trans a.mem))))
  refine ⟨?_, ?_, mem, (a.rest (by decide)).trans ((b.rest (by decide)).trans ((c.rest (by decide)).trans
    ((d.rest (by decide)).trans ((e.rest (by decide)).trans (f.rest (by decide))))))⟩
  rotate_left
  · rw [f.other .r2 (by decide), e.gpr, dpVal, d.gpr, c.gpr, b.mem, a.mem,
      h.main.toCrtLayoutState.nativeCount main]
  rw [f.gpr, dpVal, e.gpr, e.other .r0 (by decide), dpVal, d.gpr, d.other .r0 (by decide), c.gpr,
    c.other .r0 (by decide), b.gpr, b.mem, a.mem, h.main.modulus,
    h.main.toCrtLayoutState.nativeCount main]
  exact crt_narrow_link g.base g.words

theorem crt_narrowWidth_ok (s : State) {slot k w : Nat} (hs : slot < 4096) (fit : s.sp.toNat + slot + 4 ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) slot) 4)
    (count : s.mem.readW (off (State.addr s.sp) slot) 32 = BitVec.ofNat 32 k)
    (wide : s.gpr .r2 = BitVec.ofNat 32 w <<< 4 + 8)
    (small : k < 2 ^ 28) (hw : w < 2 ^ 24) :
    WP isa (.block (narrowWidth slot)) s fun t =>
      t.gpr .r7 = BitVec.ofNat 32 (narrowWords k w) ∧ t.gpr .r3 = 0 ∧ t.mem = s.mem ∧
      Rest [.r1, .r2, .r3, .r7] s t := by
  unfold narrowWidth
  refine wp_loadStack (a := off (State.addr s.sp) slot) hs (addr_add (by omega_arith)) read fun u a => ?_
  refine wp_dp (op2_imm (by decide)) fun v b => ?_
  refine wp_mov (op2_lsr ⟨by decide, by decide⟩) fun z c => ?_
  refine wp_dp (op2_imm (by decide)) fun y d => ?_
  refine wp_mov (op2_lsr ⟨by decide, by decide⟩) fun x e => ?_
  refine wp_dp (op2_reg _ _) fun r f => ?_
  refine wp_mov (op2_lsr ⟨by decide, by decide⟩) fun q g => ?_
  refine wp_mov (op2_imm (by decide)) fun p i => ?_
  refine wp_dp (op2_reg _ _) fun o j => ?_
  refine wp_dp (op2_reg _ _) fun n k' => ?_
  refine wp_dp (op2_reg _ _) fun m l => ?_
  refine wp_dp (op2_reg _ _) fun t o' => WP.block_nil ?_
  have r7z : z.gpr .r7 = (BitVec.ofNat 32 k + 7) >>> 3 := by
    rw [c.gpr, b.gpr, dpVal, a.gpr, count]
  have r2x : x.gpr .r2 = (BitVec.ofNat 32 w <<< 4 + 8 + 8) >>> 5 := by
    rw [e.gpr, d.gpr, dpVal, c.other .r2 (by decide), b.other .r2 (by decide), a.other .r2 (by decide), wide]
  have r7x : x.gpr .r7 = z.gpr .r7 := by rw [e.other .r7 (by decide), d.other .r7 (by decide)]
  have r7n : n.gpr .r7 = z.gpr .r7 := by
    rw [k'.other .r7 (by decide), j.other .r7 (by decide), i.other .r7 (by decide), g.other .r7 (by decide),
      f.other .r7 (by decide), r7x]
  have r1o : o.gpr .r1 = (0 : BitVec 32) - (z.gpr .r7 - x.gpr .r2) >>> 31 := by
    rw [j.gpr, dpVal, i.gpr, i.other .r1 (by decide), g.gpr, f.gpr, dpVal, r7x]
  have r2n : n.gpr .r2 = x.gpr .r2 - z.gpr .r7 := by
    rw [k'.gpr, dpVal, j.other .r2 (by decide), i.other .r2 (by decide), g.other .r2 (by decide),
      f.other .r2 (by decide), j.other .r7 (by decide), i.other .r7 (by decide), g.other .r7 (by decide),
      f.other .r7 (by decide), r7x]
  refine ⟨?_, ?_, o'.mem.trans (l.mem.trans (k'.mem.trans (j.mem.trans (i.mem.trans (g.mem.trans (f.mem.trans
      (e.mem.trans (d.mem.trans (c.mem.trans (b.mem.trans a.mem)))))))))),
    (a.rest (by decide)).trans ((b.rest (by decide)).trans ((c.rest (by decide)).trans ((d.rest (by decide)).trans
      ((e.rest (by decide)).trans ((f.rest (by decide)).trans ((g.rest (by decide)).trans ((i.rest (by decide)).trans
        ((j.rest (by decide)).trans ((k'.rest (by decide)).trans ((l.rest (by decide)).trans
          (o'.rest (by decide))))))))))))⟩
  · rw [o'.gpr, dpVal, l.other .r7 (by decide), l.gpr, dpVal, k'.other .r1 (by decide), r2n, r1o, r7n, r7z, r2x]
    exact narrowWidth_value small hw
  · rw [o'.other .r3 (by decide), l.other .r3 (by decide), k'.other .r3 (by decide), j.other .r3 (by decide), i.gpr]

theorem crt_enterNarrow_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtShared g bs s)
    (j : Fin 6) (prime : j = 1 ∨ j = 2) :
    WP isa (enterNarrow (56 + 8 * j.val + 4)) s fun t =>
      CrtShared g bs t ∧
      LayoutFrameReady (crtN g.base g.words) (workspaceWords g.words) (narrowWords (g.sourceLength j.succ) g.words) t ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩, ⟨State.addr s.sp, 4⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  obtain ⟨two, le, _, _, small, arrays, _⟩ := h.narrow_fits j prime
  have words := (crt_width_valid h.buffers.lengthValid).2.1
  change _ ≤ Spec.Rsa.modulusWords g.length at le
  have hj := j.isLt
  rw [enterNarrow, WP.seq_iff]
  refine WP.mono (crt_narrowAddress_ok s h) ?_
  rintro u ⟨ptrU, wideU, memU, restU⟩
  have sharedU := h.of_mem memU restU
  rw [WP.seq_iff]
  refine WP.mono (crt_narrowWidth_ok u (slot := 56 + 8 * j.val + 4) (by omega_arith)
    (by have := sharedU.stack.nowrap; omega_arith) (sharedU.stack.read (by omega_arith))
    (by simpa only [show 56 + 8 * j.val + 4 = 60 + 8 * j.val by omega_arith] using sharedU.stack.length j)
    wideU (by omega_arith) (by omega_arith)) ?_
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

end VG.Proof.Bignum.Arm
