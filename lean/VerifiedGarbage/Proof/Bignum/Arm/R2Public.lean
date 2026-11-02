module

public import VerifiedGarbage.Impl.Bignum.Arm.R2Normalized
public import VerifiedGarbage.Impl.Bignum.Arm.ArrayCompare
public import VerifiedGarbage.Proof.Bignum.Arm.R2

import VerifiedGarbage.Proof.Bignum.Arm.R2NormalizedConstants
import VerifiedGarbage.Proof.Bignum.Arm.ArrayCompare
import VerifiedGarbage.Proof.Bignum.Arm.R2Init
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.R2Normalized
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Arm.DoubleCountMemory
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopState
/-! The normalized public-modulus path preserves the original R-squared result. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/R2NormalizedCount.lean`, which only this module imported.
section

/-! # Initialize the public R-squared loop count to w+1 -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_str op2_imm dpVal)

theorem r2NormalizedCount_ok (s : State) {base : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fits : 212 ≤ size) (ptr : s.gpr .r0 = base)
    (width : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w) :
    WP isa (.block r2NormalizedCount) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) 208) (BitVec.ofNat 32 (w + 1)) ∧ Rest [.r1] s t := by
  have nowrap := ws.nowrap
  have a48 : State.addr (s.gpr .r0 + BitVec.ofNat 32 48) = off (State.addr base) 48 := by
    rw [ptr]; exact addr_add (by omega)
  have a208 : State.addr (s.gpr .r0 + BitVec.ofNat 32 208) = off (State.addr base) 208 := by
    rw [ptr]; exact addr_add (by omega)
  unfold r2NormalizedCount
  refine wp_ldr (a := off (State.addr base) 48) (by decide) a48 (ws.read (by omega)) fun s1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  refine wp_str (a := off (State.addr base) 208) (by decide)
    (by rw [u2.other .r0 (by decide), u1.other .r0 (by decide)]; exact a208)
    (by rw [u2.wr, u1.wr]; exact ws.write (by omega)) fun t u3 => WP.block_nil ?_
  refine ⟨?_, (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest _))⟩
  rw [u3.mem, u2.mem, u1.mem, u2.gpr, dpVal, u1.gpr, width]
  change s.mem.writeW _ (BitVec.ofNat 32 w + BitVec.ofNat 32 1) = _
  rw [← BitVec.ofNat_add]

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/R2NormalizedCountState.lean`, which only this module imported.
section

/-! Establish the original doubling-loop invariant after normalized initialization. -/

section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt)
open VG.Proof.X25519.Arm (Rest)

theorem r2NormalizedCountState_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s)
    (top : numAt s.mem (State.addr base) w 4 = 2 ^ (64 * w - 1))
    (bound : numAt s.mem (State.addr base) w 4 < numAt s.mem (State.addr base) w 0)
    (two : w32 s.mem (State.addr base) (arrAt w 7) = 2) :
    WP isa (.block r2NormalizedCount) s fun t => DoubleLoopReady base len w (w + 1) t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (64 * w - 1) ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits := h.layout.2.2.1
  have size : 212 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  let c := (s.mem.readW (off (State.addr base) 208) 32).toNat
  have loop : DoubleLoopReady base len w c s :=
    ⟨h.workspace, h.layout, h.width, h.ptr, h.inverse, bound, two,
      by simp only [c, BitVec.ofNat_toNat, BitVec.setWidth_eq], h.stackRead, h.stackSep, h.saved⟩
  refine WP.mono (r2NormalizedCount_ok s h.workspace size h.ptr header.count) ?_
  rintro u ⟨mem, keep⟩
  obtain ⟨next, frame, number, modulus⟩ := loop.after_count mem keep
  exact ⟨next, number.trans top, modulus, frame, keep.mono (by decide)⟩

end VG.Proof.Bignum.Arm
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest wp_subs op2_imm)

structure R2PublicChecked (base : BitVec 32) (len w M : Nat) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  top : numAt s.mem (State.addr base) w 4 = 2 ^ (64 * w - 1)
  two : w32 s.mem (State.addr base) (arrAt w 7) = 2
  modulus : numAt s.mem (State.addr base) w 0 = M
  flag : s.z = if 2 ^ (64 * w - 1) < M then false else true

theorem r2PublicPrepare_ok (s : State) {base : BitVec 32} {len w M : Nat}
    (h : ArithmeticReady base len w s) (initialM : numAt s.mem (State.addr base) w 0 = M) :
    WP isa r2PublicPrepare s fun t => R2PublicChecked base len w M t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [r2PublicPrepare, WP.seq_iff]
  refine WP.mono (r2NormalizedConstants_ok s h) ?_
  rintro u ⟨ready, top, two, modulus, frame, rest⟩
  rw [WP.seq_iff]
  have layout : LayoutFrameReady base len w u :=
    ⟨⟨ready.workspace, ready.layout, ready.width, ready.ptr⟩, ready.stackRead, ready.stackSep, ready.saved⟩
  refine WP.mono (arrayCompare_ok u layout (by decide : 4 < 8) (by decide : 0 < 8)
    (by decide) (by decide)) ?_
  rintro v ⟨layoutV, flag, keeps, frameV, restV⟩
  have fits : arrAt w 8 ≤ 8 * len := ready.width ▸ ready.layout.2.2.1
  have op (i : Nat) (hi : i = 0 ∨ i = 4 ∨ i = 7) : Operand i := by
    rcases hi with rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have oldTop := (keeps_array_num keeps fits (op 4 (by decide)) (by decide)).trans top
  have oldTwo := keeps_array_word (d := 0) (bits := 32) keeps fits (op 7 (by decide)) (by decide) (by omega)
  simp only [Nat.add_zero] at oldTwo
  have oldTwoNat := congrArg BitVec.toNat oldTwo
  change w32 v.mem (State.addr base) (arrAt w 7) = w32 u.mem (State.addr base) (arrAt w 7) at oldTwoNat
  have readyV := (ready.after_array (by decide : 3 ≠ 0) keeps frameV restV layoutV.ptr).1
  have modV := (keeps_array_num keeps fits (op 0 (by decide)) (by decide)).trans modulus
  refine wp_subs (op2_imm (by decide)) fun z keep zero => WP.block_nil ?_
  have readyZ := readyV.of_mem keep.mem (keep.rest (ws := [.r11]) (by decide))
    ((keep.other .r0 (by decide)).trans readyV.ptr)
  have modZ : numAt z.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 := by
    rw [keep.mem]; exact modV
  have frameZ : Frame [⟨State.addr base, 8 * len⟩] s.mem z.mem := by
    rw [keep.mem]; exact frame.trans frameV
  have restZ : Rest roundClobbers s z :=
    rest.trans (restV.trans ((keep.rest (ws := [.r11]) (by decide)).mono (by decide)))
  refine ⟨⟨readyZ, ?_, ?_, modZ.trans initialM, ?_⟩, frameZ, restZ⟩
  · rw [keep.mem]; exact oldTop
  · rw [keep.mem, oldTwoNat]; exact two
  · rw [zero, flag, top, modulus, initialM]
    split <;> simp

def r2PublicCount (w M : Nat) : Nat := if 2 ^ (64 * w - 1) < M then w + 1 else 65 * w

structure R2PublicInitialized (base : BitVec 32) (len w M : Nat) (s : State) : Prop where
  ready : DoubleLoopReady base len w (r2PublicCount w M) s
  value : numAt s.mem (State.addr base) w 4 = if 2 ^ (64 * w - 1) < M then 2 ^ (64 * w - 1) else 1
  modulus : numAt s.mem (State.addr base) w 0 = M
  large : 1 < M

theorem r2PublicInit_ok (s : State) {base : BitVec 32} {len w M : Nat}
    (h : ArithmeticReady base len w s) (initialM : numAt s.mem (State.addr base) w 0 = M) :
    WP isa r2PublicInit s fun t => R2PublicInitialized base len w M t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [r2PublicInit, WP.seq_iff]
  refine WP.mono (r2PublicPrepare_ok s h initialM) ?_
  rintro z ⟨checked, frameZ, restZ⟩
  have large : 1 < M := initialM ▸ h.modulus
  by_cases normalized : 2 ^ (64 * w - 1) < M
  · have zflag : z.z = false := by rw [checked.flag]; simp [normalized]
    refine WP.ite true (by simp [eval, zflag]) (fun _ => ?_) (by simp)
    refine WP.mono (r2NormalizedCountState_ok z checked.ready checked.top
      (by rw [checked.top, checked.modulus]; exact normalized) checked.two) ?_
    rintro t ⟨ready, value, modulus, frame, rest⟩
    exact ⟨⟨by simpa only [r2PublicCount, normalized, ite_true] using ready,
      by simpa only [normalized, ite_true] using value, modulus.trans checked.modulus, large⟩,
      frameZ.trans frame, restZ.trans rest⟩
  · have zflag : z.z = true := by rw [checked.flag]; simp [normalized]
    refine WP.ite false (by simp [eval, zflag]) (by simp) (fun _ => ?_)
    refine WP.mono (r2Init_ok z checked.ready) ?_
    rintro t ⟨ready, value, modulus, frame, rest⟩
    exact ⟨⟨by simpa only [r2PublicCount, normalized, ite_false] using ready,
      by simpa only [normalized, ite_false] using value, modulus.trans checked.modulus, large⟩,
      frameZ.trans frame, restZ.trans rest⟩

theorem r2PublicLoop_ok (s : State) {base : BitVec 32} {len w M : Nat}
    (h : R2PublicInitialized base len w M s) (countFits : 128 * w < 2 ^ 32) :
    WP isa doubleLoop s fun t => R2Sq base len w M w t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  by_cases normalized : 2 ^ (64 * w - 1) < M
  · have ready : DoubleLoopReady base len w (w + 1) s := by
      simpa only [r2PublicCount, normalized, ite_true] using h.ready
    have top : numAt s.mem (State.addr base) w 4 = 2 ^ (64 * w - 1) := by
      simpa only [normalized, ite_true] using h.value
    simpa only [h.modulus] using r2NormalizedLoop_ok s ready top (h.modulus ▸ h.large) countFits
  · have ready : DoubleLoopReady base len w (65 * w) s := by
      simpa only [r2PublicCount, normalized, ite_false] using h.ready
    have one : numAt s.mem (State.addr base) w 4 = 1 := by
      simpa only [normalized, ite_false] using h.value
    simpa only [h.modulus] using r2Loop_ok s ready one (h.modulus ▸ h.large) countFits

theorem r2Public_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) (countFits : 128 * w < 2 ^ 32) :
    WP isa r2Public s fun t => DoubleLoopReady base len w 0 t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [r2Public, WP.seq_iff]
  refine WP.mono (r2PublicInit_ok s h rfl) ?_
  rintro u ⟨ready, frame, rest⟩
  rw [WP.seq_iff]
  refine WP.mono (r2PublicLoop_ok u ready countFits) ?_
  rintro v ⟨sq, frameV, restV⟩
  refine WP.mono (r2Squares_ok v sq) ?_
  rintro t ⟨fin, frameT, restT⟩
  have value : numAt t.mem (State.addr base) w 4 =
      2 ^ (128 * w) % numAt s.mem (State.addr base) w 0 := by
    rw [← Nat.mod_eq_of_lt fin.operand, fin.value, show 64 * w + 64 * w = 128 * w by omega]
  exact ⟨⟨fin.ready.workspace, fin.ready.layout, fin.ready.width, fin.ready.ptr, fin.ready.inverse,
    by rw [fin.modulus]; exact fin.operand, fin.two, fin.counter,
    fin.ready.stackRead, fin.ready.stackSep, fin.ready.saved⟩,
    value, fin.modulus, frame.trans (frameV.trans frameT), rest.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm
