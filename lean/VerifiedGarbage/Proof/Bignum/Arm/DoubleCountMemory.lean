module

import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.TCB.Arm.Isa

/-! ### `Bignum.Arm.DoubleLoopState`, which this module and modules that import it used -/

section

/-! # Workspace and stack invariants shared by repeated modular doublings -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Layout Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

structure DoubleLoopReady (base : BitVec 32) (len w c : Nat) (s : State) : Prop where
  workspace : Workspace s base (8 * len)
  layout : Layout s.mem (State.addr base) len
  width : wOf s.mem (State.addr base) = w
  ptr : s.gpr .r0 = base
  inverse : ((word s.mem (State.addr base) (arrAt w 0)).toNat *
    (wordAt s.mem (State.addr base) Proof.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0
  operand : numAt s.mem (State.addr base) w 4 < numAt s.mem (State.addr base) w 0
  two : w32 s.mem (State.addr base) (arrAt w 7) = 2
  counter : s.mem.readW (off (State.addr base) 208) 32 = BitVec.ofNat 32 c
  stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4
  stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩
  saved : s.mem.readW (State.addr s.sp) 32 = base

theorem DoubleLoopReady.after_double {s t : State} {base : BitVec 32} {len w c : Nat}
    (h : DoubleLoopReady base len w c s)
    (bound : numAt t.mem (State.addr base) w 4 < numAt s.mem (State.addr base) w 0)
    (keeps : Keeps (State.addr base) len w 4 s.mem t.mem)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem)
    (rest : Rest roundClobbers s t) (ptr : t.gpr .r0 = base) :
    DoubleLoopReady base len w c t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  have kl := keeps_layout h.layout (by rw [h.width]; exact keeps)
  have oldM := keeps_array_num keeps fits (show Operand 0 by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
  have oldLow := keeps_array_word (d := 0) (bits := 64) keeps fits (show Operand 0 by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide) (by omega_using [])
  have oldTwo := keeps_array_word (d := 0) (bits := 32) keeps fits (show Operand 7 by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide) (by omega_using [])
  simp only [Nat.add_zero] at oldLow oldTwo
  refine ⟨h.workspace.congr rest.wr, kl.2, kl.1.trans h.width, ptr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · exact saved_base_kept frame h.stackSep h.saved rest.sp

end VG.Proof.Bignum.Arm

end

end

/-! # A loop-counter update preserves the RSA header, numbers, and saved base -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Layout)
open VG.Proof.X25519.Arm (Rest)

theorem counter_outside_layout {m m' : Mem} {base : Addr} {len : Nat}
    (outside : Outside base 208 4 m m') (layout : Layout m base len) :
    wOf m' base = wOf m base ∧ Layout m' base len := by
  have width : wOf m' base = wOf m base :=
    congrArg BitVec.toNat (outside.word (d := 48) (by decide) (by decide))
  refine ⟨width, ?_⟩
  unfold Layout
  rw [width]
  refine ⟨layout.1, layout.2.1, layout.2.2.1, ?_⟩
  intro j hj
  change word m' base (8 * (8 + j)) = _
  rw [outside.word (by omega_using [hj]) (by omega_using [hj])]
  exact layout.2.2.2 j hj

theorem DoubleLoopReady.after_count {s t : State} {base : BitVec 32} {len w c c' : Nat}
    (h : DoubleLoopReady base len w c s)
    (mem : t.mem = s.mem.writeW (off (State.addr base) 208) (BitVec.ofNat 32 c'))
    (rest : Rest [.r1] s t) :
    DoubleLoopReady base len w c' t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧
      numAt t.mem (State.addr base) w 4 = numAt s.mem (State.addr base) w 4 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 := by
  have nowrap := h.workspace.nowrap
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  have outside := writeW32_outside s.mem (State.addr base) (d := 208) (BitVec.ofNat 32 c') (by decide)
  rw [← mem] at outside
  have arrays (q : Nat) (hq : q < 8) :
      numAt t.mem (State.addr base) w q = numAt s.mem (State.addr base) w q := by
    have bound := Nat.le_trans (array_end_le hq) fits
    rw [numAt_native, numAt_native]
    apply outside.val32
    · right; simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []
    · omega_using [nowrap, bound]
  have kl := counter_outside_layout outside h.layout
  have frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [size]) (by decide))
  refine ⟨?_, frame, arrays 4 (by decide), arrays 0 (by decide)⟩
  refine ⟨h.workspace.congr rest.wr, kl.2, kl.1.trans h.width,
    (rest.gpr .r0 (by simp)).trans h.ptr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have fit0 := Nat.le_trans (array_end_le (w := w) (j := 0) (k := 8) (by decide)) fits
    rw [outside.word (d := arrAt w 0) (by right; simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []) (by omega_using [nowrap, fit0])]
    change (_ * (word t.mem (State.addr base) 56).toNat + 1) % 2 ^ 64 = 0
    rw [outside.word (d := 56) (by decide) (by decide)]
    exact h.inverse
  · rw [arrays 4 (by decide), arrays 0 (by decide)]; exact h.operand
  · have fit7 := Nat.le_trans (array_end_le (w := w) (j := 7) (k := 8) (by decide)) fits
    rw [outside.w32 (d := arrAt w 7) (by right; simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []) (by omega_using [nowrap, fit7])]
    exact h.two
  · rw [mem, Mem.readW_writeW_self32]
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
  · rw [rest.sp]; exact h.stackSep
  · exact saved_base_kept frame h.stackSep h.saved rest.sp

end VG.Proof.Bignum.Arm
