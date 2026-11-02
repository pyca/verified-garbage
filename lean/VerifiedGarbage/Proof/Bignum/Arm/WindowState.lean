module
public import VerifiedGarbage.Proof.Bignum.Arm.ExpState
public import VerifiedGarbage.Proof.Bignum.Arm.WindowTable

import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge

/-! # Writes to the control words of the header

The windowed exponentiation's controls are header words between bytes 128
and 255. Writing them changes nothing the arithmetic reads: the layout's
words (below byte 128) and every array. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt wordAt wOf Layout)
open VG.Proof.X25519.Arm (Rest)

/-- Only header bytes 128 to 255 differ. -/
abbrev CtlOnly (base : BitVec 32) (m m' : Mem) : Prop := Outside (State.addr base) 128 128 m m'

theorem ctl_write (m : Mem) (base : BitVec 32) {d : Nat} (v : BitVec 32) (hd : 128 ≤ d) (hd' : d + 4 ≤ 256) :
    CtlOnly base m (m.writeW (off (State.addr base) d) v) :=
  (writeW32_outside m _ v (by omega)).mono hd (by omega)

theorem ctl_write2 (m : Mem) (base : BitVec 32) {d e : Nat} (v u : BitVec 32)
    (hd : 128 ≤ d) (hd' : d + 4 ≤ 256) (he : 128 ≤ e) (he' : e + 4 ≤ 256) :
    CtlOnly base m ((m.writeW (off (State.addr base) d) v).writeW (off (State.addr base) e) u) :=
  (ctl_write m base v hd hd').trans (ctl_write _ base u he he')

theorem arrAt_le {w a b : Nat} (h : a ≤ b) : arrAt w a ≤ arrAt w b := by
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

/-- The number of any array of the first sixteen is unchanged. -/
theorem ctl_num {m m' : Mem} {base : BitVec 32} {len w q : Nat} (ctl : CtlOnly base m m')
    (fit : arrAt w (q + 1) ≤ 8 * len) (nowrap : base.toNat + 8 * len ≤ 2 ^ 32) :
    numAt m' (State.addr base) w q = numAt m (State.addr base) w q := by
  have := array_end_le (w := w) (show q < q + 1 by omega)
  rw [numAt_native, numAt_native]
  apply ctl.val32
  · right; simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega
  · omega

theorem ctl_readW {m m' : Mem} {base : BitVec 32} {d : Nat} (ctl : CtlOnly base m m') (hd : d + 4 ≤ 128) :
    m'.readW (off (State.addr base) d) 32 = m.readW (off (State.addr base) d) 32 :=
  outside_read32 ctl (Or.inl hd) (by omega)

theorem ArithmeticReady.after_ctl {s t : State} {base : BitVec 32} {len w : Nat} {rs : List Reg}
    (h : ArithmeticReady base len w s) (ctl : CtlOnly base s.mem t.mem) (rest : Rest rs s t)
    (ptr : t.gpr .r0 = base) :
    ArithmeticReady base len w t ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem := by
  have nowrap := h.workspace.nowrap
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have width : wOf t.mem (State.addr base) = wOf s.mem (State.addr base) :=
    congrArg BitVec.toNat (ctl.word (d := 48) (by omega) (by decide))
  have layout : Layout t.mem (State.addr base) len := by
    unfold Layout
    rw [width]
    refine ⟨h.layout.1, h.layout.2.1, h.layout.2.2.1, ?_⟩
    intro j hj
    change word t.mem (State.addr base) (8 * (8 + j)) = _
    rw [ctl.word (by omega) (by omega)]
    exact h.layout.2.2.2 j hj
  have frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem := outside_workspace ctl (by omega)
  have modulus : numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 :=
    ctl_num ctl (Nat.le_trans (arrAt_le (by decide)) fits) nowrap
  refine ⟨⟨h.workspace.congr rest.wr, layout, width.trans h.width, ptr, ?_, ?_, ?_, ?_, ?_⟩, frame⟩
  · have fit0 := Nat.le_trans (array_end_le (w := w) (j := 0) (k := 8) (by decide)) fits
    rw [ctl.word (d := arrAt w 0) (by right; simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega) (by omega)]
    change (_ * (word t.mem (State.addr base) 56).toNat + 1) % 2 ^ 64 = 0
    rw [ctl.word (d := 56) (by omega) (by decide)]
    exact h.inverse
  · rw [modulus]; exact h.modulus
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
  · rw [rest.sp]; exact h.stackSep
  · exact saved_base_kept frame h.stackSep h.saved rest.sp

theorem ExpState.after_ctl {s t : State} {base : BitVec 32} {len w M x E : Nat} {rs : List Reg}
    (h : ExpState base len w M x E s) (ctl : CtlOnly base s.mem t.mem) (rest : Rest rs s t)
    (ptr : t.gpr .r0 = base) : ExpState base len w M x E t ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem := by
  obtain ⟨ready, frame⟩ := h.ready.after_ctl ctl rest ptr
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have nowrap := h.ready.workspace.nowrap
  have num (q : Nat) (hq : q < 8) := ctl_num (len := len) (w := w) (q := q) ctl
    (Nat.le_trans (arrAt_le (by omega)) fits) nowrap
  refine ⟨⟨ready, ?_, h.coprime, ?_, ?_, ?_, ?_, ?_, ?_⟩, frame⟩
  · rw [num 0 (by decide)]; exact h.modulus
  · rw [num 5 (by decide)]; exact h.inputBound
  · rw [num 5 (by decide)]; exact h.inputValue
  · rw [num 6 (by decide)]; exact h.powerBound
  · rw [num 6 (by decide)]; exact h.powerValue
  · rw [num 7 (by decide)]; exact h.one
  · rw [num 4 (by decide)]; exact h.r2

theorem TableHolds.after_ctl {m m' : Mem} {base : BitVec 32} {len w M x k : Nat}
    (h : TableHolds m base w M x k) (ctl : CtlOnly base m m') (fits : arrAt w 16 ≤ 8 * len)
    (nowrap : base.toNat + 8 * len ≤ 2 ^ 32) (hk : k ≤ 8) : TableHolds m' base w M x k := by
  intro j hj
  rw [ctl_num (len := len) ctl (Nat.le_trans (arrAt_le (by omega)) fits) nowrap]
  exact h j hj

/-- An operation that writes array `o` (not one the exponentiation keeps)
keeps the exponentiation's state. -/
theorem ExpState.after_other {s t : State} {base : BitVec 32} {len w M x E o : Nat}
    (h : ExpState base len w M x E s) (ready : ArithmeticReady base len w t)
    (keeps : VG.Proof.Rsa.Mont.Keeps (State.addr base) len w o s.mem t.mem)
    (h0 : o ≠ 0) (h4 : o ≠ 4) (h5 : o ≠ 5) (h6 : o ≠ 6) (h7 : o ≠ 7) : ExpState base len w M x E t := by
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have op (q : Nat) (hq : q < 8) (h2 : q ≠ 2) (h3 : q ≠ 3) : VG.Proof.Rsa.Mont.Operand q :=
    ⟨hq, h2, h3⟩
  have num (q : Nat) (hq : q < 8) (h2 : q ≠ 2) (h3 : q ≠ 3) (ne : q ≠ o) :=
    keeps_array_num keeps fits (op q hq h2 h3) ne
  refine ⟨ready, ?_, h.coprime, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [num 0 (by decide) (by decide) (by decide) (Ne.symm h0)]; exact h.modulus
  · rw [num 5 (by decide) (by decide) (by decide) (Ne.symm h5)]; exact h.inputBound
  · rw [num 5 (by decide) (by decide) (by decide) (Ne.symm h5)]; exact h.inputValue
  · rw [num 6 (by decide) (by decide) (by decide) (Ne.symm h6)]; exact h.powerBound
  · rw [num 6 (by decide) (by decide) (by decide) (Ne.symm h6)]; exact h.powerValue
  · rw [num 7 (by decide) (by decide) (by decide) (Ne.symm h7)]; exact h.one
  · rw [num 4 (by decide) (by decide) (by decide) (Ne.symm h4)]; exact h.r2

end VG.Proof.Bignum.Arm
