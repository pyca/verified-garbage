module
public import VerifiedGarbage.Proof.Bignum.Arm.WindowBuild

import VerifiedGarbage.Proof.Bignum.Arm.WindowScan
import VerifiedGarbage.Proof.Bignum.Arm.WindowState
import VerifiedGarbage.Proof.Bignum.Arm.WindowCtl
import VerifiedGarbage.Proof.Bignum.Arm.ExpStep
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block

/-! # One exponent bit of the windowed exponentiation

The power holds `x^A R` and the pending digit is `p`, of `q` bits: the bits
read so far are `A + p`. A bit squares the power and joins the digit, so the
bits become `2 (A + p) + bit`; after the third pending bit, the power is
multiplied by `T[digit]` and the digit starts again. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps)
open VG.Proof.X25519.Arm (Rest)

structure WinState (base : BitVec 32) (len w M x A p q : Nat) (s : State) : Prop where
  power : ExpState base len w M x A s
  table : TableHolds s.mem base w M x 8
  fits : arrAt w 16 ≤ 8 * len
  digit : s.mem.readW (off (State.addr base) 196) 32 = BitVec.ofNat 32 p
  pending : s.mem.readW (off (State.addr base) 204) 32 = BitVec.ofNat 32 q
  bound : p < 2 ^ q
  short : q < 3

theorem two_writes (m : Mem) (base : BitVec 32) {d e : Nat} (v u : BitVec 32)
    (sep : d + 4 ≤ e ∨ e + 4 ≤ d) (fd : d + 4 ≤ 256) (fe : e + 4 ≤ 256) :
    ((m.writeW (off (State.addr base) d) v).writeW (off (State.addr base) e) u).readW
        (off (State.addr base) d) 32 = v ∧
      ((m.writeW (off (State.addr base) d) v).writeW (off (State.addr base) e) u).readW
        (off (State.addr base) e) 32 = u := by
  have outside := writeW32_outside (m.writeW (off (State.addr base) d) v) (State.addr base) (d := e) u
    (by omega)
  exact ⟨by rw [outside_read32 outside (d := d) (by omega) (by omega), Mem.readW_writeW_self32],
    Mem.readW_writeW_self32 _ _ _⟩

theorem windowSquare_ok (s : State) {base : BitVec 32} {len w M x A p q V : Nat}
    (h : WinState base len w M x A p q s)
    (byte : s.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 V) :
    WP isa (squareOp 6 6) s fun u => WinState base len w M x (2 * A) p q u ∧
      u.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 V ∧
      KeepsExp base s.mem u.mem ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem u.mem ∧ Rest roundClobbers s u := by
  have fits := h.fits
  have size : 256 ≤ 8 * len := Nat.le_trans (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega) fits
  refine WP.mono (exp_square_ok s h.power) ?_
  rintro u ⟨powerU, keepsU, frameU, restU⟩
  have hdrU (d : Nat) (hd : d + 4 ≤ 256) :=
    keeps_header_readW keepsU size (d := d) (bits := 32) (by omega)
  exact ⟨⟨powerU, h.table.of_keeps keepsU fits (by decide) (by decide), fits,
    (hdrU 196 (by decide)).trans h.digit, (hdrU 204 (by decide)).trans h.pending, h.bound, h.short⟩,
    (hdrU 200 (by decide)).trans byte, KeepsExp.of_keeps keepsU size, frameU, restU⟩

/-- The bit joins the digit: `2 p + bit`, below 8, and the count of pending bits;
Z when it is three. -/
theorem windowJoin_ok (s : State) {base : BitVec 32} {len w M x A p q V : Nat}
    (h : WinState base len w M x A p q s) (hv : V < 2 ^ 32)
    (byte : s.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 V) :
    WP isa (.block windowBitValue) s fun v => ExpState base len w M x A v ∧
      TableHolds v.mem base w M x 8 ∧ 2 * p + V / 128 % 2 < 2 ^ (q + 1) ∧
      v.mem.readW (off (State.addr base) 196) 32 = BitVec.ofNat 32 (2 * p + V / 128 % 2) ∧
      v.mem.readW (off (State.addr base) 204) 32 = BitVec.ofNat 32 (q + 1) ∧
      v.z = decide (q + 1 = 3) ∧
      KeepsExp base s.mem v.mem ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem v.mem ∧ Rest roundClobbers s v := by
  have fits := h.fits
  have nowrap := h.power.ready.workspace.nowrap
  have hp := h.bound
  refine WP.mono (windowBitValue_ok s h.power.ready hv h.short byte h.digit h.pending) ?_
  rintro v ⟨memV, zV, restV⟩
  have ctl : CtlOnly base s.mem v.mem := by
    rw [memV]; exact ctl_write2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  obtain ⟨powerV, frameV⟩ := h.power.after_ctl ctl restV ((restV.gpr .r0 (by simp)).trans h.power.ready.ptr)
  obtain ⟨digitV, pendingV⟩ := two_writes s.mem base (d := 196) (e := 204)
    (BitVec.ofNat 32 (2 * p + V / 128 % 2)) (BitVec.ofNat 32 (q + 1)) (by decide) (by decide) (by decide)
  rw [← memV] at digitV pendingV
  have bit : V / 128 % 2 < 2 := Nat.mod_lt _ (by decide)
  refine ⟨powerV, h.table.after_ctl ctl fits nowrap (by decide), by rw [Nat.pow_succ]; omega, digitV, pendingV, zV,
    by rw [memV]; exact KeepsExp.of_writes _ _ _ _ (Or.inr rfl) (by decide) (Or.inl (by decide)) (by decide),
    frameV, rest_round restV⟩

theorem windowBit_ok (s : State) {base : BitVec 32} {len w M x A p q V : Nat}
    (h : WinState base len w M x A p q s) (hv : V < 2 ^ 32)
    (byte : s.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 V) :
    WP isa windowBit s fun t => (∃ A' p', WinState base len w M x A' p' ((q + 1) % 3) t ∧
      A' + p' = 2 * (A + p) + V / 128 % 2) ∧
      KeepsExp base s.mem t.mem ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits := h.fits
  have hq := h.short
  rw [windowBit, WP.seq_iff]
  refine WP.mono (windowSquare_ok s h byte) ?_
  rintro u ⟨stateU, byteU, keepsU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (windowJoin_ok u stateU hv byteU) ?_
  rintro v ⟨powerV, tableV, boundV, digitV, pendingV, zV, keepsV, frameV, restV⟩
  have bit : V / 128 % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases full : q + 1 = 3
  · refine WP.ite true (by simp [eval, zV, full]) (fun _ => ?_) (by simp)
    have small : 2 * p + V / 128 % 2 < 8 := by
      rw [full] at boundV
      exact boundV
    refine WP.mono (windowApply_ok v powerV tableV fits small digitV) ?_
    rintro t ⟨powerT, tableT, digitT, pendingT, keepsT, frameT, restT⟩
    refine ⟨⟨_, 0, ⟨powerT, tableT, fits, digitT, by rw [full]; exact pendingT, by rw [full]; decide,
      by rw [full]; decide⟩, ?_⟩, keepsU.trans (keepsV.trans keepsT), frameU.trans (frameV.trans frameT),
      restU.trans (restV.trans restT)⟩
    omega
  · refine WP.ite false (by simp [eval, zV, full]) (by simp) (fun _ => WP.block_nil ?_)
    have mod : (q + 1) % 3 = q + 1 := Nat.mod_eq_of_lt (by omega)
    refine ⟨⟨_, _, ⟨powerV, tableV, fits, digitV, by rw [mod]; exact pendingV, by rw [mod]; exact boundV,
      by omega⟩, ?_⟩, keepsU.trans keepsV, frameU.trans frameV, restU.trans restV⟩
    omega

end VG.Proof.Bignum.Arm
