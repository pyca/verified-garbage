module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowScan
public import VerifiedGarbage.Proof.Bignum.Arm.ExpControl

/-! # One exponent bit of the windowed exponentiation

The power holds `x^A R` and the pending digit is `p`, of `q` bits: the bits
read so far are `A + p`. A bit squares the power and joins the digit, so the
bits become `2 (A + p) + bit`; after the third pending bit, the power is
multiplied by `T[digit]` and the digit starts again. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt numAt Keeps)
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

theorem windowBit_ok (s : State) {base : BitVec 32} {len w M x A p q V : Nat}
    (h : WinState base len w M x A p q s) (hv : V < 2 ^ 32)
    (byte : s.mem.readW (off (State.addr base) 200) 32 = BitVec.ofNat 32 V) :
    WP isa windowBit s fun t => (∃ A' p' q', WinState base len w M x A' p' q' t ∧
      A' + p' = 2 * (A + p) + V / 128 % 2) ∧
      KeepsExp base s.mem t.mem ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits := h.fits
  have nowrap := h.power.ready.workspace.nowrap
  have size : 256 ≤ 8 * len := Nat.le_trans (by simp only [arrAt, Spec.Rsa.Mont.hdrBytes]; omega) fits
  have hq := h.short
  have hp := h.bound
  rw [windowBit, WP.seq_iff]
  refine WP.mono (exp_square_ok s h.power) ?_
  rintro u ⟨powerU, keepsU, frameU, restU⟩
  have hdrU (d : Nat) (hd : d + 4 ≤ 256) :=
    keeps_header_readW keepsU size (d := d) (bits := 32) (by omega)
  rw [WP.seq_iff]
  refine WP.mono (windowBitValue_ok u powerU.ready hv hq ((hdrU 200 (by decide)).trans byte)
    ((hdrU 196 (by decide)).trans h.digit) ((hdrU 204 (by decide)).trans h.pending)) ?_
  rintro v ⟨memV, zV, restV⟩
  have ctl : CtlOnly base u.mem v.mem := by
    rw [memV]; exact ctl_write2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  obtain ⟨powerV, frameV⟩ := powerU.after_ctl ctl restV ((restV.gpr .r0 (by simp)).trans powerU.ready.ptr)
  have tableV := (h.table.of_keeps keepsU fits (by decide) (by decide)).after_ctl ctl fits nowrap (by decide)
  obtain ⟨digitV, pendingV⟩ := two_writes u.mem base (d := 196) (e := 204)
    (BitVec.ofNat 32 (2 * p + V / 128 % 2)) (BitVec.ofNat 32 (q + 1)) (by decide) (by decide) (by decide)
  rw [← memV] at digitV pendingV
  have keepsV : KeepsExp base s.mem v.mem := (KeepsExp.of_keeps keepsU size).trans (by
    rw [memV]; exact KeepsExp.of_writes _ _ _ _ (Or.inr rfl) (by decide) (Or.inl (by decide)) (by decide))
  have restSV : Rest roundClobbers s v := restU.trans (rest_round restV)
  have bit : V / 128 % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases full : q + 1 = 3
  · refine WP.ite true (by simp [eval, zV, full]) (fun _ => ?_) (by simp)
    have small : 2 * p + V / 128 % 2 < 8 := by
      have : q = 2 := by omega
      subst this
      omega
    refine WP.mono (windowApply_ok v powerV tableV fits small digitV) ?_
    rintro t ⟨powerT, tableT, digitT, pendingT, keepsT, frameT, restT⟩
    refine ⟨⟨_, 0, 0, ⟨powerT, tableT, fits, digitT, pendingT, by decide, by decide⟩, ?_⟩,
      keepsV.trans keepsT, frameU.trans (frameV.trans frameT), restSV.trans restT⟩
    omega
  · refine WP.ite false (by simp [eval, zV, full]) (by simp) (fun _ => WP.block_nil ?_)
    refine ⟨⟨_, _, q + 1, ⟨powerV, tableV, fits, digitV, pendingV, ?_, by omega⟩, ?_⟩,
      keepsV, frameU.trans frameV, restSV⟩
    · rw [Nat.pow_succ]; omega
    · omega

end VG.Proof.Bignum.Arm
