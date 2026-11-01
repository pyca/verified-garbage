module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowBuild
import VerifiedGarbage.Proof.Bignum.Arm.WindowState
import VerifiedGarbage.Proof.Bignum.Arm.WindowSelect
import VerifiedGarbage.Proof.Bignum.Arm.WindowCtl
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block

/-! # Selecting `T[digit]` and applying a window -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest)

/-- The scan has gone over the first `j` entries for the digit `d`. -/
structure ScanInv (base : BitVec 32) (len w M x A d j : Nat) (s : State) : Prop where
  power : ExpState base len w M x A s
  table : TableHolds s.mem base w M x 8
  fits : arrAt w 16 ≤ 8 * len
  digitLt : d < 8
  digit : s.mem.readW (off (State.addr base) 196) 32 = BitVec.ofNat 32 d
  selected : d < j → numAt s.mem (State.addr base) w 1 = numAt s.mem (State.addr base) w (8 + d)
  entry : s.mem.readW (off (State.addr base) 220) 32 = base + BitVec.ofNat 32 (arrAt w (8 + j))
  index : s.mem.readW (off (State.addr base) 228) 32 = BitVec.ofNat 32 j

theorem scanBody_ok (s : State) {base : BitVec 32} {len w M x A d j : Nat}
    (h : ScanInv base len w M x A d j s) (hj : j < 8) :
    WP isa scanBody s fun t => ScanInv base len w M x A d (j + 1) t ∧ t.z = decide (j + 1 = 8) ∧
      KeepsExp base s.mem t.mem ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  have fits := h.fits
  have nowrap := h.power.ready.workspace.nowrap
  rw [scanBody, WP.seq_iff]
  apply WP.block_append_iff.mpr
  refine WP.mono (scanBit_ok s h.power.ready h.digitLt hj h.digit h.index) ?_
  rintro u ⟨bit, memU, restU⟩
  have readyU := h.power.ready.of_mem memU restU ((restU.gpr .r0 (by simp)).trans h.power.ready.ptr)
  refine WP.mono (scanArgs_ok u readyU (by rw [memU]; exact h.entry)) ?_
  rintro v ⟨p0, p10, p12, count, memV, restV⟩
  have bitV : (v.gpr .r11).toNat ≤ 1 := by
    rw [restV.gpr .r11 (by simp), bit]; split <;> decide
  have select := selectAt_ok v readyU memV (rest_round restV) fits (o := 1) (a := 1) (b := 8 + j)
    (by decide) (by decide) (by decide) (by omega) p0 p10 p12 count bitV
  rw [WP.seq_iff] at select
  rw [WP.seq_iff]
  refine WP.mono select fun y hy => ?_
  rw [WP.seq_iff]
  refine WP.mono hy ?_
  rintro y ⟨readyY, value, outside, keeps, frameY, restY⟩
  rw [restV.gpr .r11 (by simp), bit, memU] at value
  rw [memU] at outside keeps frameY
  have powerY := h.power.after_other readyY keeps (by decide) (by decide) (by decide) (by decide) (by decide)
  have tableY := h.table.of_keeps keeps fits (by decide) (by decide)
  have sepHdr (e : Nat) (he : e + 4 ≤ 256) : e + 4 ≤ arrAt w 1 := by
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega
  have hdr (e : Nat) (he : e + 4 ≤ 256) := outside_read32 outside (d := e) (Or.inl (sepHdr e he)) (by omega)
  have entryY := (hdr 220 (by decide)).trans h.entry
  have indexY := (hdr 228 (by decide)).trans h.index
  have hd8 := h.digitLt
  have entryNum := outside_num outside fits nowrap (q := 8 + d) (by omega) (by omega)
  refine WP.mono (entryNext_ok y readyY hj entryY indexY) ?_
  rintro t ⟨memT, zT, restT⟩
  have ctl : CtlOnly base y.mem t.mem := by
    rw [memT]; exact ctl_write2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  have ptr : t.gpr .r0 = base := (restT.gpr .r0 (by simp)).trans readyY.ptr
  obtain ⟨powerT, frameT⟩ := powerY.after_ctl ctl restT ptr
  obtain ⟨e220, e228⟩ := header_after_writes y.mem base (base + BitVec.ofNat 32 (arrAt w (8 + (j + 1))))
    (BitVec.ofNat 32 (j + 1))
  have numT (q : Nat) (hq : q < 16) : numAt t.mem (State.addr base) w q = numAt y.mem (State.addr base) w q :=
    ctl_num (len := len) ctl (Nat.le_trans (arrAt_le (by omega)) fits) nowrap
  refine ⟨⟨powerT, tableY.after_ctl ctl fits nowrap (by decide), fits, h.digitLt, ?_, ?_,
    by rw [memT]; exact e220, by rw [memT]; exact e228⟩, zT, ?_, frameY.trans frameT,
    (rest_round restU).trans (restY.trans (rest_round restT))⟩
  · rw [memT, read_after_writes _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hdr 196 (by decide)]
    exact h.digit
  · intro hd
    rw [numT 1 (by decide), numT (8 + d) (by omega), value, entryNum]
    by_cases e : d = j
    · subst e; simp only [ite_true, show (1 : BitVec 32).toNat = 1 from rfl, Nat.one_ne_zero, ite_false]
    · simp only [e, ite_false, show (0 : BitVec 32).toNat = 0 from rfl, ite_true]
      exact h.selected (by omega)
  · refine (KeepsExp.of_outside outside (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega)).trans ?_
    rw [memT]
    exact KeepsExp.of_writes _ _ _ _ (Or.inl (by decide)) (by decide) (Or.inl (by decide)) (by decide)

theorem scanStage0_ok (s : State) {base : BitVec 32} {len w M x A d : Nat}
    (h : ExpState base len w M x A s) (table : TableHolds s.mem base w M x 8) (fits : arrAt w 16 ≤ 8 * len)
    (hd : d < 8) (digit : s.mem.readW (off (State.addr base) 196) 32 = BitVec.ofNat 32 d) :
    WP isa (.block scanInit) s fun t => ScanInv base len w M x A d 0 t ∧ KeepsExp base s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have nowrap := h.ready.workspace.nowrap
  refine WP.mono (tableInit_ok s h.ready) ?_
  rintro u ⟨memU, restU⟩
  have ctl : CtlOnly base s.mem u.mem := by
    rw [memU]; exact ctl_write2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  obtain ⟨powerU, frameU⟩ := h.after_ctl ctl restU ((restU.gpr .r0 (by simp)).trans h.ready.ptr)
  obtain ⟨e220, e228⟩ := header_after_writes s.mem base (base + BitVec.ofNat 32 (arrAt w (8 + 0)))
    (BitVec.ofNat 32 0)
  rw [← memU] at e220 e228
  have keepsU : KeepsExp base s.mem u.mem := by
    rw [memU]; exact KeepsExp.of_writes _ _ _ _ (Or.inl (by decide)) (by decide) (Or.inl (by decide)) (by decide)
  exact ⟨⟨powerU, table.after_ctl ctl fits nowrap (by decide), fits, hd,
      by rw [memU, read_after_writes _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact digit,
      fun h => absurd h (Nat.not_lt_zero _), e220, e228⟩, keepsU, frameU, rest_round restU⟩

theorem scanLoop_ok (s : State) {base : BitVec 32} {len w M x A d : Nat}
    (h : ScanInv base len w M x A d 0 s) :
    WP isa (.loop scanBody .ne) s fun t => ScanInv base len w M x A d 8 t ∧
      KeepsExp base s.mem t.mem ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let inv := fun k t => ∃ j, j + k = 8 ∧ 0 < k ∧ ScanInv base len w M x A d j t ∧
    KeepsExp base s.mem t.mem ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t
  refine WP.loop (M := isa) inv ?_ 8 s ?_
  · intro k t hk
    obtain ⟨j, hjk, hk, hi, keeps, frame, rest⟩ := hk
    refine WP.mono (scanBody_ok t hi (by omega)) ?_
    rintro v ⟨hv, hz, keepsV, frameV, restV⟩
    by_cases he : j + 1 = 8
    · left
      refine ⟨?_, he ▸ hv, keeps.trans keepsV, frame.trans frameV, rest.trans restV⟩
      change some (!v.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, j + 1, by omega, by omega, hv, keeps.trans keepsV, frame.trans frameV,
        rest.trans restV⟩
      change some (!v.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · exact ⟨0, rfl, by decide, h, KeepsExp.refl _ _, Frame.refl _ _, Rest.refl _ _⟩

/-- Array 1 `:= T[d]`. -/
theorem scan_ok (s : State) {base : BitVec 32} {len w M x A d : Nat}
    (h : ExpState base len w M x A s) (table : TableHolds s.mem base w M x 8) (fits : arrAt w 16 ≤ 8 * len)
    (hd : d < 8) (digit : s.mem.readW (off (State.addr base) 196) 32 = BitVec.ofNat 32 d) :
    WP isa scan s fun t => ExpState base len w M x A t ∧ TableHolds t.mem base w M x 8 ∧
      numAt t.mem (State.addr base) w 1 = numAt t.mem (State.addr base) w (8 + d) ∧
      t.mem.readW (off (State.addr base) 196) 32 = BitVec.ofNat 32 d ∧
      KeepsExp base s.mem t.mem ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [scan, WP.seq_iff]
  refine WP.mono (scanStage0_ok s h table fits hd digit) ?_
  rintro u ⟨inv0, keepsU, frameU, restU⟩
  refine WP.mono (scanLoop_ok u inv0) ?_
  rintro t ⟨invT, keepsT, frameT, restT⟩
  exact ⟨invT.power, invT.table, invT.selected hd, invT.digit, keepsU.trans keepsT, frameU.trans frameT,
    restU.trans restT⟩

/-- The power times `T[d]`: `x^(A + d) R`, and no pending bits. -/
theorem windowApply_ok (s : State) {base : BitVec 32} {len w M x A d : Nat}
    (h : ExpState base len w M x A s) (table : TableHolds s.mem base w M x 8) (fits : arrAt w 16 ≤ 8 * len)
    (hd : d < 8) (digit : s.mem.readW (off (State.addr base) 196) 32 = BitVec.ofNat 32 d) :
    WP isa windowApply s fun t => ExpState base len w M x (A + d) t ∧ TableHolds t.mem base w M x 8 ∧
      t.mem.readW (off (State.addr base) 196) 32 = BitVec.ofNat 32 0 ∧
      t.mem.readW (off (State.addr base) 204) 32 = BitVec.ofNat 32 0 ∧
      KeepsExp base s.mem t.mem ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have nowrap := h.ready.workspace.nowrap
  have size : 256 ≤ 8 * len := Nat.le_trans (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega) fits
  rw [windowApply, WP.seq_iff]
  refine WP.mono (scan_ok s h table fits hd digit) ?_
  rintro u ⟨powerU, tableU, selected, _, keepsU, frameU, restU⟩
  have entry := tableU d hd
  rw [← selected] at entry
  rw [WP.seq_iff]
  refine WP.mono (montOp_ok u powerU.ready (o := 6) (a := 6) (b := 1)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
    (by rw [powerU.modulus]; exact entry.1)) ?_
  rintro v ⟨ready, modulus, bound, value, keeps, frameV, restV⟩
  rw [powerU.modulus] at modulus bound value
  have powerV := powerU.after_y ready modulus keeps bound
    (mont_mulpow powerU.coprime powerU.powerValue entry.2 value)
  have tableV := tableU.of_keeps keeps fits (by decide) (by decide)
  refine WP.mono (windowReset_ok v ready) ?_
  rintro t ⟨memT, restT⟩
  have ctl : CtlOnly base v.mem t.mem := by
    rw [memT]; exact ctl_write2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  obtain ⟨powerT, frameT⟩ := powerV.after_ctl ctl restT ((restT.gpr .r0 (by simp)).trans ready.ptr)
  have outside := writeW32_outside (v.mem.writeW (off (State.addr base) 196) (BitVec.ofNat 32 0))
    (State.addr base) (d := 204) (BitVec.ofNat 32 0) (by decide)
  refine ⟨powerT, tableV.after_ctl ctl fits nowrap (by decide), ?_, by rw [memT]; exact Mem.readW_writeW_self32 _ _ _,
    keepsU.trans ((KeepsExp.of_keeps keeps size).trans ?_), frameU.trans (frameV.trans frameT),
    restU.trans (restV.trans (rest_round restT))⟩
  · rw [memT, outside_read32 outside (d := 196) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [memT]
    exact KeepsExp.of_writes _ _ _ _ (Or.inr rfl) (by decide) (Or.inl (by decide)) (by decide)

end VG.Proof.Bignum.Arm
